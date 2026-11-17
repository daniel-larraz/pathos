//! From pathos's front end to the compiled checker.
//!
//! The front end (`pathos-elab`) reads the proof against CPC as it reads
//! any proof: it resolves names, desugars applications by the operators'
//! attributes, computes nil terminators and types every term. The
//! [`Adapter`] is a plugin of that front end. It is told of each
//! assumption and each step, and instead of letting the interpreter check
//! the step it writes down, in the compiled checker's [`Store`], what
//! logos's parser hands logos's checker: the list of assumptions and the
//! list of commands. [`Built::check`] then runs the compiled checker once.
//!
//! Only the interface the generator documents is used (the stage's
//! `README.md`, "Using the artifact in Pathos"): `Store::literal`,
//! `boolean`, `numeral`, `apply`, `raw`, `named`/`construct`,
//! `Constructor::from_name`, `check_proof`, and `Limits`.

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use pathos_compiled_checker as cc;
use pathos_compiled_checker::{Constructor, Limits, Store, Verdict};
use pathos_elab::{Plugin, State, StepResult};
use pathos_syntax::{Error, Result};
use pathos_term::{Kind, Lit, NodeKind, SymbolKind, Term};

/// A term of the compiled checker's store.
type CTerm = cc::Term;

/// The input cannot be given to the compiled checker.
fn unsupported(what: impl std::fmt::Display) -> Error {
    Error::plain(format!("pathos does not read this proof: {what}"))
}

/// The compiled checker refused a term the adapter built. Bad shapes and
/// exhausted limits are errors there, never an acceptance.
fn refused(e: cc::CheckError) -> Error {
    Error::plain(format!("the compiled checker refused its input: {e}"))
}

/// What a term is made of, for the conversion.
enum Shape {
    /// Built from the term alone.
    Leaf,
    /// A curried application of the first term to the others.
    Apply(Vec<Term>),
    /// A function type: arguments, then the result.
    Fun(Vec<Term>),
    /// An indexed operator with its indices, applied to the rest.
    Indexed(Constructor, Vec<Term>, Vec<Term>),
    /// `(eo::var name type)`.
    Var(Term, Term),
    /// A constant the proof declares, with its type.
    UConst(Term),
    /// Already a term of the store.
    Done(CTerm),
    /// A term of the store applied to arguments.
    Headed(CTerm, Vec<Term>),
    /// An indexed operator whose index is a term of the store, applied to
    /// the rest.
    IndexedDone(Constructor, CTerm, Vec<Term>),
}

/// A datatype of a parametric block, as declared.
struct Template {
    /// The block it was declared in, by number.
    block: usize,
    name: String,
    /// Its parameters, if a field mentions them.
    params: Vec<Term>,
    /// Its constructors, each with its selectors.
    constructors: Vec<(Term, Vec<Term>)>,
}

/// What a symbol of a parametric block is.
#[derive(Copy, Clone)]
enum Role {
    Constructor(usize),
    Selector(usize, usize),
}

/// A parametric datatype at given type arguments.
type InstanceKey = (Term, Vec<Term>);

/// The terms of an instance: its sort, its constructors and their
/// selectors.
struct Instance {
    sort: CTerm,
    constructors: Vec<CTerm>,
    selectors: Vec<Vec<CTerm>>,
}

/// What the adapter has written down so far.
pub struct Built {
    store: Store,
    /// Symbols of the signature have identifiers below this.
    boundary: u32,
    /// The store's term for each front-end term converted so far.
    memo: HashMap<Term, CTerm>,
    /// The sorts, constructors and selectors of the proof's datatypes.
    datatypes: HashMap<Term, CTerm>,
    /// The parametric datatypes, by their symbols, and what their
    /// constructors and selectors are.
    templates: HashMap<Term, Template>,
    roles: HashMap<Term, Role>,
    next_block: usize,
    /// The instances built so far, numbered as logos numbers them.
    instances: HashMap<InstanceKey, Instance>,
    next_instance: usize,
    /// The instances whose declaration is being built: inside it they are
    /// references by name.
    building: HashMap<InstanceKey, CTerm>,
    /// The sorts and constants the proof declares, by their front-end
    /// terms. They are numbered as they are first used, and a term must
    /// keep its number whichever conversion meets it.
    declared: HashMap<Term, CTerm>,
    /// Symbols the adapter cannot represent, and why.
    refused_symbols: HashMap<Term, &'static str>,
    next_const: u32,
    next_sort: u32,
    /// The assumptions, in the order of the file.
    assumptions: Vec<CTerm>,
    commands: Vec<CTerm>,
    /// What each command is in the proof, for `--explain`.
    labels: Vec<String>,
    /// The formulas the checker's state will hold, oldest first, and where
    /// each formula stands in it.
    stack: Vec<Term>,
    positions: HashMap<Term, Vec<usize>>,
    /// The heights at which `assume-push` commands stand.
    push_heights: Vec<usize>,
    /// A step without a stated conclusion was left to the interpreter; the
    /// name it binds next tells what it proved. True for `step-pop`.
    pending_step: Option<bool>,
}

impl Built {
    fn new(boundary: u32, caching: bool) -> Built {
        let limits = Limits {
            terms: u32::MAX,
            calls: u64::MAX,
            depth: 100_000,
        };
        let mut store = Store::new(limits);
        store.set_caching(caching);
        Built {
            store,
            boundary,
            memo: HashMap::new(),
            datatypes: HashMap::new(),
            declared: HashMap::new(),
            templates: HashMap::new(),
            roles: HashMap::new(),
            next_block: 0,
            instances: HashMap::new(),
            next_instance: 0,
            building: HashMap::new(),
            refused_symbols: HashMap::new(),
            next_const: 0,
            next_sort: 0,
            assumptions: Vec::new(),
            commands: Vec::new(),
            labels: Vec::new(),
            stack: Vec::new(),
            positions: HashMap::new(),
            push_heights: Vec::new(),
            pending_step: None,
        }
    }

    fn named(&mut self, name: &str, args: &[CTerm]) -> Result<CTerm> {
        self.store.named(name, args).map_err(refused)
    }

    fn raw_nat(&mut self, n: usize) -> Result<CTerm> {
        self.store
            .raw(cc::Lit::Numeral(cc::Integer::from(n)))
            .map_err(refused)
    }

    /// A datatype's name as logos keeps it: a leading dot is doubled, so
    /// that no name of the proof is the name of an instance.
    fn raw_name(&mut self, name: &str) -> Result<CTerm> {
        if name.starts_with('.') {
            self.raw_string(&format!(".{name}"))
        } else {
            self.raw_string(name)
        }
    }

    fn raw_string(&mut self, name: &str) -> Result<CTerm> {
        let points = name.chars().map(u32::from).collect();
        self.store
            .raw(cc::Lit::String(cc::EoString::from_code_points(points)))
            .map_err(refused)
    }

    /// The sort that stands for `t`, a sort the proof declares or an
    /// application of a sort constructor it declares.
    fn sort_of(&mut self, t: Term) -> Result<CTerm> {
        if let Some(&s) = self.declared.get(&t) {
            return Ok(s);
        }
        self.next_sort += 1;
        let id = self.raw_nat(self.next_sort as usize)?;
        let s = self.named("$emb_USort", &[id])?;
        self.declared.insert(t, s);
        Ok(s)
    }

    /// The generated constructor of a symbol of the signature.
    fn constructor(st: &State, sym: Term) -> Result<Constructor> {
        let name = st.ck.store.symbol_name(sym).unwrap_or_default();
        let cname = match name {
            "eo::List" => "$eo_List".to_string(),
            "eo::List::nil" => "$eo_List_nil".to_string(),
            "eo::List::cons" => "$eo_List_cons".to_string(),
            _ => match st.ck.overloads_of(name).iter().position(|&o| o == sym) {
                // the n-th symbol of a name, as the compiler names it
                Some(i) if i > 0 => format!("$eoo_{name}.{}", i + 1),
                _ => name.to_string(),
            },
        };
        Constructor::from_name(&cname)
            .filter(|c| c.is_user() || cname.starts_with("$eo_List"))
            .ok_or_else(|| unsupported(format!("the checker for CPC has no symbol {name}")))
    }

    /// The symbol at the head of a curried application.
    fn head(st: &State, mut t: Term) -> Term {
        while st.ck.store.kind(t) == Kind::APPLY {
            t = st.ck.store.child(t, 0);
        }
        t
    }

    fn is_signature_symbol(&self, st: &State, t: Term) -> bool {
        matches!(st.ck.store.kind(t), Kind::Symbol(SymbolKind::Const)) && t.id() < self.boundary
    }

    /// Whether `t` is a sort constructor the proof declares: a constant
    /// whose type is a function to `Type`.
    fn is_sort_constructor(&self, st: &State, t: Term) -> bool {
        matches!(st.ck.store.kind(t), Kind::Symbol(SymbolKind::Const))
            && t.id() >= self.boundary
            && !self.datatypes.contains_key(&t)
            && st.ck.store.ty(t).is_some_and(|ty| {
                st.ck.store.kind(ty) == Kind::Node(NodeKind::FunctionType)
                    && st
                        .ck
                        .store
                        .children(ty)
                        .last()
                        .is_some_and(|&r| st.ck.store.kind(r) == Kind::Type)
            })
    }

    fn shape(&self, st: &State, t: Term) -> Result<Shape> {
        let store = &st.ck.store;
        let children = store.children(t);
        Ok(match store.kind(t) {
            Kind::Node(NodeKind::Apply | NodeKind::ApplyOpaque) => {
                let f = children[0];
                if store.kind(t) == Kind::APPLY && self.is_sort_constructor(st, Self::head(st, t)) {
                    // an application of a sort constructor is a sort of its own
                    return Ok(Shape::Leaf);
                }
                if self.is_signature_symbol(st, f) {
                    let c = Self::constructor(st, f)?;
                    let n = c.arity();
                    if n > 0 {
                        if children.len() - 1 < n {
                            return Err(unsupported(format!(
                                "{} takes {n} indices, in {}",
                                st.ck.show(f),
                                st.ck.show(t)
                            )));
                        }
                        return Ok(Shape::Indexed(
                            c,
                            children[1..=n].to_vec(),
                            children[n + 1..].to_vec(),
                        ));
                    }
                }
                if store.kind(t) != Kind::APPLY {
                    return Err(unsupported(format!(
                        "an application with opaque arguments that the checker for CPC has no \
                         operator for: {}",
                        st.ck.show(t)
                    )));
                }
                Shape::Apply(children.to_vec())
            }
            Kind::Node(NodeKind::AsReturn) => {
                let f = children[0];
                if self.is_signature_symbol(st, f) {
                    let c = Self::constructor(st, f)?;
                    if c.arity() == 1 {
                        return Ok(Shape::Indexed(c, vec![children[1]], Vec::new()));
                    }
                }
                return Err(unsupported(format!(
                    "a type annotation the checker for CPC has no operator for: {}",
                    st.ck.show(t)
                )));
            }
            Kind::Node(NodeKind::FunctionType) => Shape::Fun(children.to_vec()),
            Kind::Node(NodeKind::Variable) if children.len() == 2 => {
                Shape::Var(children[0], children[1])
            }
            Kind::Symbol(SymbolKind::Const)
                if t.id() >= self.boundary
                    && !self.datatypes.contains_key(&t)
                    && !self.refused_symbols.contains_key(&t) =>
            {
                match store.ty(t) {
                    Some(ty) if store.kind(ty) == Kind::Type => Shape::Leaf,
                    Some(_) if self.is_sort_constructor(st, t) => {
                        return Err(unsupported(format!(
                            "the sort constructor {} without its arguments",
                            st.ck.show(t)
                        )));
                    }
                    Some(ty) => Shape::UConst(ty),
                    None => {
                        return Err(unsupported(format!("{} has no type", st.ck.show(t))));
                    }
                }
            }
            Kind::Symbol(SymbolKind::Const) | Kind::Lit(_) | Kind::Type | Kind::BoolType => {
                Shape::Leaf
            }
            _ => {
                return Err(unsupported(format!(
                    "a term the checker for CPC has no form for: {}",
                    st.ck.show(t)
                )));
            }
        })
    }

    fn leaf(&mut self, st: &State, t: Term) -> Result<CTerm> {
        let store = &st.ck.store;
        match store.kind(t) {
            Kind::Type => self.named("$emb_Type", &[]),
            Kind::BoolType => self.named("$emb_Bool", &[]),
            Kind::Lit(_) => {
                let lit = match store.lit(t) {
                    Some(Lit::Bool(b)) => return self.store.boolean(*b).map_err(refused),
                    Some(Lit::Numeral(n)) => cc::Lit::Numeral(integer(n)?),
                    // logos has rationals only
                    Some(Lit::Decimal(q) | Lit::Rational(q)) => cc::Lit::Rational(
                        cc::Rational::parse(&q.to_string())
                            .ok_or_else(|| unsupported(format!("the rational {q}")))?,
                    ),
                    // and bit-vectors in binary only
                    Some(Lit::Hex(b) | Lit::Binary(b)) => {
                        cc::Lit::Binary(cc::BitVec::new(b.size(), &integer(b.value())?))
                    }
                    Some(Lit::String(s)) => {
                        cc::Lit::String(cc::EoString::from_code_points(s.code_points().to_vec()))
                    }
                    None => return Err(unsupported("a literal without a value")),
                };
                self.store.literal(lit).map_err(refused)
            }
            Kind::Symbol(SymbolKind::Const) if t.id() < self.boundary => {
                let c = Self::constructor(st, t)?;
                if c.arity() != 0 {
                    return Err(unsupported(format!(
                        "{} without its indices",
                        st.ck.show(t)
                    )));
                }
                self.store.construct(c, &[]).map_err(refused)
            }
            Kind::Symbol(SymbolKind::Const) => {
                if let Some(&d) = self.datatypes.get(&t) {
                    return Ok(d);
                }
                if let Some(why) = self.refused_symbols.get(&t) {
                    return Err(unsupported(format!("{}: {why}", st.ck.show(t))));
                }
                // a sort the proof declares
                self.sort_of(t)
            }
            // an application of a sort constructor
            _ => self.sort_of(t),
        }
    }

    /// The store's term for `root`. `memo` holds the terms converted
    /// before, and takes the new ones.
    fn convert_with(
        &mut self,
        st: &mut State,
        root: Term,
        memo: &mut HashMap<Term, CTerm>,
    ) -> Result<CTerm> {
        // Terms can be deep, so no recursion: each term is visited once to
        // ask for its parts and once more to be built from them.
        let mut todo = vec![(root, false)];
        while let Some((t, parts_done)) = todo.pop() {
            if memo.contains_key(&t) {
                continue;
            }
            let shape = match self.parametric(st, t)? {
                Some(shape) => shape,
                None => self.shape(st, t)?,
            };
            let parts: Vec<Term> = match &shape {
                Shape::Leaf | Shape::Done(_) => Vec::new(),
                Shape::Headed(_, ts) | Shape::IndexedDone(_, _, ts) => ts.clone(),
                Shape::Apply(ts) | Shape::Fun(ts) => ts.clone(),
                Shape::Indexed(_, indices, rest) => indices.iter().chain(rest).copied().collect(),
                Shape::Var(name, ty) => vec![*name, *ty],
                Shape::UConst(ty) => vec![*ty],
            };
            if !parts_done && !parts.is_empty() {
                todo.push((t, true));
                todo.extend(
                    parts
                        .iter()
                        .filter(|p| !memo.contains_key(p))
                        .map(|&p| (p, false)),
                );
                continue;
            }
            let get = |p: &Term| {
                memo.get(p)
                    .copied()
                    .ok_or_else(|| unsupported("a cyclic term"))
            };
            let built = match shape {
                Shape::Leaf => self.leaf(st, t)?,
                Shape::Done(c) => c,
                Shape::Headed(head, ts) => {
                    let mut acc = head;
                    for a in &ts {
                        acc = self.store.apply(acc, get(a)?).map_err(refused)?;
                    }
                    acc
                }
                Shape::IndexedDone(c, index, rest) => {
                    let mut acc = self.store.construct(c, &[index]).map_err(refused)?;
                    for a in &rest {
                        acc = self.store.apply(acc, get(a)?).map_err(refused)?;
                    }
                    acc
                }
                Shape::Apply(ts) => {
                    let mut acc = get(&ts[0])?;
                    for a in &ts[1..] {
                        acc = self.store.apply(acc, get(a)?).map_err(refused)?;
                    }
                    acc
                }
                Shape::Fun(ts) => {
                    let fun = self.named("$emb_FunType", &[])?;
                    let (ret, args) = ts.split_last().ok_or_else(|| unsupported("a type"))?;
                    let mut acc = get(ret)?;
                    for a in args.iter().rev() {
                        let partial = self.store.apply(fun, get(a)?).map_err(refused)?;
                        acc = self.store.apply(partial, acc).map_err(refused)?;
                    }
                    acc
                }
                Shape::Indexed(c, indices, rest) => {
                    let fields = indices.iter().map(get).collect::<Result<Vec<_>>>()?;
                    let mut acc = self.store.construct(c, &fields).map_err(refused)?;
                    for a in &rest {
                        acc = self.store.apply(acc, get(a)?).map_err(refused)?;
                    }
                    acc
                }
                Shape::Var(name, ty) => {
                    let fields = [get(&name)?, get(&ty)?];
                    self.named("$emb_Var", &fields)?
                }
                Shape::UConst(ty) => match self.declared.get(&t) {
                    Some(&c) => c,
                    None => {
                        self.next_const += 1;
                        let id = self.raw_nat(self.next_const as usize)?;
                        let ty = get(&ty)?;
                        let c = self.named("$emb_UConst", &[id, ty])?;
                        self.declared.insert(t, c);
                        c
                    }
                },
            };
            memo.insert(t, built);
        }
        memo.get(&root)
            .copied()
            .ok_or_else(|| unsupported("a cyclic term"))
    }

    fn convert(&mut self, st: &mut State, t: Term) -> Result<CTerm> {
        let mut memo = std::mem::take(&mut self.memo);
        let r = self.convert_with(st, t, &mut memo);
        self.memo = memo;
        r
    }

    fn list(&mut self, nil: &str, cons: &str, items: &[CTerm]) -> Result<CTerm> {
        let mut acc = self.named(nil, &[])?;
        for &item in items.iter().rev() {
            acc = self.named(cons, &[item, acc])?;
        }
        Ok(acc)
    }

    fn push(&mut self, formula: Term) {
        self.positions
            .entry(formula)
            .or_default()
            .push(self.stack.len());
        self.stack.push(formula);
    }

    fn truncate(&mut self, height: usize) {
        while self.stack.len() > height {
            if let Some(f) = self.stack.pop()
                && let Some(ps) = self.positions.get_mut(&f)
            {
                ps.pop();
            }
        }
    }

    /// What a step leaves in the state: a `step-pop` first takes away
    /// everything from its `assume-push` on.
    fn proved(&mut self, formula: Term, is_pop: bool) -> Result<()> {
        if is_pop {
            let height = self
                .push_heights
                .pop()
                .ok_or_else(|| unsupported("a step-pop without an assume-push"))?;
            self.truncate(height);
        }
        self.push(formula);
        Ok(())
    }

    fn assume(&mut self, st: &mut State, name: &str, formula: Term, is_push: bool) -> Result<()> {
        let f = self.convert(st, formula)?;
        if is_push {
            let cmd = self.named("$emb_cmd.assume_push", &[f])?;
            self.commands.push(cmd);
            self.labels.push(format!("the assume-push {name}"));
            self.push_heights.push(self.stack.len());
        } else {
            if !self.commands.is_empty() {
                // logos refuses this too: a proof is a set of assumptions
                // and the steps that refute it
                return Err(unsupported("an assume after the first proof step"));
            }
            self.assumptions.push(f);
        }
        self.push(formula);
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn step(
        &mut self,
        st: &mut State,
        step_name: &str,
        rule: Term,
        proven: Option<Term>,
        premises: &[Term],
        args: &[Term],
        is_pop: bool,
    ) -> Result<()> {
        let rule_name = st
            .ck
            .store
            .symbol_name(rule)
            .unwrap_or_default()
            .to_string();
        // the compiler writes the hyphens of a rule's name as underscores
        let rule = Constructor::from_name(&format!("$emb_r.{}", rule_name.replace('-', "_")))
            .ok_or_else(|| unsupported(format!("the checker for CPC has no rule {rule_name}")))?;
        let rule = self.store.construct(rule, &[]).map_err(refused)?;
        let mut cargs = Vec::with_capacity(args.len());
        for &a in args {
            cargs.push(self.convert(st, a)?);
        }
        let cargs = self.list("$emb_al.nil", "$emb_al.cons", &cargs)?;
        let mut indices = Vec::with_capacity(premises.len());
        for &p in premises {
            // a premise is the proof of a formula; the checker wants to
            // know how far down its state the formula stands
            if st.ck.store.kind(p) != Kind::Node(NodeKind::Proof) {
                return Err(unsupported(format!(
                    "the premise {} is not a proof",
                    st.ck.show(p)
                )));
            }
            let formula = st.ck.store.child(p, 0);
            let pos = self
                .positions
                .get(&formula)
                .and_then(|ps| ps.last())
                .ok_or_else(|| {
                    unsupported(format!(
                        "a premise proving {} is not in scope",
                        st.ck.show(formula)
                    ))
                })?;
            indices.push(self.raw_nat(self.stack.len() - pos - 1)?);
        }
        let indices = self.list("$emb_indl.nil", "$emb_indl.cons", &indices)?;
        let name = if is_pop {
            "$emb_cmd.step_pop"
        } else {
            "$emb_cmd.step"
        };
        let cmd = self.named(name, &[rule, cargs, indices])?;
        self.commands.push(cmd);
        self.labels
            .push(format!("the step {step_name} (rule {rule_name})"));
        match proven {
            Some(formula) => {
                // the checker compares what the rule gives with what the
                // step states
                let f = self.convert(st, formula)?;
                let cmd = self.named("$emb_cmd.check_proven", &[f])?;
                self.commands.push(cmd);
                self.labels.push(format!(
                    "the conclusion of the step {step_name} (rule {rule_name}): the rule gives \
                     another formula"
                ));
                self.proved(formula, is_pop)
            }
            None => {
                self.pending_step = Some(is_pop);
                Ok(())
            }
        }
    }

    fn declare_datatypes(
        &mut self,
        st: &mut State,
        datatypes: &[(Term, Vec<Term>)],
        constructors: &[(Term, Vec<Term>)],
    ) -> Result<()> {
        let store = &st.ck.store;
        let sels_of = |c: Term| {
            constructors
                .iter()
                .find(|(c2, _)| *c2 == c)
                .map_or(&[][..], |(_, s)| s.as_slice())
        };
        let is_parametric = datatypes
            .iter()
            .any(|(d, _)| store.ty(*d).is_none_or(|ty| store.kind(ty) != Kind::Type));
        if is_parametric {
            // A parametric block is a template: its datatypes are declared
            // to the checker one instance at a time, as they are used.
            self.next_block += 1;
            for (d, conses) in datatypes {
                let mut params = Vec::new();
                let mut with_sels = Vec::new();
                for (k, &c) in conses.iter().enumerate() {
                    self.roles.insert(c, Role::Constructor(k));
                    for (j, &sel) in sels_of(c).iter().enumerate() {
                        self.roles.insert(sel, Role::Selector(k, j));
                        // a selector takes the datatype applied to its
                        // parameters
                        if let Some(&applied) =
                            store.ty(sel).and_then(|ty| store.children(ty).first())
                        {
                            params = spine(st, applied).1;
                        }
                    }
                    with_sels.push((c, sels_of(c).to_vec()));
                }
                self.templates.insert(
                    *d,
                    Template {
                        block: self.next_block,
                        name: store.symbol_name(*d).unwrap_or_default().to_string(),
                        params,
                        constructors: with_sels,
                    },
                );
            }
            return Ok(());
        }
        // the selectors of each constructor of each datatype, and the type
        // of each field: what the selector returns
        let mut shapes: Vec<Vec<Vec<(Term, Term)>>> = Vec::new();
        for (_, conses) in datatypes {
            let mut dshape = Vec::new();
            for &c in conses {
                let mut fields = Vec::new();
                for &sel in sels_of(c) {
                    fields.push((sel, field_type(st, sel)?));
                }
                dshape.push(fields);
            }
            shapes.push(dshape);
        }
        let dt_names: Vec<String> = datatypes
            .iter()
            .map(|(d, _)| store.symbol_name(*d).unwrap_or_default().to_string())
            .collect();
        // Inside the block, its datatypes are references by name.
        let mut memo = HashMap::new();
        let mut names = Vec::with_capacity(datatypes.len());
        for ((d, _), name) in datatypes.iter().zip(&dt_names) {
            let name = self.raw_name(name)?;
            let r = self.named("$emb_DatatypeTypeRef", &[name])?;
            memo.insert(*d, r);
            names.push(name);
        }
        // The datatypes of the block each constructor refers to, for the
        // order below.
        let block: Vec<Term> = datatypes.iter().map(|(d, _)| *d).collect();
        let mut refs: Vec<Vec<Vec<usize>>> = Vec::new();
        let mut bodies = Vec::with_capacity(datatypes.len());
        for dshape in &shapes {
            let mut drefs = Vec::new();
            let mut cons_terms = Vec::new();
            for fields in dshape {
                let mut crefs = Vec::new();
                let mut field_terms = Vec::new();
                for &(_, ty) in fields {
                    mentions(st, ty, &block, &mut crefs);
                    field_terms.push(self.convert_with(st, ty, &mut memo)?);
                }
                drefs.push(crefs);
                cons_terms.push(self.list("$emb_edtc.unit", "$emb_edtc.cons", &field_terms)?);
            }
            refs.push(drefs);
            bodies.push(self.list("$emb_edt.null", "$emb_edt.sum", &cons_terms)?);
        }
        // logos declares a block in an order in which each datatype has a
        // value built from the ones after it.
        let order = productive_order(&refs);
        let mut decl = self.named("$emb_edd.nil", &[])?;
        for &i in order.iter().rev() {
            decl = self.named("$emb_edd.cons", &[names[i], bodies[i], decl])?;
        }
        for (i, (d, conses)) in datatypes.iter().enumerate() {
            let arities: Vec<usize> = shapes[i].iter().map(Vec::len).collect();
            let inst = self.declared_terms(names[i], decl, &arities)?;
            self.datatypes.insert(*d, inst.sort);
            for (k, &c) in conses.iter().enumerate() {
                self.datatypes.insert(c, inst.constructors[k]);
                for (j, &(sel, _)) in shapes[i][k].iter().enumerate() {
                    self.datatypes.insert(sel, inst.selectors[k][j]);
                }
            }
        }
        Ok(())
    }

    /// The sort, the constructors and the selectors of the datatype `name`
    /// of the declaration `decl`, whose constructors take `arities`
    /// fields.
    fn declared_terms(&mut self, name: CTerm, decl: CTerm, arities: &[usize]) -> Result<Instance> {
        let sort = self.named("$emb_DatatypeType", &[name, decl])?;
        let mut constructors = Vec::new();
        let mut selectors = Vec::new();
        for (k, &n) in arities.iter().enumerate() {
            let ki = self.raw_nat(k)?;
            constructors.push(self.named("$emb_DtCons", &[name, decl, ki])?);
            let mut sels = Vec::new();
            for j in 0..n {
                let ji = self.raw_nat(j)?;
                sels.push(self.named("$emb_DtSel", &[name, decl, ki, ji])?);
            }
            selectors.push(sels);
        }
        Ok(Instance {
            sort,
            constructors,
            selectors,
        })
    }

    /// The parametric datatype and the arguments that the type `ty` applies
    /// it to, if `ty` is such an application.
    fn instance_key(&self, st: &State, ty: Term) -> Option<InstanceKey> {
        if self.templates.is_empty() {
            return None;
        }
        let (head, args) = spine(st, ty);
        let tmpl = self.templates.get(&head)?;
        // a datatype without fields has no parameters on record
        let fields = tmpl.constructors.iter().any(|(_, sels)| !sels.is_empty());
        (!fields || tmpl.params.len() == args.len()).then_some((head, args))
    }

    /// The field types of the instance `key`, constructor by constructor:
    /// those of the template with the arguments in place of the parameters.
    fn instance_fields(&self, st: &mut State, key: &InstanceKey) -> Result<Vec<Vec<Term>>> {
        let tmpl = &self.templates[&key.0];
        let ctx: pathos_check::Ctx = tmpl
            .params
            .iter()
            .copied()
            .zip(key.1.iter().copied())
            .collect();
        let mut out = Vec::new();
        for (_, sels) in &tmpl.constructors {
            let mut fields = Vec::new();
            for &sel in sels {
                let ty = field_type(st, sel)?;
                fields.push(if ctx.is_empty() {
                    ty
                } else {
                    st.ck.evaluate(ty, &ctx)
                });
            }
            out.push(fields);
        }
        Ok(out)
    }

    /// The instances of the block `block` that the type `ty` mentions.
    fn mentioned_instances(
        &self,
        st: &State,
        ty: Term,
        block: usize,
        found: &mut Vec<InstanceKey>,
    ) {
        let mut seen = std::collections::HashSet::new();
        let mut todo = vec![ty];
        while let Some(t) = todo.pop() {
            if !seen.insert(t) {
                continue;
            }
            if let Some(key) = self.instance_key(st, t) {
                // its arguments may mention others
                todo.extend_from_slice(&key.1);
                if self.templates[&key.0].block == block && !found.contains(&key) {
                    found.push(key);
                }
                continue;
            }
            todo.extend_from_slice(st.ck.store.children(t));
        }
    }

    /// Declares the instance `root` to the checker, with the instances its
    /// fields need. As logos does it: the instances that need each other
    /// form one declaration, a declaration comes after those it refers to,
    /// and each instance is named `.par_<n>_<datatype>` in the order the
    /// instances are found.
    fn ensure_instance(&mut self, st: &mut State, root: &InstanceKey) -> Result<()> {
        if self.instances.contains_key(root) {
            return Ok(());
        }
        let block = self.templates[&root.0].block;
        // the instances not declared yet that `root` reaches, with their
        // fields and the instances each one mentions
        let mut nodes: Vec<InstanceKey> = vec![root.clone()];
        let mut fields: Vec<Vec<Vec<Term>>> = Vec::new();
        let mut uses: Vec<Vec<InstanceKey>> = Vec::new();
        let mut i = 0;
        while i < nodes.len() {
            let f = self.instance_fields(st, &nodes[i])?;
            let mut mentioned = Vec::new();
            for &ty in f.iter().flatten() {
                self.mentioned_instances(st, ty, block, &mut mentioned);
            }
            for key in &mentioned {
                if !self.instances.contains_key(key) && !nodes.contains(key) {
                    if nodes.len() >= 10_000 {
                        return Err(unsupported(
                            "a parametric datatype that needs too many instances",
                        ));
                    }
                    nodes.push(key.clone());
                }
            }
            fields.push(f);
            uses.push(mentioned);
            i += 1;
        }
        let n = nodes.len();
        let index = |key: &InstanceKey| nodes.iter().position(|k| k == key);
        // which instance reaches which
        let mut reach = vec![vec![false; n]; n];
        for (a, row) in reach.iter_mut().enumerate() {
            let mut todo = vec![a];
            while let Some(x) = todo.pop() {
                for b in uses[x].iter().filter_map(index) {
                    if !row[b] {
                        row[b] = true;
                        todo.push(b);
                    }
                }
            }
        }
        let mut names: Vec<Option<CTerm>> = vec![None; n];
        let mut done = vec![false; n];
        while done.iter().any(|d| !d) {
            // a group of instances that need each other and nothing else
            // that is not declared
            let Some(first) = (0..n).find(|&a| {
                !done[a] && (0..n).all(|b| done[b] || !reach[a][b] || reach[b][a] || a == b)
            }) else {
                return Err(unsupported(
                    "a parametric datatype whose instances have no order",
                ));
            };
            let group: Vec<usize> = (0..n)
                .filter(|&b| !done[b] && (b == first || (reach[first][b] && reach[b][first])))
                .collect();
            for &m in &group {
                self.next_instance += 1;
                let name = format!(
                    ".par_{}_{}",
                    self.next_instance, self.templates[&nodes[m].0].name
                );
                let name = self.raw_string(&name)?;
                names[m] = Some(name);
                let r = self.named("$emb_DatatypeTypeRef", &[name])?;
                self.building.insert(nodes[m].clone(), r);
            }
            // inside the declaration the group's instances are references,
            // so the terms built here are not those of the proof
            let mut memo = HashMap::new();
            let mut bodies = Vec::new();
            let mut refs: Vec<Vec<Vec<usize>>> = Vec::new();
            let mut failed = None;
            'group: for &m in &group {
                let mut cons_terms = Vec::new();
                let mut drefs = Vec::new();
                for cons_fields in &fields[m] {
                    let mut field_terms = Vec::new();
                    let mut mentioned = Vec::new();
                    for &ty in cons_fields {
                        self.mentioned_instances(st, ty, block, &mut mentioned);
                        match self.convert_with(st, ty, &mut memo) {
                            Ok(t) => field_terms.push(t),
                            Err(e) => {
                                failed = Some(e);
                                break 'group;
                            }
                        }
                    }
                    drefs.push(
                        mentioned
                            .iter()
                            .filter_map(|k| {
                                index(k).and_then(|x| group.iter().position(|&g| g == x))
                            })
                            .collect(),
                    );
                    cons_terms.push(self.list("$emb_edtc.unit", "$emb_edtc.cons", &field_terms)?);
                }
                refs.push(drefs);
                bodies.push(self.list("$emb_edt.null", "$emb_edt.sum", &cons_terms)?);
            }
            for &m in &group {
                self.building.remove(&nodes[m]);
            }
            if let Some(e) = failed {
                return Err(e);
            }
            let order = productive_order(&refs);
            let mut decl = self.named("$emb_edd.nil", &[])?;
            for &g in order.iter().rev() {
                let name =
                    names[group[g]].ok_or_else(|| unsupported("an instance without a name"))?;
                decl = self.named("$emb_edd.cons", &[name, bodies[g], decl])?;
            }
            for &m in &group {
                let arities: Vec<usize> = fields[m].iter().map(Vec::len).collect();
                let name = names[m].ok_or_else(|| unsupported("an instance without a name"))?;
                let inst = self.declared_terms(name, decl, &arities)?;
                self.instances.insert(nodes[m].clone(), inst);
                done[m] = true;
            }
        }
        Ok(())
    }

    /// The instance that the type `ty` is, declared if it was not.
    fn instance_of_type(&mut self, st: &mut State, ty: Term, what: Term) -> Result<InstanceKey> {
        let Some(key) = self.instance_key(st, ty) else {
            return Err(unsupported(format!(
                "{} is used at the type {}, which is not an instance of its datatype",
                st.ck.show(what),
                st.ck.show(ty)
            )));
        };
        self.ensure_instance(st, &key)?;
        Ok(key)
    }

    fn type_of(st: &mut State, t: Term) -> Result<Term> {
        st.ck
            .get_type(t, None)
            .ok_or_else(|| unsupported(format!("{} has no type", st.ck.show(t))))
    }

    /// What `t` is if it is a use of a parametric datatype: the sort of an
    /// instance, or one of its constructors, selectors, testers or
    /// updaters applied. Which instance follows from the types, as in
    /// logos: a constructor's from the type of its application, a
    /// selector's, a tester's and an updater's from the type of the term
    /// they are applied to.
    fn parametric(&mut self, st: &mut State, t: Term) -> Result<Option<Shape>> {
        if self.templates.is_empty() {
            return Ok(None);
        }
        if let Some(key) = self.instance_key(st, t) {
            if let Some(&r) = self.building.get(&key) {
                return Ok(Some(Shape::Done(r)));
            }
            self.ensure_instance(st, &key)?;
            return Ok(Some(Shape::Done(self.instances[&key].sort)));
        }
        let (head, args) = spine(st, t);
        // a constructor that needs its type comes with it: (as nil (List Int))
        let annotated = (st.ck.store.kind(head) == Kind::Node(NodeKind::ApplyOpaque))
            .then(|| st.ck.store.children(head).to_vec())
            .filter(|c| {
                c.len() == 2 && matches!(self.roles.get(&c[0]), Some(Role::Constructor(_)))
            });
        if let Some(c) = annotated {
            let Some(&Role::Constructor(k)) = self.roles.get(&c[0]) else {
                return Ok(None);
            };
            let key = self.instance_of_type(st, c[1], c[0])?;
            return Ok(Some(Shape::Headed(
                self.instances[&key].constructors[k],
                args,
            )));
        }
        match self.roles.get(&head).copied() {
            Some(Role::Constructor(k)) => {
                let ty = Self::type_of(st, t)?;
                let key = self.instance_of_type(st, ty, head)?;
                return Ok(Some(Shape::Headed(
                    self.instances[&key].constructors[k],
                    args,
                )));
            }
            Some(Role::Selector(k, j)) => {
                let Some(&operand) = args.first() else {
                    return Err(unsupported(format!(
                        "the selector {} without the term it selects from",
                        st.ck.show(head)
                    )));
                };
                let ty = Self::type_of(st, operand)?;
                let key = self.instance_of_type(st, ty, head)?;
                return Ok(Some(Shape::Headed(
                    self.instances[&key].selectors[k][j],
                    args,
                )));
            }
            None => {}
        }
        // a tester or an updater, (_ is cons) or (update sel), applied
        let (op, indexed, rest) = if st.ck.store.kind(head) == Kind::Node(NodeKind::ApplyOpaque) {
            let c = st.ck.store.children(head);
            if c.len() != 2 {
                return Ok(None);
            }
            (c[0], c[1], args)
        } else if args.len() >= 2 {
            (head, args[0], args[1..].to_vec())
        } else {
            return Ok(None);
        };
        let Some(role) = self.roles.get(&indexed).copied() else {
            return Ok(None);
        };
        if !self.is_signature_symbol(st, op) {
            return Ok(None);
        }
        let c = Self::constructor(st, op)?;
        let Some(&operand) = rest.first() else {
            return Err(unsupported(format!(
                "{} without the term it is applied to",
                st.ck.show(t)
            )));
        };
        if c.arity() != 1 {
            return Ok(None);
        }
        let ty = Self::type_of(st, operand)?;
        let key = self.instance_of_type(st, ty, indexed)?;
        let inst = &self.instances[&key];
        let index = match role {
            Role::Constructor(k) => inst.constructors[k],
            Role::Selector(k, j) => inst.selectors[k][j],
        };
        Ok(Some(Shape::IndexedDone(c, index, rest)))
    }

    /// The assumption list as the checker takes it. The checker pushes the
    /// head of the list last, so the list starts with the last assumption.
    fn assumption_list(&mut self) -> Result<CTerm> {
        let mut reversed = self.assumptions.clone();
        reversed.reverse();
        self.list("$emb_al.nil", "$emb_al.cons", &reversed)
    }

    /// Says where the compiled checker stops accepting the proof.
    pub fn explain(&mut self) -> Result<String> {
        let assumptions = self.assumption_list()?;
        let (store, commands, labels) = (&mut self.store, &self.commands, &self.labels);
        cc::with_checker_stack(|| crate::explain::explain(store, assumptions, commands, labels))
            .map_err(|e| Error::plain(format!("the compiled checker stopped: {e}")))
    }

    /// The checker's caches after a run, in one line.
    pub fn cache_stats(&self) -> String {
        let c = self.store.cache_stats();
        format!(
            "caches: types {} hits, {} misses, {} entries; programs {} hits, {} misses, {} entries",
            c.type_hits,
            c.type_misses,
            c.type_entries,
            c.program_hits,
            c.program_misses,
            c.program_entries
        )
    }

    /// Runs the compiled checker on what was written down.
    pub fn check(&mut self) -> Result<Verdict> {
        let assumptions = self.assumption_list()?;
        let commands = self.commands.clone();
        let commands = self.list("$emb_cmdl.nil", "$emb_cmdl.cons", &commands)?;
        self.store.check_proof(assumptions, commands).map_err(|e| {
            Error::plain(format!(
                "the compiled checker stopped without a verdict: {e}"
            ))
        })
    }
}

fn integer(n: &pathos_term::Integer) -> Result<cc::Integer> {
    cc::Integer::parse(&n.to_string_base(10), 10)
        .ok_or_else(|| unsupported(format!("the integer {n}")))
}

/// The type of the field a selector selects: what the selector returns.
fn field_type(st: &State, sel: Term) -> Result<Term> {
    let store = &st.ck.store;
    store
        .ty(sel)
        .and_then(|ty| store.children(ty).last().copied())
        .ok_or_else(|| unsupported("a selector without a type"))
}

/// The head of a curried application and its arguments, in order.
fn spine(st: &State, mut t: Term) -> (Term, Vec<Term>) {
    let mut args = Vec::new();
    while st.ck.store.kind(t) == Kind::APPLY {
        let children = st.ck.store.children(t);
        args.extend(children[1..].iter().rev());
        t = children[0];
    }
    args.reverse();
    (t, args)
}

/// Adds to `found` the positions in `block` of the terms `t` mentions.
fn mentions(st: &State, t: Term, block: &[Term], found: &mut Vec<usize>) {
    let mut seen = std::collections::HashSet::new();
    let mut todo = vec![t];
    while let Some(t) = todo.pop() {
        if !seen.insert(t) {
            continue;
        }
        if let Some(i) = block.iter().position(|&b| b == t) {
            if !found.contains(&i) {
                found.push(i);
            }
            continue;
        }
        todo.extend_from_slice(st.ck.store.children(t));
    }
}

/// logos's `productiveOrder` (`Logos/Parser/Core.lean`): the positions of
/// the datatypes of a block in the order it is declared in. `refs` gives,
/// for each datatype and each of its constructors, the datatypes of the
/// block the constructor refers to. A datatype is ready once one of its
/// constructors refers only to datatypes placed before; those ready first
/// come last.
fn productive_order(refs: &[Vec<Vec<usize>>]) -> Vec<usize> {
    let mut placed: Vec<usize> = Vec::new();
    let mut remaining: Vec<usize> = (0..refs.len()).collect();
    let mut order: Vec<usize> = Vec::new();
    for _ in 0..refs.len() {
        let (ready, rest): (Vec<usize>, Vec<usize>) = remaining.iter().partition(|&&d| {
            refs[d]
                .iter()
                .any(|cons| cons.iter().all(|r| placed.contains(r)))
        });
        if ready.is_empty() {
            break;
        }
        placed.extend_from_slice(&ready);
        order.splice(0..0, ready);
        remaining = rest;
    }
    remaining.extend(order);
    remaining
}

/// The plugin: it shares what it builds with the caller, which runs the
/// checker when the proof has been read.
pub struct Adapter {
    built: Rc<RefCell<Built>>,
}

impl Adapter {
    /// An adapter for a state that holds the signature and nothing else
    /// yet.
    pub fn new(st: &State, caching: bool) -> (Adapter, Rc<RefCell<Built>>) {
        let boundary = u32::try_from(st.ck.store.len()).unwrap_or(u32::MAX);
        let built = Rc::new(RefCell::new(Built::new(boundary, caching)));
        (
            Adapter {
                built: built.clone(),
            },
            built,
        )
    }
}

impl Plugin for Adapter {
    fn bind(&mut self, st: &mut State, _name: &str, e: Term) -> Result<()> {
        let mut b = self.built.borrow_mut();
        // the conclusion of a step the interpreter checked
        if let Some(is_pop) = b.pending_step
            && st.ck.store.kind(e) == Kind::Node(NodeKind::Proof)
        {
            b.pending_step = None;
            let formula = st.ck.store.child(e, 0);
            b.proved(formula, is_pop)?;
        }
        Ok(())
    }

    fn declare_datatypes(
        &mut self,
        st: &mut State,
        datatypes: &[(Term, Vec<Term>)],
        constructors: &[(Term, Vec<Term>)],
    ) -> Result<()> {
        self.built
            .borrow_mut()
            .declare_datatypes(st, datatypes, constructors)
    }

    fn notify_assume(
        &mut self,
        st: &mut State,
        name: &str,
        proven: &mut Term,
        is_push: bool,
    ) -> Result<()> {
        self.built.borrow_mut().assume(st, name, *proven, is_push)
    }

    fn notify_step(
        &mut self,
        st: &mut State,
        name: &str,
        rule: Term,
        proven: Option<Term>,
        premises: &[Term],
        args: &[Term],
        is_pop: bool,
        err: Option<&mut String>,
    ) -> Result<Option<StepResult>> {
        if err.is_some() {
            // asked again, for the reason of a failure: the step is
            // already written down
            return Ok(None);
        }
        self.built
            .borrow_mut()
            .step(st, name, rule, proven, premises, args, is_pop)?;
        // With a stated conclusion the front end goes on as if the step
        // proved it; the compiled checker says later whether it does.
        // Without one, the interpreter computes what the step proves.
        Ok(proven.map(|p| StepResult { result: Some(p) }))
    }
}
