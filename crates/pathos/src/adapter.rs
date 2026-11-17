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
    fn new(boundary: u32) -> Built {
        let limits = Limits {
            terms: u32::MAX,
            calls: u64::MAX,
            depth: 100_000,
        };
        Built {
            store: Store::new(limits),
            boundary,
            memo: HashMap::new(),
            datatypes: HashMap::new(),
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

    /// A datatype's name as logos keeps it: a leading dot is doubled.
    fn raw_name(&mut self, name: &str) -> Result<CTerm> {
        let name = if name.starts_with('.') {
            format!(".{name}")
        } else {
            name.to_string()
        };
        let points = name.chars().map(u32::from).collect();
        self.store
            .raw(cc::Lit::String(cc::EoString::from_code_points(points)))
            .map_err(refused)
    }

    fn fresh_sort(&mut self) -> Result<CTerm> {
        self.next_sort += 1;
        let id = self.raw_nat(self.next_sort as usize)?;
        self.named("$emb_USort", &[id])
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
                self.fresh_sort()
            }
            // an application of a sort constructor
            _ => self.fresh_sort(),
        }
    }

    /// The store's term for `root`. `memo` holds the terms converted
    /// before, and takes the new ones.
    fn convert_with(
        &mut self,
        st: &State,
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
            let shape = self.shape(st, t)?;
            let parts: Vec<Term> = match &shape {
                Shape::Leaf => Vec::new(),
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
                Shape::UConst(ty) => {
                    self.next_const += 1;
                    let id = self.raw_nat(self.next_const as usize)?;
                    let ty = get(&ty)?;
                    self.named("$emb_UConst", &[id, ty])?
                }
            };
            memo.insert(t, built);
        }
        memo.get(&root)
            .copied()
            .ok_or_else(|| unsupported("a cyclic term"))
    }

    fn convert(&mut self, st: &State, t: Term) -> Result<CTerm> {
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

    fn assume(&mut self, st: &State, name: &str, formula: Term, is_push: bool) -> Result<()> {
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
        st: &State,
        step_name: &str,
        rule: Term,
        proven: Option<Term>,
        premises: &[Term],
        args: &[Term],
        is_pop: bool,
    ) -> Result<()> {
        let rule_name = st.ck.store.symbol_name(rule).unwrap_or_default();
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
        st: &State,
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
            let why = "parametric datatypes are not read yet";
            for (d, conses) in datatypes {
                self.refused_symbols.insert(*d, why);
                for &c in conses {
                    self.refused_symbols.insert(c, why);
                    for &s in sels_of(c) {
                        self.refused_symbols.insert(s, why);
                    }
                }
            }
            return Ok(());
        }
        // the type of each field: what the selector returns
        let field_type = |sel: Term| -> Result<Term> {
            store
                .ty(sel)
                .and_then(|ty| store.children(ty).last().copied())
                .ok_or_else(|| unsupported("a selector without a type"))
        };
        // Inside the block, its datatypes are references by name.
        let mut memo = HashMap::new();
        let mut names = Vec::with_capacity(datatypes.len());
        for (d, _) in datatypes {
            let name = self.raw_name(store.symbol_name(*d).unwrap_or_default())?;
            let r = self.named("$emb_DatatypeTypeRef", &[name])?;
            memo.insert(*d, r);
            names.push(name);
        }
        // The datatypes of the block each constructor refers to, for the
        // order below.
        let block: Vec<Term> = datatypes.iter().map(|(d, _)| *d).collect();
        let mut refs: Vec<Vec<Vec<usize>>> = Vec::new();
        let mut bodies = Vec::with_capacity(datatypes.len());
        for (_, conses) in datatypes {
            let mut drefs = Vec::new();
            let mut cons_terms = Vec::new();
            for &c in conses {
                let mut crefs = Vec::new();
                let mut fields = Vec::new();
                for &s in sels_of(c) {
                    let ty = field_type(s)?;
                    mentions(st, ty, &block, &mut crefs);
                    fields.push(self.convert_with(st, ty, &mut memo)?);
                }
                drefs.push(crefs);
                cons_terms.push(self.list("$emb_edtc.unit", "$emb_edtc.cons", &fields)?);
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
            let sort = self.named("$emb_DatatypeType", &[names[i], decl])?;
            self.datatypes.insert(*d, sort);
            for (k, &c) in conses.iter().enumerate() {
                let ki = self.raw_nat(k)?;
                let cons = self.named("$emb_DtCons", &[names[i], decl, ki])?;
                self.datatypes.insert(c, cons);
                for (j, &s) in sels_of(c).iter().enumerate() {
                    let ji = self.raw_nat(j)?;
                    let sel = self.named("$emb_DtSel", &[names[i], decl, ki, ji])?;
                    self.datatypes.insert(s, sel);
                }
            }
        }
        Ok(())
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
    pub fn new(st: &State) -> (Adapter, Rc<RefCell<Built>>) {
        let boundary = u32::try_from(st.ck.store.len()).unwrap_or(u32::MAX);
        let built = Rc::new(RefCell::new(Built::new(boundary)));
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
