//! Building terms (`State::mkExpr` and its helpers in Ethos's `state.cpp`).
//!
//! [`Checker::mk_expr`] is what the parser calls for `(f t1 ... tn)`. It
//! applies the desugaring that the head's attributes ask for (associativity,
//! chaining, opaque arguments, overloads), reduces applications of macros and
//! programs, and evaluates `eo::` operators.

use pathos_term::{Kind, NodeKind, SymbolKind, Term};

use crate::attr::Attr;
use crate::checker::{Checker, Ctx};

impl Checker {
    /// `(-> args... ret)`, nested to the right; `ret` itself without `args`.
    pub fn mk_function_type(&mut self, args: &[Term], ret: Term) -> Term {
        let mut curr = ret;
        for &a in args.iter().rev() {
            curr = self.store.mk(Kind::FUNCTION_TYPE, &[a, curr]);
        }
        curr
    }

    /// The type of a program taking `args` and returning `ret`. Unlike
    /// function types, these are not nested.
    pub fn mk_program_type(&mut self, args: &[Term], ret: Term) -> Term {
        let mut children = args.to_vec();
        children.push(ret);
        self.store.mk(Kind::PROGRAM_TYPE, &children)
    }

    /// A type constant of the given arity: `Type`, or
    /// `(-> Type ... Type Type)`.
    pub fn mk_type_constant(&mut self, name: &str, arity: usize) -> Term {
        let ty = self.mk_type();
        let args = vec![ty; arity];
        let t = self.mk_function_type(&args, ty);
        self.mk_symbol(SymbolKind::Const, name, t)
    }

    /// `(eo::requires a1 a2 ret)`, which may evaluate at once.
    pub fn mk_requires(&mut self, a1: Term, a2: Term, ret: Term) -> Term {
        self.mk_expr(Kind::Eval(pathos_term::EvalOp::Requires), &[a1, a2, ret])
    }

    /// Wraps `ret` in one `eo::requires` for each pair in `pairs`.
    pub fn mk_requires_list(&mut self, pairs: &[Term], ret: Term) -> Term {
        let mut curr = ret;
        for &p in pairs.iter().rev() {
            let (a, b) = (self.store.child(p, 0), self.store.child(p, 1));
            curr = self.mk_requires(a, b, curr);
        }
        curr
    }

    /// `(eo::pf proven)`.
    pub fn mk_proof(&mut self, proven: Term) -> Term {
        self.store.mk(Kind::PROOF, &[proven])
    }

    /// `(eo::quote t)`, for a parameter `t`.
    pub fn mk_quote_type(&mut self, t: Term) -> Term {
        self.store.mk(Kind::QUOTE_TYPE, &[t])
    }

    pub fn mk_pair(&mut self, t1: Term, t2: Term) -> Term {
        self.store.mk(Kind::TUPLE, &[t1, t2])
    }

    /// `(eo::_ (eo::tuple params...) hd)`.
    pub fn mk_parameterized(&mut self, hd: Term, params: &[Term]) -> Term {
        let tuple = self.mk_expr(Kind::TUPLE, params);
        self.mk_expr(Kind::PARAMETERIZED, &[tuple, hd])
    }

    /// `(eo::List::cons args...)`, or `eo::List::nil` without `args`.
    pub fn mk_list(&mut self, args: &[Term]) -> Term {
        if args.is_empty() {
            return self.list_nil;
        }
        let mut largs = vec![self.list_cons];
        largs.extend_from_slice(args);
        self.mk_expr(Kind::APPLY, &largs)
    }

    /// The variable `(eo::var "name" type)`.
    pub fn get_bound_var(&mut self, name: &str, ty: Term) -> Term {
        let ename = self.mk_string_literal(name);
        self.mk_expr(Kind::VARIABLE, &[ename, ty])
    }

    /// The list of variables of a binder application, built with the
    /// binder's list constructor.
    pub fn mk_binder_list(&mut self, binder: Term, vs: &[Term]) -> Option<Term> {
        let cons = self.attribute_term(binder)?;
        let mut vlist = vec![cons];
        vlist.extend_from_slice(vs);
        Some(self.mk_expr(Kind::APPLY, &vlist))
    }

    /// The list of bindings of a let-binder application.
    pub fn mk_let_binder_list(&mut self, binder: Term, lls: &[(Term, Term)]) -> Option<Term> {
        let cons = self.attribute_term(binder)?;
        if self.store.kind(cons) != Kind::TUPLE || self.store.num_children(cons) != 2 {
            return None;
        }
        let (pair_cons, list_cons) = (self.store.child(cons, 0), self.store.child(cons, 1));
        let mut vlist = vec![list_cons];
        for &(v, t) in lls {
            vlist.push(self.mk_expr(Kind::APPLY, &[pair_cons, v, t]));
        }
        Some(self.mk_expr(Kind::APPLY, &vlist))
    }

    /// The type of a symbol that must be written `(as <symbol> <type>)`:
    /// `(-> (eo::quote x) ($eo_disamb_type_<name> x))`, where the program
    /// `$eo_disamb_type_<name>` maps `disamb_pat` to `ret`.
    pub fn mk_disambiguated_type(&mut self, disamb_pat: Term, ret: Term, name: &str) -> Term {
        let ty = self.mk_type();
        let pt = self.mk_program_type(&[ty], ty);
        let prog_name = format!("$eo_disamb_type_{name}");
        let tprog = self.mk_symbol(SymbolKind::ProgramConst, &prog_name, pt);
        let tpat = self.mk_expr(Kind::APPLY, &[tprog, disamb_pat]);
        let prog_case = self.mk_pair(tpat, ret);
        let prog = self.mk_expr(Kind::PROGRAM, &[prog_case]);
        self.define_program(tprog, Some(prog));
        let tv = self.mk_symbol(SymbolKind::Param, &format!("{prog_name}_var"), ty);
        let qtv = self.mk_quote_type(tv);
        let fapp = self.mk_expr(Kind::APPLY, &[tprog, tv]);
        self.mk_function_type(&[qtv], fapp)
    }

    /// The curried application of `children[0]` to the rest.
    pub(crate) fn mk_apply_curried(&mut self, children: &[Term]) -> Term {
        let mut curr = children[0];
        for &c in &children[1..] {
            curr = self.store.mk_apply(curr, c);
        }
        curr
    }

    /// `mk_apply_curried` for three or more children, a single `APPLY`
    /// otherwise.
    fn mk_apply_plain(&mut self, children: &[Term]) -> Term {
        if children.len() > 2 {
            self.mk_apply_curried(children)
        } else {
            self.store.mk(Kind::APPLY, children)
        }
    }

    /// Builds the term of kind `k` with the given children, after
    /// desugaring and evaluation. For `APPLY`, `children[0]` is the head.
    pub fn mk_expr(&mut self, k: Kind, children: &[Term]) -> Term {
        match k {
            Kind::Node(NodeKind::Apply) if !children.is_empty() => {
                if let Some(t) = self.mk_apply_expr(children) {
                    return t;
                }
            }
            Kind::Eval(op) => {
                // (eo::add t1 t2 t3) is (eo::add (eo::add t1 t2) t3)
                if op.is_nary() && children.len() > 2 {
                    let mut curr = self.mk_expr(k, &children[..2]);
                    for &c in &children[2..] {
                        curr = self.mk_expr(k, &[curr, c]);
                    }
                    return curr;
                }
                // with the wrong arity, build the term; typing rejects it
                if Checker::check_arity(k, children.len(), None) {
                    return self.evaluate_literal_op(op, children);
                }
                let msg = format!(
                    "Wrong number of arguments when applying literal op {}, {} arguments",
                    k,
                    children.len()
                );
                self.warn(&msg);
            }
            Kind::Node(NodeKind::AsReturn) => {
                // (as nil (List Int)) is nil applied to the opaque argument
                if children.len() == 2 {
                    let ck = self.attribute_kind(children[0]);
                    if ck == Attr::AmbDatatypeConstructor || ck == Attr::Amb {
                        return self.mk_expr(Kind::APPLY_OPAQUE, children);
                    }
                }
                // other uses of `as` are not supported: the bogus AS_RETURN
                // term built below does not type check
            }
            Kind::Node(NodeKind::As) => {
                if children.len() == 2
                    && let Some(t) = self.mk_as_expr(children)
                {
                    return t;
                }
            }
            _ => {}
        }
        self.store.mk(k, children)
    }

    /// The `APPLY` case of [`Checker::mk_expr`]. Returns `None` to build the
    /// plain n-ary `APPLY` term.
    fn mk_apply_expr(&mut self, children: &[Term]) -> Option<Term> {
        let hd = children[0];
        if let Some(ai) = self.app_info(hd) {
            if let Some(kind) = ai.kind {
                if kind == Kind::FUNCTION_TYPE {
                    // function types from the parser are nested here
                    let n = children.len();
                    let args = if n >= 2 { &children[1..n - 1] } else { &[][..] };
                    return Some(self.mk_function_type(args, children[n - 1]));
                } else if kind == Kind::APPLY {
                    // (_ f ...) drops the `_` and does not desugar
                    return Some(self.mk_apply_plain(&children[1..]));
                }
                // another builtin operator, which may evaluate
                return Some(self.mk_expr(kind, &children[1..]));
            }
            let (attr, cons, overloaded) = (ai.attr, ai.cons, ai.overloaded);
            if overloaded {
                let name = ai.overload_name.clone();
                // A symbol stays marked as overloaded after the scope of its
                // overloads ends; nothing is found for it then.
                let ov = self.overloads.get(&name).cloned().unwrap_or_default();
                if let Some(ret) = self.get_overload_internal(&ov, children, None, true) {
                    return Some(ret);
                }
                let msg = format!(
                    "No overload found when constructing application {}",
                    self.show_list(children, ", ")
                );
                self.warn(&msg);
            }
            // The constructor term may depend on the arguments: applying
            // bvor to `a` of type (BitVec 4) gives the nil terminator #b0000.
            let cons_term = self.compute_constructor_term(attr, cons, children);
            if let Some(ret) = self.mk_apply_attr(attr, cons, children, cons_term) {
                return Some(ret);
            }
        }
        let hk = self.store.kind(hd);
        if hk == Kind::LAMBDA {
            // a macro applied to the right number of arguments is reduced
            if let Some(ret) = self.mk_beta_reduce(children) {
                return Some(ret);
            }
            let msg = format!("Wrong number of arguments when applying {}", self.show(hd));
            self.warn(&msg);
        } else if hk == Kind::PROGRAM_CONST {
            // Programs without a definition yet stay unevaluated: this is the
            // case for the patterns of the program's own cases.
            if self.attribute_kind(hd) != Attr::None {
                let nparams = self
                    .get_type(hd, None)
                    .map_or(0, |t| self.store.num_children(t));
                if nparams == children.len() {
                    let mut ctx = Ctx::new();
                    if let Some(e) = self.evaluate_program_internal(children, &mut ctx) {
                        return Some(self.evaluate(e, &ctx));
                    }
                } else {
                    let msg = format!(
                        "Wrong number of arguments when applying program {}, {} arguments \
                         expected, got {}",
                        self.show(hd),
                        nparams,
                        children.len()
                    );
                    self.warn(&msg);
                }
            }
        }
        // Functions take one argument at a time. Programs and proof rules do
        // not: their types are not nested.
        if children.len() > 2 && hk != Kind::PROGRAM_CONST && hk != Kind::PROOF_RULE {
            return Some(self.mk_apply_curried(children));
        }
        None
    }

    /// `(eo::as t T)`: picks the overload of `t` that has type `T`.
    fn mk_as_expr(&mut self, children: &[Term]) -> Option<Term> {
        let (arg_types, ret_type) = self.get_function_type(children[1]);
        // stand-ins for arguments of the given types
        let mut dummy = vec![children[1]];
        for t in arg_types {
            dummy.push(self.mk_symbol(SymbolKind::Const, "tmp", t));
        }
        let overloads = match self.app_info(children[0]) {
            Some(ai) if ai.overloaded => self
                .overloads
                .get(&ai.overload_name)
                .cloned()
                .unwrap_or_default(),
            _ => vec![children[0]],
        };
        self.get_overload_internal(&overloads, &dummy, Some(ret_type), false)
    }

    /// Builds `(children[0] children[1..])` as the head's attribute asks.
    /// Returns `None` when the attribute does not change how the
    /// application is built.
    fn mk_apply_attr(
        &mut self,
        attr: Attr,
        attr_cons: Option<Term>,
        vchildren: &[Term],
        cons_term: Option<Term>,
    ) -> Option<Term> {
        let hd = vchildren[0];
        let nchild = vchildren.len();
        match attr {
            Attr::LeftAssoc
            | Attr::RightAssoc
            | Attr::LeftAssocNil
            | Attr::RightAssocNil
            | Attr::RightAssocNsNil
            | Attr::LeftAssocNsNil => {
                if nchild < 2 {
                    // Applied to nothing, e.g. when a pairwise or chainable
                    // operator has one argument: (distinct t) is true.
                    return cons_term;
                }
                let is_left = matches!(
                    attr,
                    Attr::LeftAssoc | Attr::LeftAssocNil | Attr::LeftAssocNsNil
                );
                let is_ns_nil = matches!(attr, Attr::RightAssocNsNil | Attr::LeftAssocNsNil);
                let is_nil = attr.is_list_nil();
                let at = |i: usize| vchildren[if is_left { i } else { nchild - i }];
                let mut i = 1;
                let mut curr = at(i);
                let mut nlist_terms = 0;
                if is_nil && self.attribute_kind(curr) != Attr::List {
                    // The last term is not a list variable, so the nil
                    // terminator comes after it.
                    curr = match cons_term {
                        Some(c) => c,
                        None => {
                            // The terminator could not be inferred, likely
                            // because the argument is not ground. The
                            // placeholder (eo::nil f (eo::typeof t1))
                            // evaluates to it once t1 is instantiated.
                            let typ = self
                                .store
                                .mk(Kind::Eval(pathos_term::EvalOp::TypeOf), &[vchildren[1]]);
                            self.store
                                .mk(Kind::Eval(pathos_term::EvalOp::Nil), &[hd, typ])
                        }
                    };
                    i -= 1;
                }
                i += 1;
                while i < nchild {
                    let next = at(i);
                    let cc = if is_left {
                        [hd, curr, next]
                    } else {
                        [hd, next, curr]
                    };
                    // a list variable is concatenated, not consed
                    if is_nil && self.attribute_kind(next) == Attr::List {
                        curr = self
                            .store
                            .mk(Kind::Eval(pathos_term::EvalOp::ListConcat), &cc);
                    } else {
                        nlist_terms += 1;
                        curr = self.mk_apply_curried(&cc);
                    }
                    i += 1;
                }
                if is_ns_nil && nlist_terms < 2 {
                    // A list of one element stands for the element. The
                    // arguments may be ground, so this may evaluate at once.
                    return Some(self.mk_expr(
                        Kind::Eval(pathos_term::EvalOp::ListSingletonElim),
                        &[hd, curr],
                    ));
                }
                Some(curr)
            }
            Attr::Chainable | Attr::Pairwise => {
                // Without a constructor term (the conjunction to chain
                // with), Ethos goes on with its null expression.
                let mut cchildren = vec![cons_term.unwrap_or(self.store.mk_null())];
                if attr == Attr::Chainable {
                    for i in 1..nchild.saturating_sub(1) {
                        let app = self.mk_apply_curried(&[hd, vchildren[i], vchildren[i + 1]]);
                        cchildren.push(app);
                    }
                } else {
                    for i in 1..nchild.saturating_sub(1) {
                        for j in i + 1..nchild {
                            let app = self.mk_apply_curried(&[hd, vchildren[i], vchildren[j]]);
                            cchildren.push(app);
                        }
                    }
                }
                if cchildren.len() == 2 {
                    // nothing to chain
                    return Some(cchildren[1]);
                }
                Some(self.mk_expr(Kind::APPLY, &cchildren))
            }
            Attr::ArgList => {
                // A single argument marked :list is the argument list.
                let arg_list = if nchild == 2 && self.attribute_kind(vchildren[1]) == Attr::List {
                    vchildren[1]
                } else {
                    let mut cchildren = vec![cons_term.unwrap_or(self.store.mk_null())];
                    cchildren.extend_from_slice(&vchildren[1..]);
                    self.mk_expr(Kind::APPLY, &cchildren)
                };
                Some(self.store.mk_apply(hd, arg_list))
            }
            Attr::Opaque => {
                // the number of opaque arguments is the attribute's term
                let nargs = attr_cons
                    .and_then(|c| self.store.lit(c))
                    .and_then(|l| match l {
                        pathos_term::Lit::Numeral(i) if i.fits_u32() => Some(i.to_u32() as usize),
                        _ => None,
                    })?;
                if nargs >= nchild {
                    let msg = format!(
                        "Too few arguments when applying opaque symbol {}",
                        self.show(hd)
                    );
                    self.warn(&msg);
                    return None;
                }
                // APPLY_OPAQUE is not curried
                let op = self.store.mk(Kind::APPLY_OPAQUE, &vchildren[..1 + nargs]);
                if nargs + 1 == nchild {
                    return Some(op);
                }
                let mut rchildren = vec![op];
                rchildren.extend_from_slice(&vchildren[1 + nargs..]);
                Some(self.mk_apply_plain(&rchildren))
            }
            _ => None,
        }
    }

    /// Reduces the application of a macro (a `LAMBDA` term) to arguments.
    /// Returns `None` if the number of arguments is wrong.
    fn mk_beta_reduce(&mut self, children: &[Term]) -> Option<Term> {
        let hd = children[0];
        let vars = self.store.children(self.store.child(hd, 0)).to_vec();
        if vars.len() != children.len() - 1 {
            return None;
        }
        let mut ctx = Ctx::new();
        for (v, &c) in vars.iter().zip(&children[1..]) {
            ctx.insert(*v, c);
        }
        let body = self.store.child(hd, 1);
        Some(self.evaluate(body, &ctx))
    }

    /// Finds which of `overloads` can be applied in `children`, whose first
    /// element stands for the head. The last one bound is tried first. With
    /// `ret_type`, the application must have that type. Returns the
    /// application if `ret_apply`, the chosen overload otherwise.
    fn get_overload_internal(
        &mut self,
        overloads: &[Term],
        children: &[Term],
        ret_type: Option<Term>,
        ret_apply: bool,
    ) -> Option<Term> {
        let mut vchildren = children.to_vec();
        for &hd in overloads.iter().rev() {
            vchildren[0] = hd;
            let mut x = None;
            if let Some(ai) = self.app_info(hd) {
                let (attr, cons) = (ai.attr, ai.cons);
                let cons_term = self.compute_constructor_term(attr, cons, children);
                x = self.mk_apply_attr(attr, cons, &vchildren, cons_term);
            }
            let x = match x {
                Some(x) => x,
                None => self.mk_apply_plain(&vchildren),
            };
            let t = self.get_type(x, None);
            // well typed, and of the required type if there is one
            if t.is_some() && (ret_type.is_none() || ret_type == t) {
                // an overloaded macro is reduced, as in mk_expr
                if ret_apply
                    && self.store.kind(hd) == Kind::LAMBDA
                    && let Some(ret) = self.mk_beta_reduce(&vchildren)
                {
                    return Some(ret);
                }
                return Some(if ret_apply { x } else { hd });
            }
        }
        None
    }

    /// Splits `(-> T1 ... Tn T)` into its argument types and its return
    /// type, looking through `eo::requires` in return positions.
    pub fn get_function_type(&self, t: Term) -> (Vec<Term>, Term) {
        let mut et = t;
        let mut args = Vec::new();
        while self.store.kind(et) == Kind::FUNCTION_TYPE && self.store.num_children(et) > 0 {
            let ch = self.store.children(et);
            let n = ch.len();
            args.extend_from_slice(&ch[..n - 1]);
            et = ch[n - 1];
            while self.store.kind(et) == Kind::Eval(pathos_term::EvalOp::Requires)
                && self.store.num_children(et) == 3
            {
                et = self.store.child(et, 2);
            }
        }
        (args, et)
    }

    /// The parameters that occur in the terms, each once. The order is that
    /// of Ethos's traversal: later terms and later children first.
    pub fn get_variables(&self, es: &[Term]) -> Vec<Term> {
        let mut ret = Vec::new();
        let mut visited = std::collections::HashSet::new();
        let mut to_visit = es.to_vec();
        while let Some(cur) = to_visit.pop() {
            if self.store.is_ground(cur) || !visited.insert(cur) {
                continue;
            }
            if self.store.kind(cur) == Kind::PARAM {
                ret.push(cur);
                continue;
            }
            to_visit.extend_from_slice(self.store.children(cur));
        }
        ret
    }

    /// Whether `var`, a parameter, occurs in `e`.
    pub fn has_variable(&self, e: Term, var: Term) -> bool {
        let mut visited = std::collections::HashSet::new();
        let mut to_visit = vec![e];
        while let Some(cur) = to_visit.pop() {
            if self.store.is_ground(cur) || !visited.insert(cur) {
                continue;
            }
            if cur == var {
                return true;
            }
            to_visit.extend_from_slice(self.store.children(cur));
        }
        false
    }
}
