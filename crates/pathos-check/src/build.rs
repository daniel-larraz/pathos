//! Building terms (`State::mkExpr` and its helpers in Ethos's `state.cpp`).
//!
//! [`Checker::mk_expr`] is what the parser calls for `(f t1 ... tn)`. It
//! applies the desugaring that the head's attributes ask for (associativity,
//! chaining, opaque arguments, overloads), reduces applications of macros and
//! programs, and evaluates `eo::` operators.

use std::collections::HashSet;

use pathos_term::{EvalOp, Kind, Lit, NodeKind, SymbolKind, Term};

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

use crate::attr::Attr;
use crate::checker::{Checker, Ctx};
#[cfg(verus_keep_ghost)]
use crate::checker::{all_has, keeps};
use crate::eval::{copy_of, push_all};
#[cfg(verus_keep_ghost)]
use crate::eval::{lemma_keeps_twice, use_collections};
#[cfg(verus_keep_ghost)]
use pathos_term::TermStore;

/// The terms from position `from` on. (Verus has no specification of
/// slicing by a range.)
#[cfg_attr(verus_keep_ghost, verus_verify(external_body), verus_spec(r =>
    requires from <= ts@.len(),
    ensures r@ == ts@.subrange(from as int, ts@.len() as int),
))]
#[inline(always)]
pub(crate) fn rest_of(ts: &[Term], from: usize) -> &[Term] {
    &ts[from..]
}

/// The terms from position `from` up to `to`, which is not included.
#[cfg_attr(verus_keep_ghost, verus_verify(external_body), verus_spec(r =>
    requires from <= to <= ts@.len(),
    ensures r@ == ts@.subrange(from as int, to as int),
))]
#[inline(always)]
pub(crate) fn part_of(ts: &[Term], from: usize, to: usize) -> &[Term] {
    &ts[from..to]
}

/// The list with `head` before the terms of `rest`.
#[cfg_attr(verus_keep_ghost, verus_verify, verus_spec(r =>
    ensures r@ == seq![head] + rest@,
))]
fn prepend(head: Term, rest: &[Term]) -> Vec<Term> {
    // (Verus has no `vec!`)
    #[allow(clippy::vec_init_then_push)]
    let mut list = {
        let mut list = Vec::new();
        list.push(head);
        list
    };
    push_all(&mut list, rest);
    list
}

// The texts of the warnings. Trusted: formatting and printing are not
// verified.

#[cfg_attr(verus_keep_ghost, verus_verify(external_body))]
fn msg_literal_args(k: Kind, given: usize) -> String {
    format!("Wrong number of arguments when applying literal op {k}, {given} arguments")
}

impl Checker {
    /// A type constant of the given arity: `Type`, or
    /// `(-> Type ... Type Type)`.
    pub fn mk_type_constant(&mut self, name: &str, arity: usize) -> Term {
        let ty = self.mk_type();
        let args = vec![ty; arity];
        let t = self.mk_function_type(&args, ty);
        self.mk_symbol(SymbolKind::Const, name, t)
    }

    /// The variable `(eo::var "name" type)`.
    pub fn get_bound_var(&mut self, name: &str, ty: Term) -> Term {
        let ename = self.mk_string_literal(name);
        self.mk_expr(Kind::VARIABLE, &[ename, ty])
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
}

// Written for Verus, which follows a loop over indices without a
// specification of the iterator, does not take `let` in a condition with
// `&&` or as the condition of a `while`, nor a guard in a `match`, and has
// no `vec!` and no specification of `saturating_sub`.
#[allow(
    clippy::needless_range_loop,
    clippy::collapsible_if,
    clippy::collapsible_match,
    clippy::while_let_loop,
    clippy::manual_map,
    clippy::vec_init_then_push,
    clippy::implicit_saturating_sub,
    clippy::question_mark
)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
impl Checker {
    #[cfg_attr(verus_keep_ghost, verus_verify(external_body))]
    fn msg_no_overload(&self, children: &[Term]) -> String {
        format!(
            "No overload found when constructing application {}",
            self.show_list(children, ", ")
        )
    }

    #[cfg_attr(verus_keep_ghost, verus_verify(external_body))]
    fn msg_macro_args(&self, hd: Term) -> String {
        format!("Wrong number of arguments when applying {}", self.show(hd))
    }

    #[cfg_attr(verus_keep_ghost, verus_verify(external_body))]
    fn msg_program_args(&self, hd: Term, expected: usize, given: usize) -> String {
        format!(
            "Wrong number of arguments when applying program {}, {} arguments expected, got {}",
            self.show(hd),
            expected,
            given
        )
    }

    #[cfg_attr(verus_keep_ghost, verus_verify(external_body))]
    fn msg_opaque_args(&self, hd: Term) -> String {
        format!(
            "Too few arguments when applying opaque symbol {}",
            self.show(hd)
        )
    }

    /// `(-> args... ret)`, nested to the right; `ret` itself without `args`.
    #[cfg_attr(verus_keep_ghost, verifier::loop_isolation(false), verus_spec(r =>
        requires old(self).wf(), old(self).has_all(args@), old(self).has(ret),
        ensures final(self).wf(), final(self).keeps(old(self)), final(self).has(r),
    ))]
    pub fn mk_function_type(&mut self, args: &[Term], ret: Term) -> Term {
        proof_decl! { let ghost start = *self; }
        let mut curr = ret;
        let mut i = args.len();
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant i <= args@.len(), self.wf(), self.keeps(&start), self.has(curr),
            decreases i,
        ))]
        while i > 0 {
            i -= 1;
            proof! { assert(start.has(args@[i as int])); }
            proof_decl! { let ghost before = *self; }
            curr = self.mk_term(Kind::FUNCTION_TYPE, &[args[i], curr]);
            proof! { lemma_keeps_twice(&self.store, &before.store, &start.store); }
        }
        curr
    }

    /// The type of a program taking `args` and returning `ret`. Unlike
    /// function types, these are not nested.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires old(self).wf(), old(self).has_all(args@), old(self).has(ret),
        ensures final(self).wf(), final(self).keeps(old(self)), final(self).has(r),
    ))]
    pub fn mk_program_type(&mut self, args: &[Term], ret: Term) -> Term {
        let mut children = copy_of(args);
        children.push(ret);
        self.mk_term(Kind::PROGRAM_TYPE, &children)
    }

    /// `(eo::requires a1 a2 ret)`, which may evaluate at once.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires old(self).wf(), old(self).has(a1), old(self).has(a2), old(self).has(ret),
        ensures final(self).wf(), final(self).keeps(old(self)), final(self).has(r),
    ))]
    pub fn mk_requires(&mut self, a1: Term, a2: Term, ret: Term) -> Term {
        self.mk_expr(Kind::Eval(EvalOp::Requires), &[a1, a2, ret])
    }

    /// Wraps `ret` in one `eo::requires` for each pair in `pairs`.
    #[cfg_attr(verus_keep_ghost, verifier::loop_isolation(false), verus_spec(r =>
        requires
            old(self).wf(),
            old(self).has_all(pairs@),
            old(self).has(ret),
            // each is a pair
            old(self).has_pairs(pairs@),
        ensures final(self).wf(), final(self).keeps(old(self)), final(self).has(r),
    ))]
    pub fn mk_requires_list(&mut self, pairs: &[Term], ret: Term) -> Term {
        proof_decl! { let ghost start = *self; }
        let mut curr = ret;
        let mut i = pairs.len();
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant i <= pairs@.len(), self.wf(), self.keeps(&start), self.has(curr),
            decreases i,
        ))]
        while i > 0 {
            i -= 1;
            let p = pairs[i];
            proof! { assert(start.has(pairs@[i as int])); }
            let (a, b) = (self.store.child(p, 0), self.store.child(p, 1));
            proof_decl! { let ghost before = *self; }
            curr = self.mk_requires(a, b, curr);
            proof! { lemma_keeps_twice(&self.store, &before.store, &start.store); }
        }
        curr
    }

    /// `(eo::pf proven)`.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires old(self).wf(), old(self).has(proven),
        ensures final(self).wf(), final(self).keeps(old(self)), final(self).has(r),
    ))]
    pub fn mk_proof(&mut self, proven: Term) -> Term {
        self.mk_term(Kind::PROOF, &[proven])
    }

    /// `(eo::quote t)`, for a parameter `t`.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires old(self).wf(), old(self).has(t),
        ensures final(self).wf(), final(self).keeps(old(self)), final(self).has(r),
    ))]
    pub fn mk_quote_type(&mut self, t: Term) -> Term {
        self.mk_term(Kind::QUOTE_TYPE, &[t])
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires old(self).wf(), old(self).has(t1), old(self).has(t2),
        ensures final(self).wf(), final(self).keeps(old(self)), final(self).has(r),
    ))]
    pub fn mk_pair(&mut self, t1: Term, t2: Term) -> Term {
        self.mk_term(Kind::TUPLE, &[t1, t2])
    }

    /// `(eo::_ (eo::tuple params...) hd)`.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires old(self).wf(), old(self).has(hd), old(self).has_all(params@),
        ensures final(self).wf(), final(self).keeps(old(self)), final(self).has(r),
    ))]
    pub fn mk_parameterized(&mut self, hd: Term, params: &[Term]) -> Term {
        let tuple = self.mk_expr(Kind::TUPLE, params);
        self.mk_expr(Kind::PARAMETERIZED, &[tuple, hd])
    }

    /// `(eo::List::cons args...)`, or `eo::List::nil` without `args`.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires old(self).wf(), old(self).has_all(args@),
        ensures final(self).wf(), final(self).keeps(old(self)), final(self).has(r),
    ))]
    #[cfg_attr(verus_keep_ghost, verifier::exec_allows_no_decreases_clause)]
    pub fn mk_list(&mut self, args: &[Term]) -> Term {
        if args.is_empty() {
            return self.list_nil;
        }
        let largs = prepend(self.list_cons, args);
        self.mk_expr(Kind::APPLY, &largs)
    }

    /// The list of variables of a binder application, built with the
    /// binder's list constructor.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires old(self).wf(), old(self).has_all(vs@),
        ensures
            final(self).wf(),
            final(self).keeps(old(self)),
            r matches Some(t) ==> final(self).has(t),
    ))]
    pub fn mk_binder_list(&mut self, binder: Term, vs: &[Term]) -> Option<Term> {
        let cons = self.attribute_term(binder)?;
        let vlist = prepend(cons, vs);
        Some(self.mk_expr(Kind::APPLY, &vlist))
    }

    /// The list of bindings of a let-binder application.
    #[cfg_attr(verus_keep_ghost, verifier::loop_isolation(false), verus_spec(r =>
        requires
            old(self).wf(),
            forall|j: int| 0 <= j < lls@.len() ==> old(self).has((#[trigger] lls@[j]).0) && old(self).has(lls@[j].1),
        ensures
            final(self).wf(),
            final(self).keeps(old(self)),
            r matches Some(t) ==> final(self).has(t),
    ))]
    pub fn mk_let_binder_list(&mut self, binder: Term, lls: &[(Term, Term)]) -> Option<Term> {
        proof_decl! { let ghost start = *self; }
        let cons = self.attribute_term(binder)?;
        // The constructor term is the tuple (pair constructor, list
        // constructor). Ethos asserts that only in debug builds and takes
        // the first two children of whatever term it is: for a
        // parameterized binder, of the term that pairs the parameters with
        // the tuple. With fewer than two children it reads past their end.
        if self.store.num_children(cons) < 2 {
            return None;
        }
        let (pair_cons, list_cons) = (self.store.child(cons, 0), self.store.child(cons, 1));
        let mut vlist = Vec::new();
        vlist.push(list_cons);
        #[cfg_attr(verus_keep_ghost, verus_spec(invariant
            self.wf(),
            self.keeps(&start),
            self.has(pair_cons),
            self.has_all(vlist@),
        ))]
        for i in 0..lls.len() {
            let (v, t) = lls[i];
            proof! { assert(start.has(lls@[i as int].0) && start.has(lls@[i as int].1)); }
            proof_decl! { let ghost before = *self; let ghost list = vlist@; }
            let binding = self.mk_expr(Kind::APPLY, &[pair_cons, v, t]);
            vlist.push(binding);
            proof! {
                lemma_keeps_twice(&self.store, &before.store, &start.store);
                assert forall|j: int| 0 <= j < vlist@.len() implies self.has(#[trigger] vlist@[j]) by {
                    if j < list.len() {
                        assert(before.has(list[j]));
                    }
                }
            }
        }
        Some(self.mk_expr(Kind::APPLY, &vlist))
    }

    /// The curried application of `children[0]` to the rest.
    #[cfg_attr(verus_keep_ghost, verifier::loop_isolation(false), verus_spec(r =>
        requires
            old(self).wf(),
            old(self).has_all(children@),
            // the first is the head
            children@.len() >= 1,
        ensures final(self).wf(), final(self).keeps(old(self)), final(self).has(r),
    ))]
    pub(crate) fn mk_apply_curried(&mut self, children: &[Term]) -> Term {
        proof_decl! { let ghost start = *self; }
        let mut curr = children[0];
        #[cfg_attr(verus_keep_ghost, verus_spec(invariant
            self.wf(), self.keeps(&start), self.has(curr),
        ))]
        for i in 1..children.len() {
            proof! { assert(start.has(children@[i as int])); }
            proof_decl! { let ghost before = *self; }
            curr = self.mk_app(curr, children[i]);
            proof! { lemma_keeps_twice(&self.store, &before.store, &start.store); }
        }
        curr
    }

    /// `mk_apply_curried` for three or more children, a single `APPLY`
    /// otherwise.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires old(self).wf(), old(self).has_all(children@),
        ensures final(self).wf(), final(self).keeps(old(self)), final(self).has(r),
    ))]
    fn mk_apply_plain(&mut self, children: &[Term]) -> Term {
        if children.len() > 2 {
            self.mk_apply_curried(children)
        } else {
            self.mk_term(Kind::APPLY, children)
        }
    }

    /// Builds the term of kind `k` with the given children, after
    /// desugaring and evaluation. For `APPLY`, `children[0]` is the head.
    ///
    /// `k` is a compound kind: symbols and literals are not built here.
    #[cfg_attr(verus_keep_ghost, verifier::loop_isolation(false), verus_spec(r =>
        requires old(self).wf(), old(self).has_all(children@), !(k is Symbol) && !(k is Lit),
        ensures final(self).wf(), final(self).keeps(old(self)), final(self).has(r),
    ))]
    #[cfg_attr(verus_keep_ghost, verifier::exec_allows_no_decreases_clause)]
    pub fn mk_expr(&mut self, k: Kind, children: &[Term]) -> Term {
        proof_decl! { let ghost start = *self; }
        match k {
            Kind::Node(NodeKind::Apply) => {
                if !children.is_empty() {
                    if let Some(t) = self.mk_apply_expr(children) {
                        return t;
                    }
                }
            }
            Kind::Eval(op) => {
                // (eo::add t1 t2 t3) is (eo::add (eo::add t1 t2) t3)
                if op.is_nary() && children.len() > 2 {
                    proof! { lemma_part(&self.store, children@, 0, 2); }
                    let mut curr = self.mk_expr(k, part_of(children, 0, 2));
                    #[cfg_attr(verus_keep_ghost, verus_spec(invariant
                        self.wf(), self.keeps(&start), self.has(curr),
                    ))]
                    for i in 2..children.len() {
                        proof! { assert(start.has(children@[i as int])); }
                        proof_decl! { let ghost before = *self; }
                        curr = self.mk_expr(k, &[curr, children[i]]);
                        proof! { lemma_keeps_twice(&self.store, &before.store, &start.store); }
                    }
                    return curr;
                }
                // with the wrong arity, build the term; typing rejects it
                if Checker::check_arity(k, children.len(), None) {
                    return self.evaluate_literal_op(op, children);
                }
                let msg = msg_literal_args(k, children.len());
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
                if children.len() == 2 {
                    if let Some(t) = self.mk_as_expr(children) {
                        return t;
                    }
                }
            }
            _ => {}
        }
        proof! {
            assert forall|j: int| 0 <= j < children@.len() implies self.has(#[trigger] children@[j]) by {
                assert(start.has(children@[j]));
            }
        }
        self.mk_term(k, children)
    }

    /// The `APPLY` case of [`Checker::mk_expr`]. Returns `None` to build the
    /// plain n-ary `APPLY` term.
    #[cfg_attr(verus_keep_ghost, verifier::loop_isolation(false), verus_spec(r =>
        requires
            old(self).wf(),
            old(self).has_all(children@),
            // the first is the head
            children@.len() >= 1,
        ensures
            final(self).wf(),
            final(self).keeps(old(self)),
            r matches Some(t) ==> final(self).has(t),
    ))]
    #[cfg_attr(verus_keep_ghost, verifier::exec_allows_no_decreases_clause)]
    fn mk_apply_expr(&mut self, children: &[Term]) -> Option<Term> {
        proof! {
            use_collections();
            broadcast use vstd::std_specs::btree::group_btree_axioms;
        }
        proof_decl! { let ghost start = *self; }
        let hd = children[0];
        let n = children.len();
        // what is known of the head: the kind its applications build, or
        // its attribute, its term and the terms its name is bound to
        let known = match self.app_info(hd) {
            Some(ai) => {
                let ov = if ai.overloaded {
                    // A symbol stays marked as overloaded after the scope
                    // of its overloads ends; nothing is found for it then.
                    Some(self.overloads_of(&ai.overload_name))
                } else {
                    None
                };
                Some((ai.kind, ai.attr, ai.cons, ov))
            }
            None => None,
        };
        if let Some((kind, attr, cons, ov)) = known {
            if let Some(kind) = kind {
                if kind == Kind::FUNCTION_TYPE {
                    // function types from the parser are nested here
                    let args = if n >= 2 {
                        proof! { lemma_part(&self.store, children@, 1, n as int - 1); }
                        part_of(children, 1, n - 1)
                    } else {
                        proof! { lemma_part(&self.store, children@, 0, 0); }
                        part_of(children, 0, 0)
                    };
                    return Some(self.mk_function_type(args, children[n - 1]));
                }
                proof! { lemma_part(&self.store, children@, 1, n as int); }
                if kind == Kind::APPLY {
                    // (_ f ...) drops the `_` and does not desugar
                    return Some(self.mk_apply_plain(rest_of(children, 1)));
                }
                // another builtin operator, which may evaluate
                return Some(self.mk_expr(kind, rest_of(children, 1)));
            }
            if let Some(ov) = ov {
                if let Some(ret) = self.get_overload_internal(&ov, children, None, true) {
                    return Some(ret);
                }
                let msg = self.msg_no_overload(children);
                self.warn(&msg);
            }
            proof! { lemma_all_kept(&self.store, &start.store, children@); }
            // The constructor term may depend on the arguments: applying
            // bvor to `a` of type (BitVec 4) gives the nil terminator #b0000.
            let cons_term = self.compute_constructor_term(attr, cons, children);
            proof! { lemma_all_kept(&self.store, &start.store, children@); }
            if let Some(ret) = self.mk_apply_attr(attr, cons, children, cons_term) {
                return Some(ret);
            }
        }
        proof! { lemma_all_kept(&self.store, &start.store, children@); }
        let hk = self.store.kind(hd);
        if hk == Kind::LAMBDA {
            // a macro applied to the right number of arguments is reduced
            if let Some(ret) = self.mk_beta_reduce(children) {
                return Some(ret);
            }
            let msg = self.msg_macro_args(hd);
            self.warn(&msg);
        } else if hk == Kind::PROGRAM_CONST {
            // Programs without a definition yet stay unevaluated: this is the
            // case for the patterns of the program's own cases.
            if self.attribute_kind(hd) != Attr::None {
                let nparams = match self.get_type(hd, None) {
                    Some(t) => self.store.num_children(t),
                    None => 0,
                };
                proof! { lemma_all_kept(&self.store, &start.store, children@); }
                if nparams == n {
                    let mut ctx = Ctx::new();
                    if let Some(e) = self.evaluate_program_internal(children, &mut ctx) {
                        return Some(self.evaluate(e, &ctx));
                    }
                } else {
                    let msg = self.msg_program_args(hd, nparams, n);
                    self.warn(&msg);
                }
            }
        }
        proof! { lemma_all_kept(&self.store, &start.store, children@); }
        // Functions take one argument at a time. Programs and proof rules do
        // not: their types are not nested.
        if n > 2 && hk != Kind::PROGRAM_CONST && hk != Kind::PROOF_RULE {
            return Some(self.mk_apply_curried(children));
        }
        None
    }

    /// `(eo::as t T)`: picks the overload of `t` that has type `T`.
    #[cfg_attr(verus_keep_ghost, verifier::loop_isolation(false), verus_spec(r =>
        requires old(self).wf(), old(self).has_all(children@), children@.len() == 2,
        ensures
            final(self).wf(),
            final(self).keeps(old(self)),
            r matches Some(t) ==> final(self).has(t),
    ))]
    #[cfg_attr(verus_keep_ghost, verifier::exec_allows_no_decreases_clause)]
    fn mk_as_expr(&mut self, children: &[Term]) -> Option<Term> {
        proof_decl! { let ghost start = *self; }
        let (arg_types, ret_type) = self.get_function_type(children[1]);
        // stand-ins for arguments of the given types
        let mut dummy = Vec::new();
        dummy.push(children[1]);
        #[cfg_attr(verus_keep_ghost, verus_spec(invariant
            self.wf(), self.keeps(&start), self.has_all(dummy@), dummy@.len() >= 1,
        ))]
        for i in 0..arg_types.len() {
            proof! { assert(start.has(arg_types@[i as int])); }
            proof_decl! { let ghost before = *self; let ghost list = dummy@; }
            let tmp = self.mk_symbol(SymbolKind::Const, "tmp", arg_types[i]);
            dummy.push(tmp);
            proof! {
                lemma_keeps_twice(&self.store, &before.store, &start.store);
                assert forall|j: int| 0 <= j < dummy@.len() implies self.has(#[trigger] dummy@[j]) by {
                    if j < list.len() {
                        assert(before.has(list[j]));
                    }
                }
            }
        }
        let named = match self.app_info(children[0]) {
            Some(ai) => {
                if ai.overloaded {
                    Some(self.overloads_of(&ai.overload_name))
                } else {
                    None
                }
            }
            None => None,
        };
        let overloads = match named {
            Some(ov) => ov,
            None => {
                let mut one = Vec::new();
                one.push(children[0]);
                one
            }
        };
        self.get_overload_internal(&overloads, &dummy, Some(ret_type), false)
    }

    /// Builds `(children[0] children[1..])` as the head's attribute asks.
    /// Returns `None` when the attribute does not change how the
    /// application is built.
    #[cfg_attr(verus_keep_ghost, verifier::loop_isolation(false), verus_spec(r =>
        requires
            old(self).wf(),
            old(self).has_all(vchildren@),
            // the first is the head
            vchildren@.len() >= 1,
            attr_cons matches Some(c) ==> old(self).has(c),
            cons_term matches Some(c) ==> old(self).has(c),
        ensures
            final(self).wf(),
            final(self).keeps(old(self)),
            r matches Some(t) ==> final(self).has(t),
    ))]
    #[cfg_attr(verus_keep_ghost, verifier::exec_allows_no_decreases_clause)]
    fn mk_apply_attr(
        &mut self,
        attr: Attr,
        attr_cons: Option<Term>,
        vchildren: &[Term],
        cons_term: Option<Term>,
    ) -> Option<Term> {
        proof_decl! { let ghost start = *self; }
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
                // the arguments from the left, or from the right
                let mut i: usize = 1;
                let mut curr = vchildren[if is_left { i } else { nchild - i }];
                let mut nlist_terms: usize = 0;
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
                            let typ = self.mk_term(Kind::Eval(EvalOp::TypeOf), &[vchildren[1]]);
                            self.mk_term(Kind::Eval(EvalOp::Nil), &[hd, typ])
                        }
                    };
                    i -= 1;
                }
                i += 1;
                #[cfg_attr(verus_keep_ghost, verus_spec(
                    invariant
                        1 <= i,
                        nlist_terms <= i,
                        self.wf(),
                        self.keeps(&start),
                        self.has(curr),
                    decreases nchild - i,
                ))]
                while i < nchild {
                    let next = vchildren[if is_left { i } else { nchild - i }];
                    proof! { assert(start.has(hd) && start.has(next)); }
                    let cc = if is_left {
                        [hd, curr, next]
                    } else {
                        [hd, next, curr]
                    };
                    proof_decl! { let ghost before = *self; }
                    // a list variable is concatenated, not consed
                    if is_nil && self.attribute_kind(next) == Attr::List {
                        curr = self.mk_term(Kind::Eval(EvalOp::ListConcat), &cc);
                    } else {
                        nlist_terms += 1;
                        curr = self.mk_apply_curried(&cc);
                    }
                    proof! { lemma_keeps_twice(&self.store, &before.store, &start.store); }
                    i += 1;
                }
                if is_ns_nil && nlist_terms < 2 {
                    // A list of one element stands for the element. The
                    // arguments may be ground, so this may evaluate at once.
                    return Some(self.mk_expr(Kind::Eval(EvalOp::ListSingletonElim), &[hd, curr]));
                }
                Some(curr)
            }
            Attr::Chainable | Attr::Pairwise => {
                // Without a constructor term (the conjunction to chain
                // with), Ethos goes on with its null expression.
                let first = match cons_term {
                    Some(c) => c,
                    None => self.store.mk_null(),
                };
                let mut cchildren = Vec::new();
                cchildren.push(first);
                // the last argument has none after it
                let last = if nchild >= 1 { nchild - 1 } else { 0 };
                if attr == Attr::Chainable {
                    #[cfg_attr(verus_keep_ghost, verus_spec(invariant
                        self.wf(), self.keeps(&start), self.has_all(cchildren@), cchildren@.len() >= 1,
                    ))]
                    for i in 1..last {
                        proof! { assert(start.has(hd) && start.has(vchildren@[i as int]) && start.has(vchildren@[i + 1])); }
                        proof_decl! { let ghost before = *self; let ghost list = cchildren@; }
                        let app = self.mk_apply_curried(&[hd, vchildren[i], vchildren[i + 1]]);
                        cchildren.push(app);
                        proof! {
                            lemma_keeps_twice(&self.store, &before.store, &start.store);
                            lemma_pushed(&self.store, &before.store, list, app);
                        }
                    }
                } else {
                    #[cfg_attr(verus_keep_ghost, verus_spec(invariant
                        self.wf(), self.keeps(&start), self.has_all(cchildren@), cchildren@.len() >= 1,
                    ))]
                    for i in 1..last {
                        #[cfg_attr(verus_keep_ghost, verus_spec(invariant
                            self.wf(), self.keeps(&start), self.has_all(cchildren@), cchildren@.len() >= 1,
                        ))]
                        for j in i + 1..nchild {
                            proof! { assert(start.has(hd) && start.has(vchildren@[i as int]) && start.has(vchildren@[j as int])); }
                            proof_decl! { let ghost before = *self; let ghost list = cchildren@; }
                            let app = self.mk_apply_curried(&[hd, vchildren[i], vchildren[j]]);
                            cchildren.push(app);
                            proof! {
                                lemma_keeps_twice(&self.store, &before.store, &start.store);
                                lemma_pushed(&self.store, &before.store, list, app);
                            }
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
                    let first = match cons_term {
                        Some(c) => c,
                        None => self.store.mk_null(),
                    };
                    proof! { lemma_part(&self.store, vchildren@, 1, nchild as int); }
                    let cchildren = prepend(first, rest_of(vchildren, 1));
                    self.mk_expr(Kind::APPLY, &cchildren)
                };
                Some(self.mk_app(hd, arg_list))
            }
            Attr::Opaque => {
                // the number of opaque arguments is the attribute's term
                let nargs = match attr_cons {
                    Some(c) => match self.store.lit(c) {
                        Some(Lit::Numeral(i)) => {
                            if i.fits_u32() {
                                i.to_u32() as usize
                            } else {
                                return None;
                            }
                        }
                        _ => return None,
                    },
                    None => return None,
                };
                if nargs >= nchild {
                    let msg = self.msg_opaque_args(hd);
                    self.warn(&msg);
                    return None;
                }
                // APPLY_OPAQUE is not curried
                proof! {
                    lemma_part(&self.store, vchildren@, 0, 1 + nargs as int);
                    lemma_part(&self.store, vchildren@, 1 + nargs as int, nchild as int);
                }
                let op = self.mk_term(Kind::APPLY_OPAQUE, part_of(vchildren, 0, 1 + nargs));
                if nargs + 1 == nchild {
                    return Some(op);
                }
                let rchildren = prepend(op, rest_of(vchildren, 1 + nargs));
                proof! { lemma_all_kept(&self.store, &start.store, vchildren@.subrange(1 + nargs as int, nchild as int)); }
                Some(self.mk_apply_plain(&rchildren))
            }
            _ => None,
        }
    }

    /// Reduces the application of a macro (a `LAMBDA` term) to arguments.
    /// Returns `None` if the number of arguments is wrong.
    #[cfg_attr(verus_keep_ghost, verifier::loop_isolation(false), verus_spec(r =>
        requires
            old(self).wf(),
            old(self).has_all(children@),
            // the first is the macro
            children@.len() >= 1,
            old(self).store.kind_of(children@[0].idx()) == Kind::LAMBDA,
        ensures
            final(self).wf(),
            final(self).keeps(old(self)),
            r matches Some(t) ==> final(self).has(t),
    ))]
    #[cfg_attr(verus_keep_ghost, verifier::exec_allows_no_decreases_clause)]
    fn mk_beta_reduce(&mut self, children: &[Term]) -> Option<Term> {
        proof! {
            use_collections();
            broadcast use vstd::std_specs::btree::group_btree_axioms;
        }
        let hd = children[0];
        proof! { self.store.lemma_shape(hd); }
        let vars = copy_of(self.store.children(self.store.child(hd, 0)));
        if vars.len() != children.len() - 1 {
            return None;
        }
        let mut ctx = Ctx::new();
        #[cfg_attr(verus_keep_ghost, verus_spec(invariant self.binds(ctx@),))]
        for i in 0..vars.len() {
            ctx.insert(vars[i], children[i + 1]);
        }
        let body = self.store.child(hd, 1);
        Some(self.evaluate(body, &ctx))
    }

    /// Finds which of `overloads` can be applied in `children`, whose first
    /// element stands for the head. The last one bound is tried first. With
    /// `ret_type`, the application must have that type. Returns the
    /// application if `ret_apply`, the chosen overload otherwise.
    #[cfg_attr(verus_keep_ghost, verifier::loop_isolation(false), verus_spec(r =>
        requires
            old(self).wf(),
            old(self).has_all(overloads@),
            old(self).has_all(children@),
            // the first stands for the head
            children@.len() >= 1,
        ensures
            final(self).wf(),
            final(self).keeps(old(self)),
            r matches Some(t) ==> final(self).has(t),
    ))]
    #[cfg_attr(verus_keep_ghost, verifier::exec_allows_no_decreases_clause)]
    fn get_overload_internal(
        &mut self,
        overloads: &[Term],
        children: &[Term],
        ret_type: Option<Term>,
        ret_apply: bool,
    ) -> Option<Term> {
        proof_decl! { let ghost start = *self; }
        let mut vchildren = copy_of(children);
        let mut next = overloads.len();
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant
                next <= overloads@.len(),
                self.wf(),
                self.keeps(&start),
                self.has_all(vchildren@),
                vchildren@.len() == children@.len(),
            decreases next,
        ))]
        while next > 0 {
            next -= 1;
            let hd = overloads[next];
            proof! {
                assert(start.has(overloads@[next as int]));
                lemma_all_kept(&self.store, &start.store, children@);
            }
            proof_decl! { let ghost list = vchildren@; }
            vchildren[0] = hd;
            proof! {
                assert forall|j: int| 0 <= j < vchildren@.len() implies self.has(#[trigger] vchildren@[j]) by {
                    if j > 0 {
                        assert(self.has(list[j]));
                    }
                }
            }
            proof_decl! { let ghost before = *self; }
            let mut x = None;
            let known = match self.app_info(hd) {
                Some(ai) => Some((ai.attr, ai.cons)),
                None => None,
            };
            if let Some((attr, cons)) = known {
                let cons_term = self.compute_constructor_term(attr, cons, children);
                proof! { lemma_all_kept(&self.store, &before.store, vchildren@); }
                x = self.mk_apply_attr(attr, cons, &vchildren, cons_term);
            }
            proof! { lemma_all_kept(&self.store, &before.store, vchildren@); }
            let x = match x {
                Some(x) => x,
                None => self.mk_apply_plain(&vchildren),
            };
            let t = self.get_type(x, None);
            proof! {
                lemma_keeps_twice(&self.store, &before.store, &start.store);
                lemma_all_kept(&self.store, &before.store, vchildren@);
            }
            // well typed, and of the required type if there is one
            if let Some(t) = t {
                let fits = match ret_type {
                    Some(rt) => rt == t,
                    None => true,
                };
                if fits {
                    // an overloaded macro is reduced, as in mk_expr
                    if ret_apply && self.store.kind(hd) == Kind::LAMBDA {
                        if let Some(ret) = self.mk_beta_reduce(&vchildren) {
                            return Some(ret);
                        }
                    }
                    return Some(if ret_apply { x } else { hd });
                }
            }
        }
        None
    }

    /// Splits `(-> T1 ... Tn T)` into its argument types and its return
    /// type, looking through `eo::requires` in return positions.
    #[cfg_attr(verus_keep_ghost, verifier::loop_isolation(false), verus_spec(r =>
        requires self.wf(), self.has(t),
        ensures self.has_all(r.0@), self.has(r.1),
    ))]
    pub fn get_function_type(&self, t: Term) -> (Vec<Term>, Term) {
        let mut et = t;
        let mut args = Vec::new();
        proof! { Term::lemma_idx_range(t); }
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant self.has(et), self.has_all(args@), 0 < et.idx(),
            decreases et.idx(),
        ))]
        while self.store.kind(et) == Kind::FUNCTION_TYPE && self.store.num_children(et) > 0 {
            proof! { self.store.lemma_children(et); }
            proof_decl! { let ghost top = et; }
            let ch = self.store.children(et);
            let n = ch.len();
            push_all(&mut args, part_of(ch, 0, n - 1));
            et = ch[n - 1];
            #[cfg_attr(verus_keep_ghost, verus_spec(
                invariant self.has(et), 0 < et.idx() < top.idx(),
                decreases et.idx(),
            ))]
            while self.store.kind(et) == Kind::Eval(EvalOp::Requires)
                && self.store.num_children(et) == 3
            {
                proof! { self.store.lemma_children(et); }
                et = self.store.child(et, 2);
            }
        }
        (args, et)
    }

    /// The parameters that occur in the terms, each once. The order is that
    /// of Ethos's traversal: later terms and later children first.
    #[cfg_attr(verus_keep_ghost, verifier::exec_allows_no_decreases_clause, verifier::loop_isolation(false), verus_spec(r =>
        requires self.wf(), self.has_all(es@),
        ensures self.has_all(r@),
    ))]
    pub fn get_variables(&self, es: &[Term]) -> Vec<Term> {
        proof! {
            use_collections();
            broadcast use vstd::std_specs::hash::group_hash_axioms;
        }
        let mut ret = Vec::new();
        let mut visited = HashSet::new();
        let mut to_visit = copy_of(es);
        #[cfg_attr(verus_keep_ghost, verus_spec(invariant
            self.has_all(to_visit@), self.has_all(ret@),
        ))]
        loop {
            let cur = match to_visit.pop() {
                Some(cur) => cur,
                None => break,
            };
            if self.store.is_ground(cur) || !visited.insert(cur) {
                continue;
            }
            if self.store.kind(cur) == Kind::PARAM {
                ret.push(cur);
                continue;
            }
            push_all(&mut to_visit, self.store.children(cur));
        }
        ret
    }

    /// Whether `var`, a parameter, occurs in `e`.
    #[cfg_attr(verus_keep_ghost, verifier::exec_allows_no_decreases_clause, verifier::loop_isolation(false), verus_spec(
        requires self.wf(), self.has(e),
    ))]
    pub fn has_variable(&self, e: Term, var: Term) -> bool {
        proof! {
            use_collections();
            broadcast use vstd::std_specs::hash::group_hash_axioms;
        }
        let mut visited = HashSet::new();
        let mut to_visit = Vec::new();
        to_visit.push(e);
        #[cfg_attr(verus_keep_ghost, verus_spec(invariant self.has_all(to_visit@),))]
        loop {
            let cur = match to_visit.pop() {
                Some(cur) => cur,
                None => break,
            };
            if self.store.is_ground(cur) || !visited.insert(cur) {
                continue;
            }
            if cur == var {
                return true;
            }
            push_all(&mut to_visit, self.store.children(cur));
        }
        false
    }
}

#[cfg(verus_keep_ghost)]
verus! {

/// A part of a list of terms of the store is one.
pub(crate) proof fn lemma_part(s: &TermStore, ts: Seq<Term>, from: int, to: int)
    requires all_has(s, ts), 0 <= from <= to <= ts.len(),
    ensures all_has(s, ts.subrange(from, to)),
{
    assert forall|i: int| 0 <= i < to - from implies s.has(#[trigger] ts.subrange(from, to)[i]) by {
        assert(s.has(ts[from + i]));
    }
}

/// Terms of a store are terms of a store that kept its terms.
pub(crate) proof fn lemma_all_kept(s1: &TermStore, s0: &TermStore, ts: Seq<Term>)
    requires all_has(s0, ts), keeps(s1, s0),
    ensures all_has(s1, ts),
{
    assert forall|i: int| 0 <= i < ts.len() implies s1.has(#[trigger] ts[i]) by {
        assert(s0.has(ts[i]));
    }
}

/// The same of a list with one more term.
pub(crate) proof fn lemma_pushed(s1: &TermStore, s0: &TermStore, ts: Seq<Term>, t: Term)
    requires all_has(s0, ts), keeps(s1, s0), s1.has(t),
    ensures all_has(s1, ts.push(t)),
{
    assert forall|i: int| 0 <= i < ts.len() + 1 implies s1.has(#[trigger] ts.push(t)[i]) by {
        if i < ts.len() {
            assert(s0.has(ts[i]));
        }
    }
}

} // verus!
