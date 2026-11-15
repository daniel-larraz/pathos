//! Typing (`TypeChecker::getType` in Ethos).

use std::collections::HashSet;

use pathos_term::{EvalOp, Kind, Lit, LitKind, NodeKind, Term};

use crate::checker::{Checker, Ctx};
use crate::matching;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

use crate::eval::{copy_of, push_all};
#[cfg(verus_keep_ghost)]
use crate::eval::{lemma_keeps_twice, use_collections};

/// Appends text to an optional error message. Messages are only built on
/// the second pass, after a check has failed (see [`Checker::get_type`]).
///
/// Trusted: Verus does not look into the message.
#[cfg_attr(verus_keep_ghost, verus_verify(external_body))]
fn say(out: &mut Option<&mut String>, text: &str) {
    if let Some(o) = out.as_deref_mut() {
        o.push_str(text);
    }
}

// The texts of the messages with something of the input in them. Trusted:
// formatting and printing are not verified.

#[cfg_attr(verus_keep_ghost, verus_verify(external_body))]
fn msg_bool_rule(k: LitKind) -> String {
    format!(
        "Cannot set a type rule for kind {}, since Boolean literals have the builtin type Bool",
        Kind::Lit(k)
    )
}

#[cfg_attr(verus_keep_ghost, verus_verify(external_body))]
fn msg_no_rule(k: LitKind) -> String {
    format!(
        "No type rule declared for literal kind {}; use declare-consts to declare its type \
         before use",
        Kind::Lit(k)
    )
}

#[cfg_attr(verus_keep_ghost, verus_verify(external_body))]
fn msg_unknown_arity(k: Kind) -> String {
    format!("Unknown arity for {k}")
}

#[cfg_attr(verus_keep_ghost, verus_verify(external_body))]
fn msg_arity(k: Kind) -> String {
    format!("Incorrect arity for {k}")
}

#[cfg_attr(verus_keep_ghost, verus_verify(external_body))]
fn msg_bad_type(k: Kind) -> String {
    format!("Encountered bad type for {}", k.to_term_string())
}

#[cfg_attr(verus_keep_ghost, verus_verify(external_body))]
fn msg_unknown_kind(k: Kind) -> String {
    format!("Unknown kind {k}")
}

// Written for Verus, which follows a loop over indices without a
// specification of the iterator, and does not take `let` in a condition
// with `&&` or as the condition of a `while`.
#[allow(
    clippy::needless_range_loop,
    clippy::collapsible_if,
    clippy::while_let_loop
)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
impl Checker {
    #[cfg_attr(verus_keep_ghost, verus_verify(external_body))]
    fn msg_rule_set(&self, k: LitKind, t: Term, prev: Term) -> String {
        format!(
            "Cannot set type rule for kind {} to {}, since its type was already set to {}",
            Kind::Lit(k),
            self.show(t),
            self.show(prev)
        )
    }

    #[cfg_attr(verus_keep_ghost, verus_verify(external_body))]
    fn msg_unreduced(&self, t: Term) -> String {
        format!(
            "Has type {} whose evaluation cannot be reduced",
            self.show(t)
        )
    }

    #[cfg_attr(verus_keep_ghost, verus_verify(external_body))]
    fn msg_non_function(&self, hd: Term, hd_type: Term) -> String {
        format!(
            "Non-function {} as head of APPLY\nIts type is {}",
            self.show(hd),
            self.show(hd_type)
        )
    }

    /// `types` and `given` are the numbers of children of the head's type
    /// and of the application.
    #[cfg_attr(verus_keep_ghost, verus_verify(external_body))]
    fn msg_app_arity(&self, hd: Term, types: usize, given: usize) -> String {
        format!(
            "Incorrect arity for {}, which expects {} arguments but {} were provided",
            self.show(hd),
            types.wrapping_sub(1),
            given - 1
        )
    }

    #[cfg_attr(verus_keep_ghost, verus_verify(external_body))]
    fn msg_child_type(
        &self,
        hd: Term,
        i: usize,
        term: Term,
        has: Term,
        expected: Term,
        ctx: &Ctx,
    ) -> String {
        format!(
            "Checking application of {}\nUnexpected type of child #{}\n  Term: {}\n  Has type: \
             {}\n  Expected type: {}\n  Context {}\n",
            self.show(hd),
            i,
            self.show(term),
            self.show(has),
            self.show(expected),
            self.show_ctx(ctx)
        )
    }

    /// The return type of the function type `t`
    /// ([`Checker::get_function_type`]).
    ///
    /// Trusted: `build.rs` is not verified.
    #[cfg_attr(verus_keep_ghost, verus_verify(external_body), verus_spec(r =>
        requires self.wf(), self.has(t),
        ensures self.has(r),
    ))]
    fn return_type_of(&self, t: Term) -> Term {
        self.get_function_type(t).1
    }

    /// [`Checker::mk_function_type`]. Trusted: `build.rs` is not verified.
    #[cfg_attr(verus_keep_ghost, verus_verify(external_body), verus_spec(r =>
        requires old(self).wf(), old(self).has_all(args@), old(self).has(ret),
        ensures
            final(self).wf(),
            final(self).keeps(old(self)),
            final(self).has(r),
    ))]
    fn function_type_of(&mut self, args: &[Term], ret: Term) -> Term {
        self.mk_function_type(args, ret)
    }

    /// Sets the type rule of a literal kind. Fails if the kind is Boolean,
    /// whose type is builtin, or if the rule is already set to another type.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires old(self).wf(), old(self).has(t),
        ensures final(self).wf(), final(self).keeps(old(self)),
    ))]
    pub fn set_literal_type_rule(
        &mut self,
        k: LitKind,
        t: Term,
        mut out: Option<&mut String>,
    ) -> bool {
        proof! {
            use_collections();
            axiom_literal_kinds_are_keys();
            broadcast use vstd::std_specs::hash::group_hash_axioms;
        }
        if k == LitKind::Boolean {
            if out.is_some() {
                say(&mut out, &msg_bool_rule(k));
            }
            return false;
        }
        if let Some(&prev) = self.literal_type_rules.get(&k) {
            if prev != t {
                if out.is_some() {
                    let msg = self.msg_rule_set(k, t, prev);
                    say(&mut out, &msg);
                }
                return false;
            }
        }
        self.literal_type_rules.insert(k, t);
        true
    }

    /// The type of literals of kind `k`. `self_term` instantiates `eo::self`
    /// in the rule; without it, `eo::?` does.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires old(self).wf(), self_term matches Some(t) ==> old(self).has(t),
        ensures
            final(self).wf(),
            final(self).keeps(old(self)),
            r matches Some(t) ==> final(self).has(t),
    ))]
    pub fn get_literal_type_rule(
        &mut self,
        k: LitKind,
        self_term: Option<Term>,
        mut out: Option<&mut String>,
    ) -> Option<Term> {
        self.literal_type_rule(k, self_term, &mut out)
    }

    /// [`Checker::get_literal_type_rule`], for a caller that goes on with
    /// its message.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires old(self).wf(), self_term matches Some(t) ==> old(self).has(t),
        ensures
            final(self).wf(),
            final(self).keeps(old(self)),
            r matches Some(t) ==> final(self).has(t),
    ))]
    #[cfg_attr(verus_keep_ghost, verifier::exec_allows_no_decreases_clause)]
    fn literal_type_rule(
        &mut self,
        k: LitKind,
        self_term: Option<Term>,
        out: &mut Option<&mut String>,
    ) -> Option<Term> {
        proof! {
            use_collections();
            axiom_literal_kinds_are_keys();
            broadcast use vstd::std_specs::hash::group_hash_axioms;
            broadcast use vstd::std_specs::btree::group_btree_axioms;
        }
        if k == LitKind::Boolean {
            return Some(self.mk_bool_type());
        }
        let tp = match self.literal_type_rules.get(&k) {
            Some(&tp) => tp,
            None => {
                if out.is_some() {
                    say(out, &msg_no_rule(k));
                }
                return None;
            }
        };
        if !self.store.is_ground(tp) {
            let mut ctx = Ctx::new();
            let any = self.mk_any();
            let instance = match self_term {
                Some(t) => t,
                None => any,
            };
            ctx.insert(self.mk_self(), instance);
            return Some(self.evaluate(tp, &ctx));
        }
        Some(tp)
    }

    /// The type of `e`, or `None` if it is not well typed. Types are cached
    /// in the store.
    ///
    /// With `out`, a description of the failure is appended to it. Callers
    /// first call without `out` and, on failure, call again to get the
    /// message, as Ethos does.
    ///
    /// Verus proves that it does not panic, not that it ends: it evaluates.
    #[cfg_attr(verus_keep_ghost, verifier::loop_isolation(false), verus_spec(r =>
        requires old(self).wf(), old(self).has(e),
        ensures
            final(self).wf(),
            final(self).keeps(old(self)),
            r matches Some(t) ==> final(self).has(t),
    ))]
    #[cfg_attr(verus_keep_ghost, verifier::exec_allows_no_decreases_clause)]
    pub fn get_type(&mut self, e: Term, mut out: Option<&mut String>) -> Option<Term> {
        proof! {
            use_collections();
            broadcast use vstd::std_specs::hash::group_hash_axioms;
        }
        if let Some(t) = self.store.ty(e) {
            return Some(t);
        }
        proof_decl! { let ghost start = *self; }
        let mut visited: HashSet<Term> = HashSet::new();
        let mut to_visit = Vec::new();
        to_visit.push(e);
        let mut ret = None;
        #[cfg_attr(verus_keep_ghost, verus_spec(invariant
            self.wf(),
            self.keeps(&start),
            self.has_all(to_visit@),
            ret matches Some(t) ==> self.has(t),
        ))]
        loop {
            let cur = match to_visit.last() {
                Some(&cur) => cur,
                None => break,
            };
            proof! { assert(self.has(to_visit@[to_visit@.len() - 1])); }
            if let Some(t) = self.store.ty(cur) {
                ret = Some(t);
                to_visit.pop();
                continue;
            }
            if visited.insert(cur) {
                push_all(&mut to_visit, self.store.children(cur));
            } else {
                proof_decl! { let ghost before = *self; }
                let found = self.get_type_internal(cur, &mut out);
                proof! {
                    lemma_keeps_twice(&self.store, &before.store, &start.store);
                    assert forall|i: int| 0 <= i < to_visit@.len() implies self.has(#[trigger] to_visit@[i]) by {
                        assert(before.has(to_visit@[i]));
                    }
                }
                let t = found?;
                if self.store.is_ground(t) && self.store.is_evaluatable(t) {
                    if out.is_some() {
                        let msg = self.msg_unreduced(t);
                        say(&mut out, &msg);
                    }
                    return None;
                }
                proof_decl! { let ghost mid = *self; }
                self.store.set_ty(cur, t);
                proof! {
                    self.lemma_stored(&mid);
                    lemma_keeps_twice(&self.store, &mid.store, &start.store);
                    assert forall|i: int| 0 <= i < to_visit@.len() implies self.has(#[trigger] to_visit@[i]) by {
                        assert(mid.has(to_visit@[i]));
                    }
                }
                ret = Some(t);
                to_visit.pop();
            }
        }
        ret
    }

    /// Whether the `eo::` operator or `PROOF` kind `k` takes `nargs`
    /// arguments.
    #[cfg_attr(verus_keep_ghost, verus_spec(r => ensures r == Checker::takes(k, nargs),))]
    pub fn check_arity(k: Kind, nargs: usize, mut out: Option<&mut String>) -> bool {
        Checker::arity(k, nargs, &mut out)
    }

    /// [`Checker::check_arity`], for a caller that goes on with its message.
    #[cfg_attr(verus_keep_ghost, verus_spec(r => ensures r == Checker::takes(k, nargs),))]
    fn arity(k: Kind, nargs: usize, out: &mut Option<&mut String>) -> bool {
        let ret = match k {
            Kind::Node(NodeKind::Proof) => nargs == 1,
            Kind::Eval(op) => match op {
                EvalOp::IsEq
                | EvalOp::Eq
                | EvalOp::IntDiv
                | EvalOp::IntMod
                | EvalOp::RatDiv
                | EvalOp::Pow
                | EvalOp::ToBin
                | EvalOp::Find
                | EvalOp::Compare
                | EvalOp::Log
                | EvalOp::Gt
                | EvalOp::ListLength
                | EvalOp::ListRev
                | EvalOp::ListSetof
                | EvalOp::ListSingletonElim
                | EvalOp::ListSingletonIntro
                | EvalOp::Nil => nargs == 2,
                EvalOp::ListConcat => nargs == 3,
                EvalOp::IsOk
                | EvalOp::TypeOf
                | EvalOp::NameOf
                | EvalOp::Hash
                | EvalOp::Not
                | EvalOp::Neg
                | EvalOp::IsNeg
                | EvalOp::Length
                | EvalOp::ToInt
                | EvalOp::ToRat
                | EvalOp::ToString
                | EvalOp::IsZ
                | EvalOp::IsQ
                | EvalOp::IsBin
                | EvalOp::IsStr
                | EvalOp::IsBool
                | EvalOp::IsVar
                | EvalOp::DtConstructors
                | EvalOp::DtSelectors => nargs == 1,
                EvalOp::Requires
                | EvalOp::IfThenElse
                | EvalOp::Cons
                | EvalOp::ListFind
                | EvalOp::ListErase
                | EvalOp::ListEraseAll
                | EvalOp::ListNth
                | EvalOp::ListMinclude
                | EvalOp::ListMeq
                | EvalOp::ListDiff
                | EvalOp::ListInter
                | EvalOp::ListRepeat => nargs == 3,
                EvalOp::Extract => nargs == 3 || nargs == 2,
                // the n-ary operators
                EvalOp::Add
                | EvalOp::Mul
                | EvalOp::And
                | EvalOp::Or
                | EvalOp::Xor
                | EvalOp::Concat => nargs == 2,
            },
            _ => {
                if out.is_some() {
                    say(out, &msg_unknown_arity(k));
                }
                false
            }
        };
        if !ret {
            if out.is_some() {
                say(out, &msg_arity(k));
            }
        }
        ret
    }

    /// The type of `e`, whose children all have their types cached.
    #[cfg_attr(verus_keep_ghost, verifier::loop_isolation(false), verus_spec(r =>
        requires old(self).wf(), old(self).has(e),
        ensures
            final(self).wf(),
            final(self).keeps(old(self)),
            r matches Some(t) ==> final(self).has(t),
    ))]
    #[cfg_attr(verus_keep_ghost, verifier::exec_allows_no_decreases_clause)]
    fn get_type_internal(&mut self, e: Term, out: &mut Option<&mut String>) -> Option<Term> {
        proof! {
            self.store.lemma_children(e);
            self.store.lemma_shape(e);
        }
        let k = self.store.kind(e);
        match k {
            Kind::Node(NodeKind::Apply | NodeKind::ApplyOpaque) => {
                let children = copy_of(self.store.children(e));
                let mut ctx = Ctx::new();
                self.get_type_app_internal(&children, &mut ctx, out)
            }
            Kind::Node(NodeKind::Lambda) => {
                let vars = copy_of(self.store.children(self.store.child(e, 0)));
                let mut args = Vec::with_capacity(vars.len());
                #[cfg_attr(verus_keep_ghost, verus_spec(invariant
                    forall|j: int| 0 <= j < args@.len() ==> self.has(#[trigger] args@[j]),
                ))]
                for i in 0..vars.len() {
                    args.push(self.store.ty(vars[i])?);
                }
                let ret = self.store.ty(self.store.child(e, 1))?;
                Some(self.function_type_of(&args, ret))
            }
            Kind::Type
            | Kind::BoolType
            | Kind::Any
            | Kind::Node(NodeKind::FunctionType | NodeKind::ProgramType) => Some(self.mk_type()),
            Kind::Node(NodeKind::Proof) => {
                let ctype = self.store.ty(self.store.child(e, 0))?;
                if self.store.kind(ctype) != Kind::BoolType {
                    say(out, "Non-Bool for argument of Proof");
                    return None;
                }
                Some(self.mk_proof_type())
            }
            // These are not really typed. Their type is the unknown, not
            // Type, so that they cannot be used as the types of terms.
            Kind::Node(NodeKind::QuoteType | NodeKind::Tuple) => Some(self.mk_any()),
            Kind::Lit(lk) => self.literal_type_rule(lk, Some(e), out),
            Kind::Node(NodeKind::As | NodeKind::AsReturn) => {
                // an AS term is only built when the annotation was wrong
                if out.is_some() {
                    say(out, &msg_bad_type(k));
                }
                None
            }
            Kind::Node(NodeKind::Parameterized) => self.store.ty(self.store.child(e, 1)),
            Kind::Node(NodeKind::Variable) => {
                // `eo::var` can be applied to any number of arguments. Ethos
                // reads the first two without checking that they are there;
                // here a missing one fails the check that needs it.
                let children = self.store.children(e);
                let (c0, c1) = (children.first().copied(), children.get(1).copied());
                let ctype1 = match c0 {
                    Some(c) => self.store.ty(c),
                    None => None,
                };
                let ctype2 = match c1 {
                    Some(c) => self.store.ty(c),
                    None => None,
                };
                let string_type = self.literal_type_rule(LitKind::String, c0, out)?;
                let is_string = match ctype1 {
                    Some(t) => t == string_type,
                    None => false,
                };
                if !is_string {
                    say(out, "Expected a string for first argument of eo::var");
                    return None;
                }
                if let Some(c1) = c1 {
                    if let Some(t) = ctype2 {
                        if self.store.kind(t) == Kind::Type {
                            return Some(c1);
                        }
                    }
                }
                say(out, "Expected a type for second argument of eo::var");
                None
            }
            Kind::Eval(op) => {
                let children = copy_of(self.store.children(e));
                let mut ctypes: Vec<Option<Term>> = Vec::with_capacity(children.len());
                #[cfg_attr(verus_keep_ghost, verus_spec(invariant
                    ctypes@.len() == i,
                    forall|j: int| 0 <= j < i ==> ((#[trigger] ctypes@[j]) matches Some(t) ==> self.has(t)),
                ))]
                for i in 0..children.len() {
                    ctypes.push(self.store.ty(children[i]));
                }
                self.get_literal_op_type(op, &children, &ctypes, out)
            }
            Kind::Symbol(_) | Kind::Node(NodeKind::Program) | Kind::Null => {
                // symbols always have a type; programs and the null
                // expression are never typed
                if out.is_some() {
                    say(out, &msg_unknown_kind(k));
                }
                None
            }
        }
    }

    /// The type of the application of `children[0]` to the rest, whose types
    /// are cached. `ctx` receives the instantiation of the head's type.
    ///
    /// The pairs matched are remembered across the arguments, and the
    /// parameter of a quoted argument is bound in between, which may bind
    /// it again (`docs/ethos-differences.md`). So what is proved of
    /// matching, that a match found instantiates the pattern to the term,
    /// is not known of these calls; that they do not panic is.
    #[cfg_attr(verus_keep_ghost, verifier::loop_isolation(false), verus_spec(r =>
        requires
            old(self).wf(),
            old(self).has_all(children@),
            // the first is the head
            children@.len() >= 1,
            old(self).binds(old(ctx)@),
        ensures
            final(self).wf(),
            final(self).keeps(old(self)),
            r matches Some(t) ==> final(self).has(t),
    ))]
    #[cfg_attr(verus_keep_ghost, verifier::exec_allows_no_decreases_clause)]
    pub(crate) fn get_type_app_internal(
        &mut self,
        children: &[Term],
        ctx: &mut Ctx,
        out: &mut Option<&mut String>,
    ) -> Option<Term> {
        proof! {
            use_collections();
            broadcast use vstd::std_specs::hash::group_hash_axioms;
            broadcast use vstd::std_specs::btree::group_btree_axioms;
        }
        let hd = children[0];
        let hd_type = self.store.ty(hd)?;
        let hk = self.store.kind(hd_type);
        if hk != Kind::FUNCTION_TYPE && hk != Kind::PROGRAM_TYPE {
            if out.is_some() {
                let msg = self.msg_non_function(hd, hd_type);
                say(out, &msg);
            }
            return None;
        }
        let hdtypes = copy_of(self.store.children(hd_type));
        if hdtypes.len() != children.len() {
            if out.is_some() {
                let msg = self.msg_app_arity(hd, hdtypes.len(), children.len());
                say(out, &msg);
            }
            return None;
        }
        let mut visited = HashSet::new();
        #[cfg_attr(verus_keep_ghost, verus_spec(invariant
            hdtypes@.len() == children@.len(),
            self.has_all(hdtypes@),
            self.binds(ctx@),
        ))]
        for i in 1..hdtypes.len() {
            let mut hdt = hdtypes[i - 1];
            let mut child = children[i];
            let type_success;
            if self.store.kind(hdt) == Kind::QUOTE_TYPE {
                // For an argument type (eo::quote x), the argument must have
                // the type of x, which is ground. Then x is bound to the
                // argument itself: no matching is needed.
                proof! { self.store.lemma_shape(hdt); }
                let x = self.store.child(hdt, 0);
                let ct = self.store.ty(child)?;
                let cte = self.store.ty(x)?;
                if ct != cte {
                    type_success = false;
                    hdt = cte;
                    child = ct;
                } else {
                    type_success = true;
                    hdt = x;
                    ctx.insert(hdt, child);
                }
            } else {
                child = self.store.ty(child)?;
                type_success = matching::match_terms(&self.store, hdt, child, ctx, &mut visited);
            }
            if !type_success {
                if out.is_some() {
                    let msg = self.msg_child_type(hd, i, children[i], child, hdt, ctx);
                    say(out, &msg);
                }
                return None;
            }
        }
        // the return type, in the matched context
        let ret = hdtypes[hdtypes.len() - 1];
        Some(self.evaluate(ret, ctx))
    }

    /// The type of an `eo::` operator application.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires
            old(self).wf(),
            old(self).has_all(children@),
            children@.len() == child_types@.len(),
            forall|j: int| 0 <= j < child_types@.len() ==>
                ((#[trigger] child_types@[j]) matches Some(t) ==> old(self).has(t)),
        ensures
            final(self).wf(),
            final(self).keeps(old(self)),
            r matches Some(t) ==> final(self).has(t),
    ))]
    #[cfg_attr(verus_keep_ghost, verifier::exec_allows_no_decreases_clause)]
    fn get_literal_op_type(
        &mut self,
        op: EvalOp,
        children: &[Term],
        child_types: &[Option<Term>],
        out: &mut Option<&mut String>,
    ) -> Option<Term> {
        if !Checker::arity(Kind::Eval(op), child_types.len(), out) {
            return None;
        }
        // Most of these operators only occur in patterns, where typing is
        // not strict.
        match op {
            EvalOp::TypeOf => Some(self.mk_type()),
            // the type is the second argument
            EvalOp::Nil => Some(children[1]),
            EvalOp::Add
            | EvalOp::Mul
            | EvalOp::Pow
            | EvalOp::Neg
            | EvalOp::And
            | EvalOp::Or
            | EvalOp::Xor
            | EvalOp::Not
            | EvalOp::Concat
            | EvalOp::Extract => child_types[0],
            EvalOp::IfThenElse
            | EvalOp::Cons
            | EvalOp::ListConcat
            | EvalOp::ListNth
            | EvalOp::ListErase
            | EvalOp::ListEraseAll
            | EvalOp::ListRev
            | EvalOp::ListSetof
            | EvalOp::ListDiff
            | EvalOp::ListInter
            | EvalOp::ListSingletonElim
            | EvalOp::ListSingletonIntro => child_types[1],
            EvalOp::Requires => child_types[2],
            EvalOp::ListRepeat => {
                let op_type = child_types[0]?;
                if self.store.kind(op_type) == Kind::FUNCTION_TYPE {
                    Some(self.return_type_of(op_type))
                } else {
                    None
                }
            }
            EvalOp::IsOk
            | EvalOp::IsEq
            | EvalOp::Eq
            | EvalOp::IsNeg
            | EvalOp::Compare
            | EvalOp::IsZ
            | EvalOp::IsQ
            | EvalOp::IsBin
            | EvalOp::IsStr
            | EvalOp::IsBool
            | EvalOp::IsVar
            | EvalOp::Gt
            | EvalOp::ListMinclude
            | EvalOp::ListMeq => Some(self.mk_bool_type()),
            EvalOp::Hash
            | EvalOp::Log
            | EvalOp::IntDiv
            | EvalOp::IntMod
            | EvalOp::ToInt
            | EvalOp::Length
            | EvalOp::Find
            | EvalOp::ListLength
            | EvalOp::ListFind => self.literal_type_rule(LitKind::Numeral, None, out),
            EvalOp::RatDiv | EvalOp::ToRat => self.literal_type_rule(LitKind::Rational, None, out),
            EvalOp::NameOf | EvalOp::ToString => self.literal_type_rule(LitKind::String, None, out),
            EvalOp::ToBin => self.literal_type_rule(LitKind::Binary, None, out),
            EvalOp::DtConstructors | EvalOp::DtSelectors => Some(self.mk_list_type()),
        }
    }
}

impl Checker {
    /// The term for a string literal given as Ethos's `mkLiteral` takes it:
    /// text in which `\u{...}` escapes denote code points.
    pub fn mk_string_literal(&mut self, s: &str) -> Term {
        self.store
            .mk_lit(Lit::String(pathos_term::EoString::parse(s, true)))
    }
}

#[cfg(verus_keep_ghost)]
verus! {

/// Assumed: the derived `Hash` and `Eq` of the kinds of literals agree,
/// which is what the table of literal type rules needs to behave as a map.
#[verifier::external_body]
pub proof fn axiom_literal_kinds_are_keys()
    ensures vstd::std_specs::hash::obeys_key_model::<LitKind>(),
{
}

impl Checker {
    /// [`Checker::check_arity`]: whether the `eo::` operator or `PROOF`
    /// kind `k` takes `nargs` arguments.
    pub open spec fn takes(k: Kind, nargs: usize) -> bool {
        match k {
                Kind::Node(NodeKind::Proof) => nargs == 1,
                Kind::Eval(op) => match op {
                    EvalOp::IsEq
                    | EvalOp::Eq
                    | EvalOp::IntDiv
                    | EvalOp::IntMod
                    | EvalOp::RatDiv
                    | EvalOp::Pow
                    | EvalOp::ToBin
                    | EvalOp::Find
                    | EvalOp::Compare
                    | EvalOp::Log
                    | EvalOp::Gt
                    | EvalOp::ListLength
                    | EvalOp::ListRev
                    | EvalOp::ListSetof
                    | EvalOp::ListSingletonElim
                    | EvalOp::ListSingletonIntro
                    | EvalOp::Nil => nargs == 2,
                    EvalOp::ListConcat => nargs == 3,
                    EvalOp::IsOk
                    | EvalOp::TypeOf
                    | EvalOp::NameOf
                    | EvalOp::Hash
                    | EvalOp::Not
                    | EvalOp::Neg
                    | EvalOp::IsNeg
                    | EvalOp::Length
                    | EvalOp::ToInt
                    | EvalOp::ToRat
                    | EvalOp::ToString
                    | EvalOp::IsZ
                    | EvalOp::IsQ
                    | EvalOp::IsBin
                    | EvalOp::IsStr
                    | EvalOp::IsBool
                    | EvalOp::IsVar
                    | EvalOp::DtConstructors
                    | EvalOp::DtSelectors => nargs == 1,
                    EvalOp::Requires
                    | EvalOp::IfThenElse
                    | EvalOp::Cons
                    | EvalOp::ListFind
                    | EvalOp::ListErase
                    | EvalOp::ListEraseAll
                    | EvalOp::ListNth
                    | EvalOp::ListMinclude
                    | EvalOp::ListMeq
                    | EvalOp::ListDiff
                    | EvalOp::ListInter
                    | EvalOp::ListRepeat => nargs == 3,
                    EvalOp::Extract => nargs == 3 || nargs == 2,
                    // the n-ary operators
                    EvalOp::Add
                    | EvalOp::Mul
                    | EvalOp::And
                    | EvalOp::Or
                    | EvalOp::Xor
                    | EvalOp::Concat => nargs == 2,
                },
            _ => false,
        }
    }
}

} // verus!
