//! Evaluation (`TypeChecker::evaluate` and the program and `eo::` operator
//! evaluators in Ethos's `type_checker.cpp`).

use std::collections::{HashMap, HashSet};

use pathos_term::{EvalOp, Integer, Kind, Lit, NodeKind, Term};
#[cfg(verus_keep_ghost)]
use pathos_term::{
    LitKind, TermStore, Tree, Val, lemma_vals, lit_arity, lit_spec, tree_is_evaluatable,
    tree_is_ground, vals,
};

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

use crate::attr::Attr;
use crate::checker::{Checker, Ctx};
#[cfg(verus_keep_ghost)]
use crate::checker::{all_has, axiom_terms_are_keys, keeps};
use crate::matching::{self, CaseMatch};
#[cfg(verus_keep_ghost)]
use crate::matching::{axiom_term_pairs_are_keys, axiom_terms_are_ordered, ctx_ok};

/// The `i`-th argument of the operator `k`, read where Ethos reads it. A
/// missing one stops the run.
macro_rules! arg {
    ($self:ident, $k:expr, $args:expr, $i:expr) => {
        match $args.get($i) {
            Some(&a) => a,
            None => return $self.missing_argument($k, $args),
        }
    };
}

/// One level of evaluation: a term being evaluated in a context. A new level
/// starts each time a program application reduces to a case's body.
#[cfg_attr(verus_keep_ghost, verus_verify)]
struct EvFrame {
    init: Term,
    ctx: Ctx,
    /// The value of each subterm visited so far; `None` while its children
    /// are being evaluated.
    visited: HashMap<Term, Option<Term>>,
    visit: Vec<Term>,
    /// The program application this level computes, to be cached.
    result_key: Option<Vec<Term>>,
}

/// The results of program applications in one call of
/// [`Checker::evaluate`]; `None` is an application that failed.
type EvalCache = HashMap<Vec<Term>, Option<Term>>;

/// What a level does after a term on its work list was looked at.
#[cfg_attr(verus_keep_ghost, verus_verify)]
enum Step {
    /// Goes on with its work list.
    Next,
    /// Waits for a new level: the body of a program's case, which needs
    /// substitution.
    Call(EvFrame),
    /// Stops: the run is over; see [`Checker::take_fatal`].
    Fatal,
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
impl EvFrame {
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        ensures
            r.init == init,
            r.ctx == ctx,
            r.visited@ == Map::<Term, Option<Term>>::empty(),
            r.visit@ == seq![init],
            r.result_key == result_key,
    ))]
    fn new(init: Term, ctx: Ctx, result_key: Option<Vec<Term>>) -> EvFrame {
        proof! {
            use_collections();
            broadcast use vstd::std_specs::hash::group_hash_axioms;
        }
        // (Verus has no `vec!`)
        #[allow(clippy::vec_init_then_push)]
        let visit = {
            let mut visit = Vec::new();
            visit.push(init);
            visit
        };
        EvFrame {
            init,
            ctx,
            visited: HashMap::new(),
            visit,
            result_key,
        }
    }

    /// The value of the term the level was made for, once its work list is
    /// empty.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        ensures r == if self.valued(self.init) { self.visited@[self.init]->0 } else { self.init },
    ))]
    fn result(&self) -> Term {
        proof! {
            use_collections();
            broadcast use vstd::std_specs::hash::group_hash_axioms;
        }
        match self.visited.get(&self.init) {
            Some(&Some(v)) => v,
            _ => self.init,
        }
    }

    /// Gives the term on top of the work list its value and takes it off.
    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires old(self).visit@.len() > 0,
        ensures
            final(self).visit@ == old(self).visit@.drop_last(),
            final(self).visited@ == old(self).visited@.insert(cur, Some(value)),
            final(self).init == old(self).init,
            final(self).ctx == old(self).ctx,
            final(self).result_key == old(self).result_key,
    ))]
    fn settle(&mut self, cur: Term, value: Term) {
        proof! {
            use_collections();
            broadcast use vstd::std_specs::hash::group_hash_axioms;
        }
        self.visited.insert(cur, Some(value));
        self.visit.pop();
    }
}

/// The values, if every child has one.
// Written for Verus: a loop over indices, and no `?`.
#[allow(clippy::needless_range_loop, clippy::question_mark)]
#[cfg_attr(verus_keep_ghost, verus_verify, verus_spec(r =>
    ensures
        r matches Some(a) ==> a@.len() == cchildren@.len()
            && forall|i: int| 0 <= i < a@.len() ==> cchildren@[i] == Some(#[trigger] a@[i]),
        (forall|i: int| 0 <= i < cchildren@.len() ==> (#[trigger] cchildren@[i]) is Some) ==> r is Some,
))]
fn all_values(cchildren: &[Option<Term>]) -> Option<Vec<Term>> {
    let mut args = Vec::with_capacity(cchildren.len());
    #[cfg_attr(verus_keep_ghost, verus_spec(invariant
        args@.len() == i,
        forall|j: int| 0 <= j < i ==> cchildren@[j] == Some(#[trigger] args@[j]),
    ))]
    for i in 0..cchildren.len() {
        match cchildren[i] {
            Some(v) => args.push(v),
            None => return None,
        }
    }
    Some(args)
}

/// The value of each child, or the child itself where it has none.
#[allow(clippy::needless_range_loop)]
#[cfg_attr(verus_keep_ghost, verus_verify, verus_spec(r =>
    requires cchildren@.len() == children@.len(),
    ensures
        r@.len() == children@.len(),
        forall|i: int| 0 <= i < r@.len() ==>
            #[trigger] r@[i] == (if cchildren@[i] is Some { cchildren@[i]->0 } else { children@[i] }),
))]
fn values_or(cchildren: &[Option<Term>], children: &[Term]) -> Vec<Term> {
    let mut args = Vec::with_capacity(children.len());
    #[cfg_attr(verus_keep_ghost, verus_spec(invariant
        cchildren@.len() == children@.len(),
        args@.len() == i,
        forall|j: int| 0 <= j < i ==>
            #[trigger] args@[j] == (if cchildren@[j] is Some { cchildren@[j]->0 } else { children@[j] }),
    ))]
    for i in 0..children.len() {
        args.push(match cchildren[i] {
            Some(v) => v,
            None => children[i],
        });
    }
    args
}

/// A copy of the terms. (Verus has no specification of `to_vec`.)
#[cfg_attr(verus_keep_ghost, verus_verify(external_body), verus_spec(r => ensures r@ == ts@,))]
pub(crate) fn copy_of(ts: &[Term]) -> Vec<Term> {
    ts.to_vec()
}

/// Puts the terms on a list, in their order. (Verus's specification of
/// `extend_from_slice` speaks of clones.)
#[cfg_attr(verus_keep_ghost, verus_verify(external_body), verus_spec(
    ensures final(list)@ == old(list)@ + ts@,
))]
#[inline(always)]
pub(crate) fn push_all(list: &mut Vec<Term>, ts: &[Term]) {
    list.extend_from_slice(ts);
}

/// A copy of the substitution. (Verus has no specification of `clone` for
/// the map.)
#[cfg_attr(verus_keep_ghost, verus_verify(external_body), verus_spec(r => ensures r@ == ctx@,))]
fn copy_of_ctx(ctx: &Ctx) -> Ctx {
    ctx.clone()
}

/// A term was looked at the second time before its children had values: a
/// bug in [`Checker::evaluate`].
#[cfg_attr(verus_keep_ghost, verus_verify(external_body), verus_spec(requires false,))]
fn children_first(what: &str) -> Vec<Term> {
    unreachable!("children of {what} are evaluated first")
}

// Written for Verus, which follows a loop over indices without a
// specification of the iterator, and does not take `let` in a condition
// with `&&`.
#[allow(clippy::needless_range_loop, clippy::collapsible_if)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
impl Checker {
    /// Evaluates `e` with the parameters in `ctx` replaced: applies programs
    /// and `eo::` operators until none applies. Stuck applications stay in
    /// the result.
    ///
    /// Verus proves that it does not panic, not that it ends: a program
    /// may run for ever.
    #[cfg_attr(verus_keep_ghost, verifier::exec_allows_no_decreases_clause, verifier::loop_isolation(false), verus_spec(r =>
        requires old(self).wf(), old(self).has(e), old(self).binds(ctx@),
        ensures
            final(self).wf(),
            final(self).keeps(old(self)),
            final(self).has(r),
    ))]
    pub fn evaluate(&mut self, e: Term, ctx: &Ctx) -> Term {
        proof! {
            use_collections();
            axiom_term_lists_are_keys();
            broadcast use vstd::std_specs::hash::group_hash_axioms;
            broadcast use vstd::std_specs::btree::group_btree_axioms;
        }
        proof_decl! { let ghost start = *self; }
        // Results of program applications in this call, so that programs
        // recursing over a term visit shared subterms once. `None` is an
        // application that failed: it is not tried again, as in Ethos, so
        // its warnings appear once.
        let mut eval_cache: EvalCache = HashMap::new();
        // the levels that wait for the one above them, and the one at work
        let mut estack: Vec<EvFrame> = Vec::new();
        let mut evf = EvFrame::new(e, copy_of_ctx(ctx), None);
        #[cfg_attr(verus_keep_ghost, verus_spec(invariant
            start.wf(),
            start.has(e),
            self.wf(),
            self.keeps(&start),
            evf.ok(&self.store),
            frames_ok(&self.store, estack@),
            cache_ok(&self.store, eval_cache@),
        ))]
        loop {
            proof_decl! { let ghost before = *self; }
            let step = self.run_frame(&mut evf, &mut eval_cache);
            proof! {
                lemma_frames_kept(&self.store, &before.store, estack@);
                lemma_keeps_twice(&self.store, &before.store, &start.store);
            }
            match step {
                Step::Next => {}
                // continue with the new level
                Step::Call(frame) => {
                    proof_decl! { let ghost below = estack@; }
                    estack.push(evf);
                    evf = frame;
                    proof! {
                        assert forall|i: int| 0 <= i < estack@.len() implies (#[trigger] estack@[i]).ok(&self.store) by {
                            if i < below.len() {
                                assert(below[i].ok(&self.store));
                            }
                        }
                    }
                    continue;
                }
                Step::Fatal => return e,
            }
            // this level is done: hand its result to the level below
            let result = evf.result();
            if let Some(key) = evf.result_key {
                eval_cache.insert(key, Some(result));
            }
            proof_decl! { let ghost below = estack@; }
            match estack.pop() {
                None => return result,
                Some(parent) => {
                    evf = parent;
                    proof_decl! { let ghost waiting = evf; }
                    proof! {
                        assert(below[below.len() - 1].ok(&self.store));
                        assert(waiting.ok(&self.store));
                        assert forall|i: int| 0 <= i < estack@.len() implies (#[trigger] estack@[i]).ok(&self.store) by {
                            assert(below[i].ok(&self.store));
                        }
                    }
                    if let Some(app) = evf.visit.pop() {
                        evf.visited.insert(app, Some(result));
                    }
                    proof! {
                        if waiting.visit@.len() > 0 {
                            lemma_settle(&waiting, &evf, &self.store, result);
                        } else {
                            lemma_same(&waiting, &evf, &self.store);
                        }
                    }
                }
            }
        }
    }

    /// Works on a level until its work list is empty ([`Step::Next`]) or it
    /// has to wait or stop.
    #[cfg_attr(verus_keep_ghost, verifier::exec_allows_no_decreases_clause, verifier::loop_isolation(false), verus_spec(r =>
        requires
            old(self).wf(),
            old(evf).ok(&old(self).store),
            cache_ok(&old(self).store, old(eval_cache)@),
        ensures
            final(self).wf(),
            final(self).keeps(old(self)),
            final(evf).ok(&final(self).store),
            cache_ok(&final(self).store, final(eval_cache)@),
            r matches Step::Call(f) ==> f.ok(&final(self).store),
    ))]
    fn run_frame(&mut self, evf: &mut EvFrame, eval_cache: &mut EvalCache) -> Step {
        proof_decl! { let ghost start = *self; }
        #[cfg_attr(verus_keep_ghost, verus_spec(invariant
            self.wf(),
            self.keeps(&start),
            evf.ok(&self.store),
            cache_ok(&self.store, eval_cache@),
        ))]
        loop {
            let cur = match evf.visit.last() {
                Some(&cur) => cur,
                None => return Step::Next,
            };
            proof_decl! { let ghost before = *self; }
            let step = self.visit_term(evf, eval_cache, cur);
            proof! { lemma_keeps_twice(&self.store, &before.store, &start.store); }
            match step {
                Step::Next => {}
                other => return other,
            }
        }
    }

    /// Looks at the term on top of a level's work list.
    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires
            old(self).wf(),
            old(evf).ok(&old(self).store),
            old(evf).visit@.len() > 0,
            cur == old(evf).visit@.last(),
            cache_ok(&old(self).store, old(eval_cache)@),
        ensures
            final(self).wf(),
            final(self).keeps(old(self)),
            final(evf).ok(&final(self).store),
            cache_ok(&final(self).store, final(eval_cache)@),
            r matches Step::Call(f) ==> f.ok(&final(self).store),
    ))]
    #[cfg_attr(verus_keep_ghost, verifier::exec_allows_no_decreases_clause)]
    fn visit_term(&mut self, evf: &mut EvFrame, eval_cache: &mut EvalCache, cur: Term) -> Step {
        proof! {
            use_collections();
            broadcast use vstd::std_specs::hash::group_hash_axioms;
            broadcast use vstd::std_specs::btree::group_btree_axioms;
            assert(self.store.has(cur));
        }
        proof_decl! { let ghost f0 = *evf; let ghost before = *self; }
        // Not evaluatable, and ground or nothing to substitute: the
        // term stays as it is.
        if !self.store.is_evaluatable(cur) && (self.store.is_ground(cur) || evf.ctx.is_empty()) {
            evf.settle(cur, cur);
            proof! { lemma_settle(&f0, evf, &self.store, cur); }
            return Step::Next;
        }
        let ck = self.store.kind(cur);
        if ck == Kind::PARAM {
            // a parameter the context does not bind stays
            let v = match evf.ctx.get(&cur) {
                Some(&v) => v,
                None => cur,
            };
            evf.settle(cur, v);
            proof! { lemma_settle(&f0, evf, &self.store, v); }
            return Step::Next;
        }
        let seen = evf.visited.get(&cur).copied();
        match seen {
            None => {
                // a plugin may evaluate the term itself
                if self.has_eval_plugin() {
                    let value = self.plugin_evaluate(cur, &evf.ctx);
                    proof! {
                        lemma_frame_kept(&f0, &self.store, &before.store);
                        lemma_cache_kept(&self.store, &before.store, eval_cache@);
                    }
                    if let Some(r) = value {
                        evf.settle(cur, r);
                        proof! { lemma_settle(&f0, evf, &self.store, r); }
                        return Step::Next;
                    }
                }
                // first visit: evaluate the children
                evf.visited.insert(cur, None);
                let children = self.store.children(cur);
                if ck == Kind::Eval(EvalOp::IfThenElse) {
                    if children.len() != 3 {
                        // malformed: does not evaluate
                        evf.settle(cur, cur);
                        proof! {
                            assert(evf.visited@ =~= f0.visited@.insert(cur, Some(cur)));
                            lemma_settle(&f0, evf, &self.store, cur);
                        }
                        return Step::Next;
                    }
                    // only the condition, for now
                    evf.visit.push(children[0]);
                    proof! {
                        let pushed = seq![children@[0]];
                        assert(evf.visit@ =~= f0.visit@ + pushed);
                        lemma_grow(&f0, evf, &self.store, pushed);
                    }
                } else {
                    push_all(&mut evf.visit, children);
                    proof! {
                        assert(self.store.kind_of(cur.idx()) == ck);
                        lemma_grow(&f0, evf, &self.store, children@);
                    }
                }
                Step::Next
            }
            Some(Some(_v)) => {
                evf.visit.pop();
                proof! {
                    assert(evf.visited@ =~= f0.visited@.insert(cur, Some(_v)));
                    lemma_settle(&f0, evf, &self.store, _v);
                }
                Step::Next
            }
            // second visit: the children are evaluated (for if-then-else,
            // at least the condition is)
            Some(None) => self.revisit_term(evf, eval_cache, cur, ck),
        }
    }

    /// Evaluates the term on top of a level's work list from the values of
    /// its children.
    #[inline]
    #[cfg_attr(verus_keep_ghost, verifier::loop_isolation(false), verus_spec(r =>
        requires
            old(self).wf(),
            old(evf).ok(&old(self).store),
            old(evf).visit@.len() > 0,
            cur == old(evf).visit@.last(),
            cache_ok(&old(self).store, old(eval_cache)@),
            old(evf).pending(cur),
            ck == old(self).store.kind_of(cur.idx()),
        ensures
            final(self).wf(),
            final(self).keeps(old(self)),
            final(evf).ok(&final(self).store),
            cache_ok(&final(self).store, final(eval_cache)@),
            r matches Step::Call(f) ==> f.ok(&final(self).store),
    ))]
    #[cfg_attr(verus_keep_ghost, verifier::exec_allows_no_decreases_clause)]
    fn revisit_term(
        &mut self,
        evf: &mut EvFrame,
        eval_cache: &mut EvalCache,
        cur: Term,
        ck: Kind,
    ) -> Step {
        proof! {
            use_collections();
            axiom_term_lists_are_keys();
            broadcast use vstd::std_specs::hash::group_hash_axioms;
            broadcast use vstd::std_specs::btree::group_btree_axioms;
            assert(self.store.has(cur));
            self.store.lemma_children(cur);
            self.store.lemma_shape(cur);
            lemma_top_open(evf, &self.store);
        }
        proof_decl! { let ghost f0 = *evf; let ghost before = *self; }
        let children = copy_of(self.store.children(cur));
        let mut cchildren: Vec<Option<Term>> = Vec::with_capacity(children.len());
        let mut cchanged = false;
        #[cfg_attr(verus_keep_ghost, verus_spec(invariant
            cchildren@.len() == i,
            cchanged ==> i > 0,
            forall|j: int| 0 <= j < i ==> #[trigger] cchildren@[j]
                == (if evf.valued(children@[j]) { evf.visited@[children@[j]] } else { None }),
            forall|j: int| 0 <= j < i ==> ((#[trigger] cchildren@[j]) matches Some(v) ==> self.store.has(v)),
        ))]
        for i in 0..children.len() {
            let cp = children[i];
            let v = match evf.visited.get(&cp) {
                Some(&Some(v)) => Some(v),
                _ => None,
            };
            if let Some(v) = v {
                cchanged = cchanged || v != cp;
            }
            cchildren.push(v);
        }
        let mut evaluated: Option<Term> = None;
        let mut can_evaluate = true;
        // the children put on the work list here
        proof_decl! { let ghost mut pushed: Seq<Term> = Seq::empty(); }
        proof! { assert(evf.visit@ =~= f0.visit@ + pushed); }
        match ck {
            Kind::Node(NodeKind::Apply | NodeKind::ApplyOpaque) => {
                let args = match all_values(&cchildren) {
                    Some(args) => args,
                    None => children_first("an application"),
                };
                proof! {
                    assert forall|j: int| 0 <= j < args@.len() implies self.store.has(#[trigger] args@[j]) by {
                        assert(cchildren@[j] == Some(args@[j]));
                    }
                }
                if self.store.kind(args[0]) == Kind::PROGRAM_CONST {
                    let cached = eval_cache.get(&args).copied();
                    if let Some(r) = cached {
                        evaluated = r;
                    } else {
                        let mut new_ctx = Ctx::new();
                        evaluated = self.evaluate_program_internal(&args, &mut new_ctx);
                        proof! {
                            lemma_frame_kept(&f0, &self.store, &before.store);
                            lemma_cache_kept(&self.store, &before.store, eval_cache@);
                        }
                        if let Some(ev) = evaluated {
                            // a body that needs substitution is evaluated
                            // at a new level
                            if !self.store.is_ground(ev) && !new_ctx.is_empty() {
                                return Step::Call(EvFrame::new(ev, new_ctx, Some(args)));
                            }
                        }
                        // otherwise the result, or the failure, is final
                        eval_cache.insert(args, evaluated);
                    }
                }
            }
            Kind::Eval(EvalOp::IfThenElse) => {
                let cond = match cchildren[0] {
                    Some(c) => match self.store.lit(c) {
                        Some(Lit::Bool(b)) => Some(*b),
                        _ => None,
                    },
                    None => None,
                };
                if let Some(b) = cond {
                    // only the branch taken is evaluated
                    let index = if b { 1 } else { 2 };
                    match cchildren[index] {
                        None => {
                            can_evaluate = false;
                            evf.visit.push(children[index]);
                            proof! {
                                pushed = pushed.push(children@[index as int]);
                                assert(evf.visit@ =~= f0.visit@ + pushed);
                            }
                        }
                        Some(v) => evaluated = Some(v),
                    }
                } else {
                    // Both branches are evaluated, so that substitution
                    // into them is complete.
                    #[cfg_attr(verus_keep_ghost, verus_spec(invariant
                        evf.visited@ == f0.visited@,
                        evf.init == f0.init && evf.ctx == f0.ctx && evf.result_key == f0.result_key,
                        evf.visit@ == f0.visit@ + pushed,
                        can_evaluate ==> pushed.len() == 0,
                        forall|j: int| 0 <= j < pushed.len() ==> self.store.has(#[trigger] pushed[j])
                            && pushed[j].idx() < cur.idx(),
                    ))]
                    for i in 1..3 {
                        if cchildren[i].is_none() {
                            evf.visit.push(children[i]);
                            can_evaluate = false;
                            proof! {
                                pushed = pushed.push(children@[i as int]);
                                assert(evf.visit@ =~= f0.visit@ + pushed);
                            }
                        }
                    }
                }
            }
            Kind::Eval(op) => {
                let args = match all_values(&cchildren) {
                    Some(args) => args,
                    None => children_first("an operator"),
                };
                proof! {
                    assert forall|j: int| 0 <= j < args@.len() implies self.store.has(#[trigger] args@[j]) by {
                        assert(cchildren@[j] == Some(args@[j]));
                    }
                }
                evaluated = self.evaluate_literal_op_internal(op, &args);
                proof! {
                    lemma_frame_kept(&f0, &self.store, &before.store);
                    lemma_cache_kept(&self.store, &before.store, eval_cache@);
                }
                if self.is_fatal() {
                    return Step::Fatal;
                }
            }
            _ => {}
        }
        if can_evaluate {
            let ev = match evaluated {
                Some(ev) => ev,
                None => {
                    if cchanged {
                        let args = values_or(&cchildren, &children);
                        proof_decl! { let ghost mid = *self; }
                        let made = self.store.mk(ck, &args);
                        proof! {
                            self.lemma_stored(&mid);
                            lemma_frame_kept(&f0, &self.store, &mid.store);
                            lemma_cache_kept(&self.store, &mid.store, eval_cache@);
                        }
                        made
                    } else {
                        cur
                    }
                }
            };
            proof! { assert(pushed.len() == 0 ==> f0.visit@ + pushed =~= f0.visit@); }
            evf.settle(cur, ev);
            proof! { lemma_settle(&f0, evf, &self.store, ev); }
        }
        proof! {
            if !can_evaluate {
                assert(evf.visited@ =~= f0.visited@.insert(cur, None));
                lemma_grow(&f0, evf, &self.store, pushed);
            }
        }
        Step::Next
    }

    /// Whether a plugin may evaluate terms.
    #[cfg_attr(verus_keep_ghost, verus_verify(external_body))]
    fn has_eval_plugin(&self) -> bool {
        self.eval_plugin.0.is_some()
    }

    /// Whether the run is over; see [`Checker::take_fatal`].
    #[cfg_attr(verus_keep_ghost, verus_verify(external_body))]
    fn is_fatal(&self) -> bool {
        self.fatal.is_some()
    }

    /// The plugin's value of `e`, if a plugin evaluates it.
    ///
    /// Trusted: a plugin is code that Verus does not see.
    #[cfg_attr(verus_keep_ghost, verus_verify(external_body), verus_spec(r =>
        requires old(self).wf(), old(self).has(e), old(self).binds(ctx@),
        ensures
            final(self).wf(),
            final(self).keeps(old(self)),
            r matches Some(t) ==> final(self).has(t),
    ))]
    fn plugin_evaluate(&mut self, e: Term, ctx: &Ctx) -> Option<Term> {
        let mut plugin = self.eval_plugin.0.take()?;
        let ret = if plugin.has_evaluation(self, e) {
            plugin.evaluate(self, e, ctx)
        } else {
            None
        };
        self.eval_plugin.0 = Some(plugin);
        ret
    }

    /// What the plugin makes of applying the program `children[0]` to the
    /// other arguments, if there is a plugin and it evaluates that program.
    ///
    /// Trusted: a plugin is code that Verus does not see.
    #[cfg_attr(verus_keep_ghost, verus_verify(external_body), verus_spec(r =>
        requires
            old(self).wf(),
            old(self).has_all(children@),
            children@.len() >= 1,
            old(self).binds(old(new_ctx)@),
        ensures
            final(self).wf(),
            final(self).keeps(old(self)),
            final(self).binds(final(new_ctx)@),
            r matches Some(Some(t)) ==> final(self).has(t),
    ))]
    fn plugin_evaluate_program(
        &mut self,
        children: &[Term],
        new_ctx: &mut Ctx,
    ) -> Option<Option<Term>> {
        let mut plugin = self.eval_plugin.0.take()?;
        let handles = plugin.has_evaluation(self, children[0]);
        let ret = handles.then(|| plugin.evaluate_program(self, children, new_ctx));
        self.eval_plugin.0 = Some(plugin);
        ret
    }

    /// The type of `e`, if it has one ([`Checker::get_type`] without a
    /// message).
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires old(self).wf(), old(self).has(e),
        ensures
            final(self).wf(),
            final(self).keeps(old(self)),
            r matches Some(t) ==> final(self).has(t),
    ))]
    #[cfg_attr(verus_keep_ghost, verifier::exec_allows_no_decreases_clause)]
    fn type_of(&mut self, e: Term) -> Option<Term> {
        self.get_type(e, None)
    }

    /// Whether every term is ground.
    #[cfg_attr(verus_keep_ghost, verifier::loop_isolation(false), verus_spec(r =>
        requires self.wf(), self.has_all(ts@),
        ensures r == forall|j: int| 0 <= j < ts@.len() ==> tree_is_ground(self.store.tree((#[trigger] ts@[j]).idx())),
    ))]
    fn all_ground(&self, ts: &[Term]) -> bool {
        #[cfg_attr(verus_keep_ghost, verus_spec(invariant
            forall|j: int| 0 <= j < i ==> tree_is_ground(self.store.tree((#[trigger] ts@[j]).idx())),
        ))]
        for i in 0..ts.len() {
            if !self.store.is_ground(ts[i]) {
                return false;
            }
        }
        true
    }

    /// Whether one of the terms after the first is evaluatable.
    #[cfg_attr(verus_keep_ghost, verifier::loop_isolation(false), verus_spec(
        requires self.wf(), self.has_all(ts@),
    ))]
    fn any_argument_evaluatable(&self, ts: &[Term]) -> bool {
        for i in 1..ts.len() {
            if self.store.is_evaluatable(ts[i]) {
                return true;
            }
        }
        false
    }

    /// Whether every term is a literal.
    #[cfg_attr(verus_keep_ghost, verifier::loop_isolation(false), verus_spec(r =>
        requires self.wf(), self.has_all(ts@),
        ensures r == forall|j: int| 0 <= j < ts@.len() ==> self.store.kind_of((#[trigger] ts@[j]).idx()) is Lit,
    ))]
    fn all_literals(&self, ts: &[Term]) -> bool {
        #[cfg_attr(verus_keep_ghost, verus_spec(invariant
            forall|j: int| 0 <= j < i ==> self.store.kind_of((#[trigger] ts@[j]).idx()) is Lit,
        ))]
        for i in 0..ts.len() {
            if !matches!(self.store.kind(ts[i]), Kind::Lit(_)) {
                return false;
            }
        }
        true
    }

    /// Applies the program `args[0]` to the other arguments and evaluates
    /// the result. Returns the unevaluated application if no case matches.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires old(self).wf(), old(self).has_all(args@), args@.len() >= 1,
        ensures
            final(self).wf(),
            final(self).keeps(old(self)),
            final(self).has(r),
    ))]
    pub fn evaluate_program_app(&mut self, args: &[Term]) -> Term {
        proof! {
            use_collections();
            broadcast use vstd::std_specs::hash::group_hash_axioms;
            broadcast use vstd::std_specs::btree::group_btree_axioms;
        }
        let mut new_ctx = Ctx::new();
        match self.evaluate_program_internal(args, &mut new_ctx) {
            Some(ret) => self.evaluate(ret, &new_ctx),
            None => {
                proof_decl! { let ghost before = *self; }
                let t = self.store.mk(Kind::APPLY, args);
                proof! { self.lemma_stored(&before); }
                t
            }
        }
    }

    /// Finds the first case of the program `children[0]` that matches the
    /// arguments. Returns the case's body and fills `new_ctx` with the
    /// match. Returns `None` if the arguments are not ground values or no
    /// case matches.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires
            old(self).wf(),
            old(self).has_all(children@),
            // the first is the program's symbol
            children@.len() >= 1,
            old(self).binds(old(new_ctx)@),
        ensures
            final(self).wf(),
            final(self).keeps(old(self)),
            final(self).binds(final(new_ctx)@),
            r matches Some(t) ==> final(self).has(t),
    ))]
    pub(crate) fn evaluate_program_internal(
        &mut self,
        children: &[Term],
        new_ctx: &mut Ctx,
    ) -> Option<Term> {
        if !self.all_ground(children) {
            return None;
        }
        // Arguments that are themselves stuck, or are unapplied programs,
        // make the application stuck.
        if self.any_argument_evaluatable(children) {
            return None;
        }
        let hd = children[0];
        if let Some(ret) = self.plugin_evaluate_program(children, new_ctx) {
            return ret;
        }
        self.stats.count_program(hd);
        let Some(prog) = self.get_program(hd) else {
            let msg = self.msg_no_program(hd);
            self.warn(&msg);
            return None;
        };
        match matching::match_cases(&self.store, prog, children, new_ctx) {
            CaseMatch::Body(body) => Some(body),
            CaseMatch::BadArity(pat) => {
                let msg1 = self.msg_bad_arity(pat);
                let msg2 = self.msg_arguments(children);
                self.warn(&msg1);
                self.warn(&msg2);
                None
            }
            CaseMatch::NoCase => None,
        }
    }

    /// Applies the `eo::` operator to the arguments. Returns the application
    /// itself if it does not evaluate.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires
            old(self).wf(),
            old(self).has_all(args@),
            op == EvalOp::IfThenElse ==> args@.len() >= 3,
        ensures
            final(self).wf(),
            final(self).keeps(old(self)),
            final(self).has(r),
    ))]
    #[cfg_attr(verus_keep_ghost, verifier::exec_allows_no_decreases_clause)]
    pub fn evaluate_literal_op(&mut self, op: EvalOp, args: &[Term]) -> Term {
        match self.evaluate_literal_op_internal(op, args) {
            Some(ret) => ret,
            None => {
                proof_decl! { let ghost before = *self; }
                let t = self.store.mk(Kind::Eval(op), args);
                proof! { self.lemma_stored(&before); }
                t
            }
        }
    }

    /// The nil terminator of `op` for lists whose type (or, without
    /// `tinst_list_arg`, whose element type) is `tinst`.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires
            old(self).wf(),
            old(self).has(op),
            old(self).has(nil),
            tinst matches Some(t) ==> old(self).has(t),
        ensures
            final(self).wf(),
            final(self).keeps(old(self)),
            r matches Some(t) ==> final(self).has(t),
            // a terminator that does not depend on a type is the terminator
            old(self).store.kind_of(nil.idx()) != Kind::Node(NodeKind::Parameterized)
                ==> r == Some(nil) && final(self).store == old(self).store,
    ))]
    #[cfg_attr(verus_keep_ghost, verifier::exec_allows_no_decreases_clause)]
    fn evaluate_nil(
        &mut self,
        op: Term,
        nil: Term,
        is_left: bool,
        tinst: Option<Term>,
        tinst_list_arg: bool,
    ) -> Option<Term> {
        proof! {
            use_collections();
            broadcast use vstd::std_specs::hash::group_hash_axioms;
            broadcast use vstd::std_specs::btree::group_btree_axioms;
        }
        if self.store.kind(nil) != Kind::PARAMETERIZED {
            // the terminator does not depend on the type
            return Some(nil);
        }
        let tinst = match tinst {
            Some(t) if self.store.is_ground(t) => t,
            _ => return None,
        };
        let top = self.type_of(op)?;
        // For a right associative operator of type (-> T L L), the element
        // type is the first argument type and the list type the second; for
        // a left associative one, of type (-> L T L), the other way round.
        // Ethos takes these children whatever the type looks like: for
        // (-> T L) the "second argument type" is the first child of L. Where
        // there is no such child Ethos reads past the end; here the
        // terminator is then not found.
        let src = if is_left == tinst_list_arg {
            *self.store.children(top).first()?
        } else {
            let rest = *self.store.children(top).get(1)?;
            *self.store.children(rest).first()?
        };
        let mut ctx = Ctx::new();
        let mut visited = HashSet::new();
        if !matching::match_terms(&self.store, src, tinst, &mut ctx, &mut visited) {
            return None;
        }
        // a parameterized term is its parameters and its body
        proof! { self.store.lemma_shape(nil); }
        let body = self.store.child(nil, 1);
        Some(self.evaluate(body, &ctx))
    }

    /// The elements of the `op`-list `e`, and its tail. With `check_nil`,
    /// the tail must be that term; otherwise this warns and returns `None`.
    #[cfg_attr(verus_keep_ghost, verifier::loop_isolation(false), verus_spec(r =>
        requires
            old(self).wf(),
            old(self).has(e),
            old(self).has(op),
            check_nil matches Some(n) ==> old(self).has(n),
            old(self).has_all(old(children)@),
        ensures
            final(self).unchanged(old(self)),
            final(self).has_all(final(children)@),
            // a list is no longer than the store is large
            final(children)@.len() <= old(children)@.len() + u32::MAX,
            r matches Some(t) ==> final(self).has(t),
            // the elements and the tail are those of the tree
            trees(&final(self).store, final(children)@) == trees(&final(self).store, old(children)@)
                + elems(final(self).store.tree(op.idx()), is_left, final(self).store.tree(e.idx())),
            r matches Some(t) ==> final(self).store.tree(t.idx())
                == tail_of(final(self).store.tree(op.idx()), is_left, final(self).store.tree(e.idx())),
            // and with a terminator given, there is a result exactly for a list
            match check_nil {
                Some(nil) => r is Some == is_list(
                    final(self).store.tree(op.idx()),
                    final(self).store.tree(nil.idx()),
                    is_left,
                    final(self).store.tree(e.idx()),
                ),
                None => r is Some,
            },
    ))]
    fn get_nary_children(
        &mut self,
        e: Term,
        op: Term,
        check_nil: Option<Term>,
        children: &mut Vec<Term>,
        is_left: bool,
    ) -> Option<Term> {
        let orig = e;
        let mut e = e;
        proof! { Term::lemma_idx_range(orig); }
        proof_decl! { let ghost f = self.store.tree(op.idx()); let ghost s = self.store; }
        proof! { assert(trees(&s, children@) + Seq::<Tree>::empty() =~= trees(&s, children@)); }
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant
                self.store == s,
                self.has(e),
                0 < e.idx(),
                self.has_all(children@),
                children@.len() + e.idx() <= old(children)@.len() + orig.idx(),
                trees(&s, children@) + elems(f, is_left, s.tree(e.idx()))
                    == trees(&s, old(children)@) + elems(f, is_left, s.tree(orig.idx())),
                tail_of(f, is_left, s.tree(e.idx())) == tail_of(f, is_left, s.tree(orig.idx())),
            decreases e.idx(),
        ))]
        while let Some((head, tail)) = self.nary_step(e, op, is_left) {
            proof_decl! { let ghost before = children@; let ghost cur = e; }
            children.push(head);
            e = tail;
            proof! {
                assert(trees(&s, children@) =~= trees(&s, before) + seq![s.tree(head.idx())]);
                assert(trees(&s, children@) + elems(f, is_left, s.tree(tail.idx()))
                    =~= trees(&s, before) + elems(f, is_left, s.tree(cur.idx())));
            }
        }
        proof! {
            assert(elems(f, is_left, s.tree(e.idx())) =~= Seq::<Tree>::empty());
            assert(trees(&s, children@) + Seq::<Tree>::empty() =~= trees(&s, children@));
            if check_nil is Some && s.tree(e.idx()) == s.tree(check_nil->0.idx()) {
                s.theorem_same_tree_same_term(e, check_nil->0);
            }
        }
        if let Some(nil) = check_nil {
            if e != nil {
                let msg = self.msg_not_a_list(nil, orig);
                self.warn(&msg);
                return None;
            }
        }
        Some(e)
    }

    /// If `e` is `(op head tail)` (or `(op tail head)` when left
    /// associative), its head and tail.
    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires self.wf(), self.has(e), self.has(op),
        ensures
            r matches Some((head, tail)) ==> self.has(head) && self.has(tail)
                && 0 < head.idx() < e.idx() && 0 < tail.idx() < e.idx(),
            // it is `uncons` on the trees
            (match r {
                Some((head, tail)) => Some((self.store.tree(head.idx()), self.store.tree(tail.idx()))),
                None => None,
            }) == uncons(self.store.tree(op.idx()), is_left, self.store.tree(e.idx())),
    ))]
    fn nary_step(&self, e: Term, op: Term, is_left: bool) -> Option<(Term, Term)> {
        let s = &self.store;
        proof! {
            s.lemma_children(e);
            if s.is_compound(e.idx()) {
                s.lemma_tree_compound(e);
            } else {
                s.lemma_tree_leaf(e);
            }
        }
        if s.kind(e) != Kind::APPLY || s.num_children(e) != 2 {
            return None;
        }
        let cop = s.child(e, 0);
        proof! {
            s.lemma_children(cop);
            if s.is_compound(cop.idx()) {
                s.lemma_tree_compound(cop);
            } else {
                s.lemma_tree_leaf(cop);
            }
        }
        if s.kind(cop) != Kind::APPLY || s.num_children(cop) != 2 || s.child(cop, 0) != op {
            proof! {
                if s.kind_of(cop.idx()) == Kind::APPLY && s.kids(cop.idx()).len() == 2 {
                    // another head: another tree
                    if s.tree(s.kids(cop.idx())[0].idx()) == s.tree(op.idx()) {
                        s.theorem_same_tree_same_term(s.kids(cop.idx())[0], op);
                    }
                }
            }
            return None;
        }
        let (a, b) = (s.child(cop, 1), s.child(e, 1));
        Some(if is_left { (b, a) } else { (a, b) })
    }

    /// Whether `e` is an `op`-list ending in `nil`.
    #[cfg_attr(verus_keep_ghost, verifier::loop_isolation(false), verus_spec(r =>
        requires self.wf(), self.has(e), self.has(op), self.has(nil),
        ensures r == is_list(self.store.tree(op.idx()), self.store.tree(nil.idx()), is_left, self.store.tree(e.idx())),
    ))]
    fn is_nary_list(&self, e: Term, op: Term, nil: Term, is_left: bool) -> bool {
        proof_decl! { let ghost orig = e; let ghost f = self.store.tree(op.idx()); }
        let mut e = e;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant
                self.has(e),
                tail_of(f, is_left, self.store.tree(e.idx())) == tail_of(f, is_left, self.store.tree(orig.idx())),
            decreases e.idx(),
        ))]
        while let Some((_, tail)) = self.nary_step(e, op, is_left) {
            e = tail;
        }
        proof! {
            if self.store.tree(e.idx()) == self.store.tree(nil.idx()) {
                self.store.theorem_same_tree_same_term(e, nil);
            }
        }
        e == nil
    }

    /// The `n`-th tail of the `op`-list `e`, which has at least `n`
    /// elements.
    #[cfg_attr(verus_keep_ghost, verifier::loop_isolation(false), verus_spec(r =>
        requires self.wf(), self.has(e), self.has(op),
        ensures
            self.has(r),
            self.store.tree(r.idx()) == nth_tail(self.store.tree(op.idx()), is_left, self.store.tree(e.idx()), n as nat),
    ))]
    fn get_nary_nth_tail(&self, e: Term, op: Term, is_left: bool, n: usize) -> Term {
        proof_decl! { let ghost orig = e; let ghost f = self.store.tree(op.idx()); }
        let mut e = e;
        #[cfg_attr(verus_keep_ghost, verus_spec(invariant
            self.has(e),
            nth_tail(f, is_left, self.store.tree(e.idx()), (n - _i) as nat)
                == nth_tail(f, is_left, self.store.tree(orig.idx()), n as nat),
        ))]
        for _i in 0..n {
            match self.nary_step(e, op, is_left) {
                Some((_, tail)) => e = tail,
                None => break,
            }
        }
        e
    }

    /// Puts the elements `hargs` in front of the `op`-list `ret`.
    #[cfg_attr(verus_keep_ghost, verifier::loop_isolation(false), verus_spec(r =>
        requires
            old(self).wf(),
            old(self).has(op),
            old(self).has(ret),
            old(self).has_all(hargs@),
        ensures
            final(self).wf(),
            final(self).keeps(old(self)),
            final(self).has(r),
            final(self).grew_from(old(self)),
            // the list built is `build` on the trees, unless the store is
            // full, when a term made is a placeholder
            final(self).store.spec_limit() is None ==> final(self).store.tree(r.idx()) == build(
                old(self).store.tree(op.idx()),
                is_left,
                trees(&old(self).store, hargs@),
                old(self).store.tree(ret.idx()),
            ),
    ))]
    fn prepend_nary_children(
        &mut self,
        op: Term,
        ret: Term,
        hargs: &[Term],
        is_left: bool,
    ) -> Term {
        proof_decl! {
            let ghost s0 = self.store;
            let ghost f = s0.tree(op.idx());
            let ghost ts = trees(&s0, hargs@);
            let ghost tail = s0.tree(ret.idx());
        }
        let mut ret = ret;
        // from the last element to the first
        let mut i = hargs.len();
        proof! {
            self.store.lemma_extends_itself();
            assert(ts.subrange(i as int, ts.len() as int) =~= Seq::<Tree>::empty());
        }
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant
                self.wf(),
                self.keeps(old(self)),
                self.store.extends(&s0),
                s0.spec_limit() is Some ==> self.store.spec_limit() is Some,
                self.has(ret),
                i <= hargs@.len(),
                self.store.spec_limit() is None ==> self.store.tree(ret.idx())
                    == build(f, is_left, ts.subrange(i as int, ts.len() as int), tail),
            decreases i,
        ))]
        while i > 0 {
            i -= 1;
            let h = hargs[i];
            proof_decl! { let ghost before = *self; let ghost rest = ret; }
            ret = if is_left {
                let c1 = self.store.mk_apply(op, ret);
                proof_decl! {
                    self.lemma_stored(&before);
                    let ghost between = *self;
                }
                let c2 = self.store.mk_apply(c1, h);
                proof! {
                    self.lemma_stored(&between);
                    lemma_cons_built(&s0, &before.store, &between.store, &self.store, op, h, rest, c1, c2, true);
                }
                c2
            } else {
                let c1 = self.store.mk_apply(op, h);
                proof_decl! {
                    self.lemma_stored(&before);
                    let ghost between = *self;
                }
                let c2 = self.store.mk_apply(c1, ret);
                proof! {
                    self.lemma_stored(&between);
                    lemma_cons_built(&s0, &before.store, &between.store, &self.store, op, h, rest, c1, c2, false);
                }
                c2
            };
            proof! {
                if self.store.spec_limit() is None {
                    let sub = ts.subrange(i as int, ts.len() as int);
                    assert(sub[0] == s0.tree(h.idx()));
                    assert(sub.drop_first() =~= ts.subrange(i + 1, ts.len() as int));
                }
            }
        }
        proof! { assert(ts.subrange(0, ts.len() as int) =~= ts); }
        ret
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires old(self).wf(),
        ensures
            final(self).wf(),
            final(self).keeps(old(self)),
            final(self).has(r),
            final(self).grew_from(old(self)),
            !final(self).is_full() ==> final(self).is_numeral(r, n as int),
    ))]
    fn mk_usize(&mut self, n: usize) -> Term {
        self.mk_numeral(Integer::from(n))
    }

    /// Stops the run: evaluating `k` needs an argument that `args` lacks.
    /// Ethos reads past the end of its argument vector here, which is
    /// undefined behaviour and usually ends in a segmentation fault.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires old(self).wf(), old(self).has_all(args@),
        ensures
            r is None,
            final(self).unchanged(old(self)),
    ))]
    fn missing_argument(&mut self, k: EvalOp, args: &[Term]) -> Option<Term> {
        if self.fatal.is_none() {
            self.fatal = Some(self.msg_too_few_arguments(k, args));
        }
        None
    }

    /// Applies the literal operator `k` to literals: [`Lit::evaluate`] on
    /// their values, and the literal for its result.
    #[cfg_attr(verus_keep_ghost, verifier::loop_isolation(false), verus_spec(r =>
        requires
            old(self).wf(),
            old(self).has_all(args@),
            forall|j: int| 0 <= j < args@.len() ==> old(self).store.kind_of((#[trigger] args@[j]).idx()) is Lit,
        ensures
            final(self).wf(),
            final(self).keeps(old(self)),
            r matches Some(t) ==> final(self).has(t),
            // exactly the specification, for the number of arguments the
            // operator takes; unless the store is full, when the term made
            // is a placeholder
            is_lit_op(k) && args@.len() == lit_arity(k) && short_args(&old(self).store, args@)
                && final(self).store.spec_limit() is None ==> (match r {
                    Some(t) => Some(final(self).store.value(t)@) == lit_spec(k, values(&old(self).store, args@))
                        && final(self).store.is_lit(t, final(self).store.value(t)),
                    None => lit_spec(k, values(&old(self).store, args@)) is None,
                }),
    ))]
    fn evaluate_on_literals(&mut self, k: EvalOp, args: &[Term]) -> Option<Term> {
        proof_decl! { let ghost start = *self; }
        if !arity_ok(k, args.len()) {
            let msg = self.msg_wrong_arity(k, args);
            self.warn(&msg);
            return None;
        }
        let mut lits: Vec<&Lit> = Vec::new();
        #[cfg_attr(verus_keep_ghost, verus_spec(invariant
            forall|j: int| 0 <= j < lits@.len() ==> (#[trigger] lits@[j]).wf(),
            lits@.len() == i,
            forall|j: int| 0 <= j < i ==> *(#[trigger] lits@[j]) == self.store.value(args@[j]),
        ))]
        for i in 0..args.len() {
            if let Some(lit) = self.store.lit(args[i]) {
                proof! { self.store.lemma_lit(args@[i as int], *lit); }
                lits.push(lit);
            }
        }
        proof! {
            lemma_vals(lits@);
            assert(vals(lits@) =~= values(&self.store, args@));
            assert(pathos_term::short_strings(lits@) == short_args(&self.store, args@));
        }
        let eval = Lit::evaluate(k, lits.as_slice())?;
        proof_decl! { let ghost before = *self; }
        let t = self.store.mk_lit(eval);
        proof! {
            self.lemma_stored(&before);
            if self.store.spec_limit() is None {
                self.store.lemma_lit(t, eval);
            }
        }
        Some(t)
    }

    /// Applies the `eo::` operator to evaluated arguments. Returns `None`
    /// if it does not evaluate on them.
    ///
    /// An `eo::ite` comes with its three arguments: `mk_expr` checks the
    /// arity before it calls this, and `evaluate` handles `eo::ite` itself.
    #[cfg_attr(verus_keep_ghost, verifier::loop_isolation(false), verus_spec(r =>
        requires
            old(self).wf(),
            old(self).has_all(args@),
            k == EvalOp::IfThenElse ==> args@.len() >= 3,
        ensures
            final(self).wf(),
            final(self).keeps(old(self)),
            r matches Some(t) ==> final(self).has(t),
            // The operators on values compute their specification, exactly.
            // (When the store is full, the term made is a placeholder.)
            is_scalar_op(k) && args@.len() == scalar_arity(k) && short_args(&old(self).store, args@)
                && final(self).store.spec_limit() is None ==> (match r {
                    Some(t) => Some(final(self).store.value(t)@) == scalar_spec(&old(self).store, k, args@)
                        && final(self).store.is_lit(t, final(self).store.value(t)),
                    None => scalar_spec(&old(self).store, k, args@) is None,
                }),
    ))]
    #[cfg_attr(verus_keep_ghost, verifier::exec_allows_no_decreases_clause)]
    pub(crate) fn evaluate_literal_op_internal(
        &mut self,
        k: EvalOp,
        args: &[Term],
    ) -> Option<Term> {
        let first = *args.first()?;
        // These two may evaluate on non-ground arguments.
        match k {
            EvalOp::IfThenElse => {
                return match self.store.lit(first) {
                    // the branches may be non-ground
                    Some(Lit::Bool(b)) => Some(args[if *b { 1 } else { 2 }]),
                    // equal branches are not simplified
                    _ => None,
                };
            }
            EvalOp::Requires => {
                // (eo::requires t s r) is r when t and s are the same value,
                // whether or not r is ground.
                if self.store.is_ground(first) && !self.store.is_evaluatable(first) {
                    let Some(&second) = args.get(1) else {
                        return self.missing_argument(k, args);
                    };
                    if self.store.is_ground(second)
                        && !self.store.is_evaluatable(second)
                        && first == second
                    {
                        return match args.get(2) {
                            Some(&r) => Some(r),
                            None => self.missing_argument(k, args),
                        };
                    }
                }
                return None;
            }
            _ => {}
        }
        if !self.all_ground(args) {
            return None;
        }
        // These three look at their second argument unless the first is
        // stuck.
        if matches!(k, EvalOp::IsEq | EvalOp::Eq | EvalOp::Compare)
            && args.len() < 2
            && !self.store.is_evaluatable(first)
        {
            return self.missing_argument(k, args);
        }
        match k {
            // false exactly when the argument is stuck
            EvalOp::IsOk => return Some(self.mk_bool(!self.store.is_evaluatable(first))),
            // true when both arguments are the same value; false also when
            // one of them is stuck
            EvalOp::IsEq => {
                return Some(self.mk_bool(
                    !self.store.is_evaluatable(first)
                        && !self.store.is_evaluatable(args[1])
                        && first == args[1],
                ));
            }
            EvalOp::Eq => {
                // only compares values
                proof! {
                    self.store.lemma_evaluatable(first);
                    if args@.len() >= 2 {
                        self.store.lemma_evaluatable(args@[1]);
                    }
                }
                if !self.store.is_evaluatable(first) && !self.store.is_evaluatable(args[1]) {
                    let same = self.mk_bool(first == args[1]);
                    proof! { self.store.lemma_lit(same, Lit::Bool(first == args@[1])); }
                    return Some(same);
                }
                return None;
            }
            EvalOp::Hash => {
                if self.store.is_evaluatable(first) {
                    return None;
                }
                let h = self.get_hash(first);
                // Ethos keeps the low 32 bits
                return Some(self.mk_numeral(Integer::from(h as u32)));
            }
            EvalOp::Compare => {
                if self.store.is_evaluatable(first) || self.store.is_evaluatable(args[1]) {
                    return None;
                }
                let h1 = self.get_hash(args[0]);
                let h2 = self.get_hash(args[1]);
                return Some(self.mk_bool(h1 > h2));
            }
            EvalOp::IsZ
            | EvalOp::IsQ
            | EvalOp::IsBin
            | EvalOp::IsStr
            | EvalOp::IsBool
            | EvalOp::IsVar => {
                let kk = match k {
                    EvalOp::IsZ => Kind::NUMERAL,
                    EvalOp::IsQ => Kind::RATIONAL,
                    EvalOp::IsBin => Kind::BINARY,
                    EvalOp::IsStr => Kind::STRING,
                    EvalOp::IsBool => Kind::BOOLEAN,
                    _ => Kind::VARIABLE,
                };
                let is_kind = self.mk_bool(self.store.kind(first) == kk);
                proof! { self.store.lemma_lit(is_kind, Lit::Bool(self.store.kind_of(first.idx()) == kk)); }
                return Some(is_kind);
            }
            EvalOp::TypeOf => {
                if !self.store.is_evaluatable(first) {
                    if let Some(et) = self.type_of(first) {
                        if self.store.is_ground(et) {
                            return Some(et);
                        }
                    }
                }
            }
            EvalOp::NameOf => {
                if self.store.kind(first) == Kind::VARIABLE {
                    // `(eo::var)` is a variable without children. Ethos
                    // reads its first child all the same, past the end.
                    return match self.store.children(first).first() {
                        Some(&name) => Some(name),
                        None => self.missing_argument(k, args),
                    };
                }
            }
            EvalOp::DtSelectors => {
                // an ambiguous constructor comes with its type annotation
                let sym = if self.store.kind(first) == Kind::APPLY_OPAQUE {
                    // which is its head
                    proof! { self.store.lemma_shape(first); }
                    self.store.child(first, 0)
                } else {
                    first
                };
                return match self.app_info(sym) {
                    Some(ac)
                        if matches!(
                            ac.attr,
                            Attr::DatatypeConstructor | Attr::AmbDatatypeConstructor
                        ) =>
                    {
                        ac.cons
                    }
                    _ => None,
                };
            }
            EvalOp::DtConstructors => return self.evaluate_dt_constructors(first),
            _ => {}
        }
        // On literal values, run the literal evaluator. Symbols are not
        // values.
        if self.all_literals(args) {
            return self.evaluate_on_literals(k, args);
        }
        if !k.is_list_op() {
            return None;
        }
        self.evaluate_list_op(k, args)
    }

    #[cfg_attr(verus_keep_ghost, verifier::loop_isolation(false), verus_spec(r =>
        requires old(self).wf(), old(self).has(arg),
        ensures
            final(self).wf(),
            final(self).keeps(old(self)),
            r matches Some(t) ==> final(self).has(t),
    ))]
    #[cfg_attr(verus_keep_ghost, verifier::exec_allows_no_decreases_clause)]
    fn evaluate_dt_constructors(&mut self, arg: Term) -> Option<Term> {
        let mut sym = arg;
        // A parametric datatype is applied to its parameters; it is fully
        // applied when its type is Type.
        let mut is_param = false;
        if self.store.kind(sym) == Kind::APPLY {
            let fully_applied = match self.type_of(sym) {
                Some(t) => t == self.mk_type(),
                None => false,
            };
            if fully_applied {
                is_param = true;
                #[cfg_attr(verus_keep_ghost, verus_spec(
                    invariant self.has(sym),
                    decreases sym.idx(),
                ))]
                while self.store.kind(sym) == Kind::APPLY && self.store.num_children(sym) > 0 {
                    proof! { self.store.lemma_children(sym); }
                    sym = self.store.child(sym, 0);
                }
            }
        }
        let cons = match self.app_info(sym) {
            Some(ac) if ac.attr == Attr::Datatype => ac.cons?,
            _ => return None,
        };
        if !is_param {
            return Some(cons);
        }
        // the ambiguous constructors get the datatype as annotation
        let mut cargs = Vec::new();
        let cop = self.mk_list_cons();
        self.get_nary_children(cons, cop, None, &mut cargs, false);
        let mut cargsp = Vec::with_capacity(cargs.len());
        proof_decl! { let ghost start = *self; }
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant
                self.wf(),
                self.keeps(&start),
                self.has_all(cargsp@),
        ))]
        for i in 0..cargs.len() {
            let c = cargs[i];
            cargsp.push(if self.attribute_kind(c) == Attr::AmbDatatypeConstructor {
                proof_decl! { let ghost before = *self; }
                let t = self.store.mk(Kind::APPLY_OPAQUE, &[c, arg]);
                proof! { self.lemma_stored(&before); }
                t
            } else {
                c
            });
        }
        Some(self.mk_list(&cargsp))
    }

    /// Evaluates a list operator: `args[0]` is the list constructor.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires old(self).wf(), old(self).has_all(args@), args@.len() >= 1,
        ensures
            final(self).wf(),
            final(self).keeps(old(self)),
            r matches Some(t) ==> final(self).has(t),
            // The tables say whether the first argument builds lists, which
            // way they nest and what ends them. When the term that ends
            // them does not depend on a type, the result is the
            // specification's. (When it does, the terminator is found by
            // typing and evaluation, and `evaluate_list_op_with` says what
            // is proved, given the one found.)
            ({
                let head = list_head(&old(self).store, args@[0]);
                if old(self).app@.contains_key(head) && old(self).app@[head].attr.spec_is_list_nil()
                    && old(self).app@[head].cons is Some {
                    let nil = old(self).app@[head].cons->0;
                    old(self).store.kind_of(nil.idx()) != Kind::Node(NodeKind::Parameterized)
                        && k != EvalOp::ListSingletonIntro ==> list_ok(
                        &old(self).store,
                        &final(self).store,
                        k,
                        head,
                        nil,
                        old(self).app@[head].attr.spec_is_left_nil(),
                        args@,
                        r,
                    )
                } else {
                    r is None
                }
            }),
    ))]
    #[cfg_attr(verus_keep_ghost, verifier::exec_allows_no_decreases_clause)]
    fn evaluate_list_op(&mut self, k: EvalOp, args: &[Term]) -> Option<Term> {
        proof! {
            use_collections();
            broadcast use vstd::std_specs::hash::group_hash_axioms;
            broadcast use vstd::std_specs::btree::group_btree_axioms;
        }
        let mut op = args[0];
        // the attributes are on the operator inside (eo::_ params op)
        if self.store.kind(op) == Kind::PARAMETERIZED {
            proof! { self.store.lemma_shape(op); }
            op = self.store.child(op, 1);
        }
        let ac = self.app_info(op)?;
        let (ck, cons) = (ac.attr, ac.cons);
        if !ck.is_list_nil() {
            return None;
        }
        let cons = cons?;
        let is_left = ck.is_left_nil();
        if k == EvalOp::ListSingletonIntro {
            return self.evaluate_list_singleton_intro(op, cons, is_left, args);
        }
        // the nil terminator, which may depend on the type of args[1]
        let nil = if k == EvalOp::Nil {
            // eo::nil takes the type itself
            if args.len() < 2 && self.store.kind(cons) == Kind::PARAMETERIZED {
                return self.missing_argument(k, args);
            }
            return self.evaluate_nil(args[0], cons, is_left, args.get(1).copied(), false);
        } else if self.store.kind(cons) != Kind::PARAMETERIZED {
            cons
        } else if args.len() > 1 {
            // Operators whose second argument is an element, not a list,
            // infer the terminator from the element type.
            self.type_of(args[1]);
            let t = self.store.ty(args[1]);
            let tinst_list_arg = k != EvalOp::Cons && k != EvalOp::ListRepeat;
            self.evaluate_nil(args[0], cons, is_left, t, tinst_list_arg)?
        } else {
            return None;
        };
        self.evaluate_list_op_with(k, args, op, nil, is_left)
    }

    /// Evaluates a list operator other than `eo::nil` and
    /// `eo::list_singleton_intro` on lists of `op` that end in `nil`.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires
            k != EvalOp::Nil,
            old(self).wf(),
            old(self).has_all(args@),
            old(self).has(op),
            old(self).has(nil),
        ensures
            final(self).wf(),
            final(self).keeps(old(self)),
            r matches Some(t) ==> final(self).has(t),
            // given the terminator, the result is the specification's
            list_ok(&old(self).store, &final(self).store, k, op, nil, is_left, args@, r),
    ))]
    fn evaluate_list_op_with(
        &mut self,
        k: EvalOp,
        args: &[Term],
        op: Term,
        nil: Term,
        is_left: bool,
    ) -> Option<Term> {
        match k {
            EvalOp::Cons | EvalOp::ListConcat => {
                self.list_cons_or_concat(k, args, op, nil, is_left)
            }
            EvalOp::ListRepeat => self.list_repeat(k, args, op, nil, is_left),
            EvalOp::ListLength => self.list_length(k, args, op, nil, is_left),
            EvalOp::ListNth => self.list_nth(k, args, op, nil, is_left),
            EvalOp::ListFind => self.list_find(k, args, op, nil, is_left),
            EvalOp::ListErase | EvalOp::ListEraseAll => self.list_erase(k, args, op, nil, is_left),
            EvalOp::ListRev => self.list_rev(k, args, op, nil, is_left),
            EvalOp::ListSetof => self.list_setof(k, args, op, nil, is_left),
            EvalOp::ListMinclude | EvalOp::ListMeq => self.list_compare(k, args, op, nil, is_left),
            EvalOp::ListDiff | EvalOp::ListInter => {
                self.list_diff_or_inter(k, args, op, nil, is_left)
            }
            EvalOp::ListSingletonElim => self.list_singleton_elim(k, args, op, nil, is_left),
            _ => None,
        }
    }

    /// `(eo::cons op e t)` and `(eo::list_concat op t1 t2)`.
    #[cfg_attr(verus_keep_ghost, verifier::loop_isolation(false), verus_spec(r =>
        requires
            k == EvalOp::Cons || k == EvalOp::ListConcat,
            old(self).wf(),
            old(self).has_all(args@),
            old(self).has(op),
            old(self).has(nil),
        ensures
            final(self).wf(),
            final(self).keeps(old(self)),
            r matches Some(t) ==> final(self).has(t),
            list_ok(&old(self).store, &final(self).store, k, op, nil, is_left, args@, r),
    ))]
    fn list_cons_or_concat(
        &mut self,
        k: EvalOp,
        args: &[Term],
        op: Term,
        nil: Term,
        is_left: bool,
    ) -> Option<Term> {
        proof! {
            use_collections();
            broadcast use vstd::std_specs::hash::group_hash_axioms;
            broadcast use vstd::std_specs::btree::group_btree_axioms;
        }
        proof_decl! {
            let ghost s0 = self.store;
            let ghost f = s0.tree(op.idx());
            let ghost nl = s0.tree(nil.idx());
            let ghost a = trees(&s0, args@);
        }
        proof! { s0.lemma_extends_itself(); }
        let mut hargs = Vec::new();
        let is_concat = k == EvalOp::ListConcat;
        let tail_index: usize = if is_left { 1 } else { 2 };
        let head_index: usize = if is_left { 2 } else { 1 };
        let ret = arg!(self, k, args, if is_concat { tail_index } else { 2 });
        if !self.is_nary_list(ret, op, nil, is_left) {
            return None;
        }
        if k == EvalOp::Cons {
            hargs.push(arg!(self, k, args, 1));
            proof! {
                let es = trees(&s0, hargs@);
                assert(es =~= seq![a[1]]);
                assert(es.drop_first() =~= Seq::<Tree>::empty());
                assert(build(f, is_left, es, a[2]) == cons_tree(f, is_left, a[1], build(f, is_left, es.drop_first(), a[2])));
            }
        } else {
            let list = arg!(self, k, args, head_index);
            self.get_nary_children(list, op, Some(nil), &mut hargs, is_left)?;
            proof! { lemma_read(&s0, hargs@, elems(f, is_left, s0.tree(list.idx()))); }
            // nothing to rebuild when the tail is empty
            if ret == nil {
                proof! { lemma_build_elems(f, is_left, s0.tree(list.idx())); }
                return Some(arg!(self, k, args, head_index));
            }
        }
        Some(self.prepend_nary_children(op, ret, &hargs, is_left))
    }

    /// `(eo::list_repeat op e n)`: the list of `n` times `e`.
    #[cfg_attr(verus_keep_ghost, verifier::loop_isolation(false), verus_spec(r =>
        requires
            k == EvalOp::ListRepeat,
            old(self).wf(),
            old(self).has_all(args@),
            old(self).has(op),
            old(self).has(nil),
        ensures
            final(self).wf(),
            final(self).keeps(old(self)),
            r matches Some(t) ==> final(self).has(t),
            list_ok(&old(self).store, &final(self).store, k, op, nil, is_left, args@, r),
    ))]
    fn list_repeat(
        &mut self,
        k: EvalOp,
        args: &[Term],
        op: Term,
        nil: Term,
        is_left: bool,
    ) -> Option<Term> {
        proof! {
            use_collections();
            broadcast use vstd::std_specs::hash::group_hash_axioms;
            broadcast use vstd::std_specs::btree::group_btree_axioms;
        }
        proof_decl! {
            let ghost s0 = self.store;
            let ghost f = s0.tree(op.idx());
            let ghost nl = s0.tree(nil.idx());
            let ghost a = trees(&s0, args@);
        }
        proof! { s0.lemma_extends_itself(); }
        let n = arg!(self, k, args, 2);
        let count = self.store.lit(n);
        proof! {
            lemma_numeral_of(&s0, n);
            if count is Some {
                s0.lemma_lit(n, *count->0);
            }
        }
        let count = match count {
            Some(Lit::Numeral(i)) if i.fits_u32() => i.to_u32(),
            _ => return None,
        };
        let mut ret = nil;
        proof_decl! { let ghost start = *self; }
        proof! { assert(Seq::new(0, |i: int| a[1]) =~= Seq::<Tree>::empty()); }
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant
                self.wf(),
                self.keeps(&start),
                self.has(ret),
                self.store.extends(&s0),
                s0.spec_limit() is Some ==> self.store.spec_limit() is Some,
                self.store.spec_limit() is None ==> self.store.tree(ret.idx())
                    == build(f, is_left, Seq::new(_i as nat, |i: int| a[1]), nl),
        ))]
        for _i in 0..count {
            let elem = arg!(self, k, args, 1);
            proof_decl! { let ghost before = self.store; let ghost rest = ret; }
            let single = [elem];
            ret = self.prepend_nary_children(op, ret, &single, is_left);
            proof! {
                self.store.lemma_extends_twice(&before, &s0);
                if self.store.spec_limit() is None {
                    before.theorem_trees_are_kept(&s0, op);
                    before.theorem_trees_are_kept(&s0, elem);
                    let one = trees(&before, single@);
                    assert(one =~= seq![a[1]]);
                    assert(one.drop_first() =~= Seq::<Tree>::empty());
                    assert(build(f, is_left, one, before.tree(rest.idx()))
                        == cons_tree(f, is_left, a[1], build(f, is_left, one.drop_first(), before.tree(rest.idx()))));
                    let more = Seq::new((_i + 1) as nat, |i: int| a[1]);
                    assert(more.drop_first() =~= Seq::new(_i as nat, |i: int| a[1]));
                    assert(more[0] == a[1]);
                    assert(build(f, is_left, more, nl)
                        == cons_tree(f, is_left, more[0], build(f, is_left, more.drop_first(), nl)));
                }
            }
        }
        Some(ret)
    }

    /// `(eo::list_len op t)`.
    #[cfg_attr(verus_keep_ghost, verifier::loop_isolation(false), verus_spec(r =>
        requires
            k == EvalOp::ListLength,
            old(self).wf(),
            old(self).has_all(args@),
            old(self).has(op),
            old(self).has(nil),
        ensures
            final(self).wf(),
            final(self).keeps(old(self)),
            r matches Some(t) ==> final(self).has(t),
            list_ok(&old(self).store, &final(self).store, k, op, nil, is_left, args@, r),
    ))]
    fn list_length(
        &mut self,
        k: EvalOp,
        args: &[Term],
        op: Term,
        nil: Term,
        is_left: bool,
    ) -> Option<Term> {
        proof! {
            use_collections();
            broadcast use vstd::std_specs::hash::group_hash_axioms;
            broadcast use vstd::std_specs::btree::group_btree_axioms;
        }
        let mut hargs = Vec::new();
        let list = arg!(self, k, args, 1);
        self.get_nary_children(list, op, Some(nil), &mut hargs, is_left)?;
        Some(self.mk_usize(hargs.len()))
    }

    /// `(eo::list_nth op t n)`.
    #[cfg_attr(verus_keep_ghost, verifier::loop_isolation(false), verus_spec(r =>
        requires
            k == EvalOp::ListNth,
            old(self).wf(),
            old(self).has_all(args@),
            old(self).has(op),
            old(self).has(nil),
        ensures
            final(self).wf(),
            final(self).keeps(old(self)),
            r matches Some(t) ==> final(self).has(t),
            list_ok(&old(self).store, &final(self).store, k, op, nil, is_left, args@, r),
    ))]
    fn list_nth(
        &mut self,
        k: EvalOp,
        args: &[Term],
        op: Term,
        nil: Term,
        is_left: bool,
    ) -> Option<Term> {
        proof! {
            use_collections();
            broadcast use vstd::std_specs::hash::group_hash_axioms;
            broadcast use vstd::std_specs::btree::group_btree_axioms;
        }
        proof_decl! {
            let ghost s0 = self.store;
            let ghost f = s0.tree(op.idx());
            let ghost nl = s0.tree(nil.idx());
            let ghost a = trees(&s0, args@);
        }
        proof! { s0.lemma_extends_itself(); }
        let mut hargs = Vec::new();
        let n = arg!(self, k, args, 2);
        let index = self.store.lit(n);
        proof! {
            lemma_numeral_of(&s0, n);
            if index is Some {
                s0.lemma_lit(n, *index->0);
            }
        }
        let i = match index {
            Some(Lit::Numeral(i)) if i.fits_u32() => i.to_u32() as usize,
            _ => return None,
        };
        // all the elements are read, to check that this is a list
        let list = arg!(self, k, args, 1);
        self.get_nary_children(list, op, Some(nil), &mut hargs, is_left)?;
        proof! { lemma_read(&s0, hargs@, elems(f, is_left, s0.tree(list.idx()))); }
        hargs.get(i).copied()
    }

    /// `(eo::list_find op t e)`: the position of `e` in `t`, or -1.
    #[cfg_attr(verus_keep_ghost, verifier::loop_isolation(false), verus_spec(r =>
        requires
            k == EvalOp::ListFind,
            old(self).wf(),
            old(self).has_all(args@),
            old(self).has(op),
            old(self).has(nil),
        ensures
            final(self).wf(),
            final(self).keeps(old(self)),
            r matches Some(t) ==> final(self).has(t),
            list_ok(&old(self).store, &final(self).store, k, op, nil, is_left, args@, r),
    ))]
    fn list_find(
        &mut self,
        k: EvalOp,
        args: &[Term],
        op: Term,
        nil: Term,
        is_left: bool,
    ) -> Option<Term> {
        proof! {
            use_collections();
            broadcast use vstd::std_specs::hash::group_hash_axioms;
            broadcast use vstd::std_specs::btree::group_btree_axioms;
        }
        let mut hargs = Vec::new();
        let list = arg!(self, k, args, 1);
        self.get_nary_children(list, op, Some(nil), &mut hargs, is_left)?;
        proof_decl! {
            let ghost s0 = self.store;
            let ghost es = elems(s0.tree(op.idx()), is_left, s0.tree(list.idx()));
        }
        proof! { lemma_read(&s0, hargs@, es); }
        let elem = arg!(self, k, args, 2);
        let found = position(&hargs, elem);
        proof! {
            // terms that differ have trees that differ
            assert forall|j: int| 0 <= j < hargs@.len() && hargs@[j] != elem implies
                #[trigger] es[j] != s0.tree(elem.idx()) by {
                if s0.tree(hargs@[j].idx()) == s0.tree(elem.idx()) {
                    s0.theorem_same_tree_same_term(hargs@[j], elem);
                }
            }
            match found {
                Some(i) => lemma_find_at(es, s0.tree(elem.idx()), 0, i as int),
                None => lemma_find_none(es, s0.tree(elem.idx()), 0),
            }
        }
        match found {
            Some(i) => Some(self.mk_usize(i)),
            None => {
                let neg_one = match self.neg_one {
                    Some(t) => t,
                    None => self.mk_numeral(Integer::one().neg()),
                };
                self.neg_one = Some(neg_one);
                Some(neg_one)
            }
        }
    }

    /// `(eo::list_erase op t e)` and `(eo::list_erase_all op t e)`.
    #[cfg_attr(verus_keep_ghost, verifier::loop_isolation(false), verifier::rlimit(100), verus_spec(r =>
        requires
            k == EvalOp::ListErase || k == EvalOp::ListEraseAll,
            old(self).wf(),
            old(self).has_all(args@),
            old(self).has(op),
            old(self).has(nil),
        ensures
            final(self).wf(),
            final(self).keeps(old(self)),
            r matches Some(t) ==> final(self).has(t),
            list_ok(&old(self).store, &final(self).store, k, op, nil, is_left, args@, r),
    ))]
    fn list_erase(
        &mut self,
        k: EvalOp,
        args: &[Term],
        op: Term,
        nil: Term,
        is_left: bool,
    ) -> Option<Term> {
        proof! {
            use_collections();
            broadcast use vstd::std_specs::hash::group_hash_axioms;
            broadcast use vstd::std_specs::btree::group_btree_axioms;
        }
        let mut hargs = Vec::new();
        let list = arg!(self, k, args, 1);
        self.get_nary_children(list, op, Some(nil), &mut hargs, is_left)?;
        let is_all = k == EvalOp::ListEraseAll;
        let mut result = Vec::new();
        let mut change_index = 0;
        let mut change_size = 0;
        proof_decl! {
            let ghost at = *self;
            let ghost s0 = self.store;
            let ghost f = s0.tree(op.idx());
            let ghost nl = s0.tree(nil.idx());
            let ghost es = elems(f, is_left, s0.tree(list.idx()));
            // the element to erase, when it is there
            let ghost z = if args@.len() >= 3 { s0.tree(args@[2].idx()) } else { nl };
        }
        proof! {
            lemma_read(&s0, hargs@, es);
            assert(es.take(0) =~= Seq::<Tree>::empty());
            assert(trees(&s0, result@) =~= Seq::<Tree>::empty());
        }
        // (a loop without `break`, so that the proof knows how it ended)
        let mut i = 0;
        let mut stop = false;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant
                *self == at,
                self.has_all(result@),
                i <= hargs@.len(),
                change_index <= i,
                stop ==> !is_all && change_index == i && i >= 1,
                args@.len() >= 3 ==> (if is_all {
                    &&& trees(&s0, result@) == erase_all_rec(es.take(i as int), z)
                    &&& change_size <= result@.len()
                    &&& trees(&s0, result@).take(change_size as int) == erase_all_rec(es.take(change_index as int), z)
                    &&& forall|j: int| change_index <= j < i ==> es[j] != z
                } else if stop {
                    &&& es[i - 1] == z
                    &&& trees(&s0, result@) == es.take(i - 1)
                    &&& forall|j: int| 0 <= j < i - 1 ==> es[j] != z
                } else {
                    &&& change_index == 0
                    &&& trees(&s0, result@) == es.take(i as int)
                    &&& forall|j: int| 0 <= j < i ==> es[j] != z
                }),
            decreases hargs@.len() - i,
        ))]
        while i < hargs.len() && !stop {
            let h = hargs[i];
            let elem = arg!(self, k, args, 2);
            proof_decl! { let ghost before = result@; }
            proof! {
                assert(es[i as int] == s0.tree(h.idx()));
                if s0.tree(h.idx()) == z {
                    s0.theorem_same_tree_same_term(h, elem);
                }
                lemma_erase_all_step(es, z, i as int);
            }
            if h == elem {
                change_index = i + 1;
                if is_all {
                    change_size = result.len();
                    proof! { assert(trees(&s0, result@).take(change_size as int) =~= trees(&s0, result@)); }
                } else {
                    stop = true;
                    proof! { assert(es.take(i + 1 - 1) =~= es.take(i as int)); }
                }
            } else {
                result.push(h);
                proof! {
                    assert(trees(&s0, result@) =~= trees(&s0, before) + seq![es[i as int]]);
                    if is_all {
                        assert(trees(&s0, result@).take(change_size as int)
                            =~= trees(&s0, before).take(change_size as int));
                    }
                }
            }
            i += 1;
        }
        if change_index == 0 {
            proof! {
                if args@.len() >= 3 {
                    assert(es.take(es.len() as int) =~= es);
                    lemma_erase_none(es, z);
                    lemma_build_elems(f, is_left, s0.tree(list.idx()));
                }
            }
            return Some(arg!(self, k, args, 1));
        }
        // Keep the list after the last change as it is, and rebuild
        // only what comes before.
        proof_decl! { let ghost kept = trees(&s0, result@); let ghost whole = result@; }
        if is_all {
            result.truncate(change_size);
            proof! {
                if args@.len() >= 3 {
                    assert(result@ =~= whole.take(change_size as int));
                    assert(trees(&s0, result@) =~= kept.take(change_size as int));
                }
            }
        }
        let list = arg!(self, k, args, 1);
        let ret = self.get_nary_nth_tail(list, op, is_left, change_index);
        proof! {
            if args@.len() >= 3 {
                let c = change_index as int;
                let n = es.len() as int;
                lemma_nth_tail(f, is_left, s0.tree(list.idx()), change_index as nat);
                let rest = es.subrange(c, n);
                lemma_build_append(f, is_left, trees(&s0, result@), rest, nl);
                if is_all {
                    assert(es.take(n) =~= es);
                    assert(es =~= es.take(c) + rest);
                    lemma_erase_all_append(es.take(c), rest, z);
                    assert forall|j: int| 0 <= j < rest.len() implies rest[j] != z by {
                        assert(rest[j] == es[c + j]);
                    }
                    lemma_erase_none(rest, z);
                } else {
                    lemma_erase_at(es, z, c - 1);
                }
            }
        }
        Some(self.prepend_nary_children(op, ret, &result, is_left))
    }

    /// `(eo::list_rev op t)`.
    #[cfg_attr(verus_keep_ghost, verifier::loop_isolation(false), verus_spec(r =>
        requires
            k == EvalOp::ListRev,
            old(self).wf(),
            old(self).has_all(args@),
            old(self).has(op),
            old(self).has(nil),
        ensures
            final(self).wf(),
            final(self).keeps(old(self)),
            r matches Some(t) ==> final(self).has(t),
            list_ok(&old(self).store, &final(self).store, k, op, nil, is_left, args@, r),
    ))]
    fn list_rev(
        &mut self,
        k: EvalOp,
        args: &[Term],
        op: Term,
        nil: Term,
        is_left: bool,
    ) -> Option<Term> {
        proof! {
            use_collections();
            broadcast use vstd::std_specs::hash::group_hash_axioms;
            broadcast use vstd::std_specs::btree::group_btree_axioms;
        }
        let mut hargs = Vec::new();
        let list = arg!(self, k, args, 1);
        self.get_nary_children(list, op, Some(nil), &mut hargs, is_left)?;
        proof_decl! {
            let ghost s0 = self.store;
            let ghost es = elems(s0.tree(op.idx()), is_left, s0.tree(list.idx()));
        }
        proof! { lemma_read(&s0, hargs@, es); }
        reverse(hargs.as_mut_slice());
        proof! { assert(trees(&s0, hargs@) =~= es.reverse()); }
        Some(self.prepend_nary_children(op, nil, &hargs, is_left))
    }

    /// `(eo::list_setof op t)`: `t` without the later copies of its elements.
    #[cfg_attr(verus_keep_ghost, verifier::loop_isolation(false), verus_spec(r =>
        requires
            k == EvalOp::ListSetof,
            old(self).wf(),
            old(self).has_all(args@),
            old(self).has(op),
            old(self).has(nil),
        ensures
            final(self).wf(),
            final(self).keeps(old(self)),
            r matches Some(t) ==> final(self).has(t),
            list_ok(&old(self).store, &final(self).store, k, op, nil, is_left, args@, r),
    ))]
    fn list_setof(
        &mut self,
        k: EvalOp,
        args: &[Term],
        op: Term,
        nil: Term,
        is_left: bool,
    ) -> Option<Term> {
        proof! {
            use_collections();
            broadcast use vstd::std_specs::hash::group_hash_axioms;
            broadcast use vstd::std_specs::btree::group_btree_axioms;
        }
        let mut hargs = Vec::new();
        let list = arg!(self, k, args, 1);
        self.get_nary_children(list, op, Some(nil), &mut hargs, is_left)?;
        let mut seen = HashSet::new();
        let mut result = Vec::new();
        let mut change_index = 0;
        let mut change_size = 0;
        proof_decl! {
            let ghost s0 = self.store;
            let ghost f = s0.tree(op.idx());
            let ghost nl = s0.tree(nil.idx());
            let ghost es = elems(f, is_left, s0.tree(list.idx()));
        }
        proof! {
            lemma_read(&s0, hargs@, es);
            assert(es.take(0) =~= Seq::<Tree>::empty());
            assert(trees(&s0, result@) =~= Seq::<Tree>::empty());
            assert(es.subrange(0, 0) =~= Seq::<Tree>::empty());
            assert(trees(&s0, result@).take(0) + es.subrange(0, 0) =~= trees(&s0, result@));
        }
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant
                self.store == s0,
                self.has_all(result@),
                change_index <= i,
                // what was seen: the elements so far
                forall|t: Term| seen@.contains(t) <==> exists|j: int| 0 <= j < i && #[trigger] hargs@[j] == t,
                // the result so far is the plugin's on the elements so far;
                // up to the last change it is what will be rebuilt, and
                // since then every element was kept
                trees(&s0, result@) == setof_rec(es.take(i as int)),
                change_size <= result@.len(),
                trees(&s0, result@).take(change_size as int) == setof_rec(es.take(change_index as int)),
                trees(&s0, result@) == trees(&s0, result@).take(change_size as int)
                    + es.subrange(change_index as int, i as int),
                change_index == 0 ==> change_size == 0,
        ))]
        for i in 0..hargs.len() {
            let elem = hargs[i];
            proof_decl! { let ghost before = result@; let ghost was_seen = seen@.contains(elem); }
            proof! {
                // seen as a term is seen as a tree
                if es.take(i as int).contains(es[i as int]) {
                    let j = choose|j: int| 0 <= j < i && es.take(i as int)[j] == es[i as int];
                    s0.theorem_same_tree_same_term(hargs@[j], elem);
                }
                if was_seen {
                    let j = choose|j: int| 0 <= j < i && #[trigger] hargs@[j] == elem;
                    assert(es.take(i as int)[j] == es[i as int]);
                }
                lemma_setof_step(es, i as int);
            }
            if seen.insert(elem) {
                result.push(elem);
                proof! {
                    assert(trees(&s0, result@) =~= trees(&s0, before) + seq![es[i as int]]);
                    assert(trees(&s0, result@).take(change_size as int) =~= trees(&s0, before).take(change_size as int));
                    assert(es.subrange(change_index as int, i + 1)
                        =~= es.subrange(change_index as int, i as int) + seq![es[i as int]]);
                    assert(trees(&s0, result@) =~= trees(&s0, result@).take(change_size as int)
                        + es.subrange(change_index as int, i + 1));
                }
            } else {
                change_index = i + 1;
                change_size = result.len();
                proof! {
                    assert(trees(&s0, result@).take(change_size as int) =~= trees(&s0, result@));
                    assert(es.subrange(i + 1, i + 1) =~= Seq::<Tree>::empty());
                    assert(trees(&s0, result@) =~= trees(&s0, result@).take(change_size as int)
                        + es.subrange(i + 1, i + 1));
                }
            }
            proof! {
                assert forall|t: Term| seen@.contains(t) <==> exists|j: int| 0 <= j < i + 1 && #[trigger] hargs@[j] == t by {
                    if seen@.contains(t) && t != elem {
                        let j = choose|j: int| 0 <= j < i && #[trigger] hargs@[j] == t;
                        assert(0 <= j < i + 1 && hargs@[j] == t);
                    }
                    if t == elem {
                        assert(hargs@[i as int] == t);
                    }
                }
            }
        }
        proof! { assert(es.take(es.len() as int) =~= es); }
        if change_index == 0 {
            proof! {
                // nothing was seen twice: the set is the list
                assert(es.subrange(0, es.len() as int) =~= es);
                assert(Seq::<Tree>::empty() + es =~= es);
                assert(trees(&s0, result@).take(0) =~= Seq::<Tree>::empty());
                lemma_build_elems(f, is_left, s0.tree(list.idx()));
            }
            return Some(arg!(self, k, args, 1));
        }
        proof_decl! { let ghost kept = trees(&s0, result@); let ghost whole = result@; }
        result.truncate(change_size);
        let list = arg!(self, k, args, 1);
        let ret = self.get_nary_nth_tail(list, op, is_left, change_index);
        proof! {
            assert(result@ =~= whole.take(change_size as int));
            assert(trees(&s0, result@) =~= kept.take(change_size as int));
            lemma_nth_tail(f, is_left, s0.tree(list.idx()), change_index as nat);
            lemma_build_append(f, is_left, trees(&s0, result@), es.subrange(change_index as int, es.len() as int), nl);
        }
        Some(self.prepend_nary_children(op, ret, &result, is_left))
    }

    /// `(eo::list_minclude op t1 t2)` and `(eo::list_meq op t1 t2)`: whether `t1`
    /// has the elements of `t2` at least, or exactly, as often.
    #[cfg_attr(verus_keep_ghost, verifier::loop_isolation(false), verus_spec(r =>
        requires
            old(self).wf(),
            old(self).has_all(args@),
            old(self).has(op),
            old(self).has(nil),
        ensures
            final(self).wf(),
            final(self).keeps(old(self)),
            r matches Some(t) ==> final(self).has(t),
    ))]
    fn list_compare(
        &mut self,
        k: EvalOp,
        args: &[Term],
        op: Term,
        nil: Term,
        is_left: bool,
    ) -> Option<Term> {
        proof! {
            use_collections();
            broadcast use vstd::std_specs::hash::group_hash_axioms;
            broadcast use vstd::std_specs::btree::group_btree_axioms;
        }
        let mut hargs = Vec::new();
        let mut hargs2 = Vec::new();
        let list = arg!(self, k, args, 1);
        self.get_nary_children(list, op, Some(nil), &mut hargs, is_left)?;
        let list2 = arg!(self, k, args, 2);
        self.get_nary_children(list2, op, Some(nil), &mut hargs2, is_left)?;
        if arg!(self, k, args, 1) == arg!(self, k, args, 2) {
            return Some(self.mk_true());
        }
        let count1 = count_terms(&hargs);
        let count2 = count_terms(&hargs2);
        let is_eq = k == EvalOp::ListMeq;
        // With equally many distinct elements, comparing the counts
        // in one direction is enough.
        if is_eq && count1.len() != count2.len() {
            return Some(self.mk_false());
        }
        if !counts_cover(&count1, &count2, is_eq) {
            return Some(self.mk_false());
        }
        Some(self.mk_true())
    }

    /// `(eo::list_diff op t1 t2)` and `(eo::list_inter op t1 t2)`, on multisets.
    #[cfg_attr(verus_keep_ghost, verifier::loop_isolation(false), verus_spec(r =>
        requires
            old(self).wf(),
            old(self).has_all(args@),
            old(self).has(op),
            old(self).has(nil),
        ensures
            final(self).wf(),
            final(self).keeps(old(self)),
            r matches Some(t) ==> final(self).has(t),
    ))]
    fn list_diff_or_inter(
        &mut self,
        k: EvalOp,
        args: &[Term],
        op: Term,
        nil: Term,
        is_left: bool,
    ) -> Option<Term> {
        proof! {
            use_collections();
            broadcast use vstd::std_specs::hash::group_hash_axioms;
            broadcast use vstd::std_specs::btree::group_btree_axioms;
        }
        let mut hargs = Vec::new();
        let mut hargs2 = Vec::new();
        let list = arg!(self, k, args, 1);
        self.get_nary_children(list, op, Some(nil), &mut hargs, is_left)?;
        let list2 = arg!(self, k, args, 2);
        self.get_nary_children(list2, op, Some(nil), &mut hargs2, is_left)?;
        let is_diff = k == EvalOp::ListDiff;
        if arg!(self, k, args, 1) == arg!(self, k, args, 2) {
            return Some(if is_diff { nil } else { arg!(self, k, args, 1) });
        }
        let mut count2 = count_terms(&hargs2);
        let mut change_index = 0;
        let mut change_size = 0;
        let mut result = Vec::new();
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant
                self.has_all(result@),
                change_index <= i,
                forall|t: Term| count2@.contains_key(t) ==> #[trigger] count2@[t] >= 1,
        ))]
        for i in 0..hargs.len() {
            let h = hargs[i];
            // one occurrence in the second list is used up
            let found = match count2.get(&h) {
                Some(&n) => {
                    if n == 1 {
                        count2.remove(&h);
                    } else {
                        count2.insert(h, n - 1);
                    }
                    true
                }
                None => false,
            };
            if found == is_diff {
                change_index = i + 1;
                change_size = result.len();
                continue;
            }
            result.push(h);
        }
        if change_index == 0 {
            return Some(arg!(self, k, args, 1));
        }
        result.truncate(change_size);
        let list = arg!(self, k, args, 1);
        let ret = self.get_nary_nth_tail(list, op, is_left, change_index);
        Some(self.prepend_nary_children(op, ret, &result, is_left))
    }

    /// `(eo::list_singleton_elim op t)`.
    #[cfg_attr(verus_keep_ghost, verifier::loop_isolation(false), verus_spec(r =>
        requires
            k == EvalOp::ListSingletonElim,
            old(self).wf(),
            old(self).has_all(args@),
            old(self).has(op),
            old(self).has(nil),
        ensures
            final(self).wf(),
            final(self).keeps(old(self)),
            r matches Some(t) ==> final(self).has(t),
            list_ok(&old(self).store, &final(self).store, k, op, nil, is_left, args@, r),
    ))]
    fn list_singleton_elim(
        &mut self,
        k: EvalOp,
        args: &[Term],
        op: Term,
        nil: Term,
        is_left: bool,
    ) -> Option<Term> {
        proof! {
            use_collections();
            broadcast use vstd::std_specs::hash::group_hash_axioms;
            broadcast use vstd::std_specs::btree::group_btree_axioms;
        }
        let mut hargs = Vec::new();
        let list = arg!(self, k, args, 1);
        self.get_nary_children(list, op, Some(nil), &mut hargs, is_left)?;
        // a list of one element is that element
        Some(if hargs.len() == 1 {
            hargs[0]
        } else {
            arg!(self, k, args, 1)
        })
    }

    /// `(eo::list_singleton_intro op t)`: `t` if it is an `op`-list, the
    /// list of the one element `t` otherwise.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires
            old(self).wf(),
            old(self).has(op),
            old(self).has(nil),
            old(self).has_all(args@),
        ensures
            final(self).wf(),
            final(self).keeps(old(self)),
            r matches Some(t) ==> final(self).has(t),
    ))]
    #[cfg_attr(verus_keep_ghost, verifier::exec_allows_no_decreases_clause)]
    fn evaluate_list_singleton_intro(
        &mut self,
        op: Term,
        nil: Term,
        is_left: bool,
        args: &[Term],
    ) -> Option<Term> {
        let Some(&arg) = args.get(1) else {
            return self.missing_argument(EvalOp::ListSingletonIntro, args);
        };
        self.type_of(arg);
        let arg_type = self.store.ty(arg);
        if let Some(n) = self.evaluate_nil(op, nil, is_left, arg_type, true) {
            if self.is_nary_list(arg, op, n, is_left) {
                return Some(arg);
            }
        }
        let n = self.evaluate_nil(op, nil, is_left, arg_type, false)?;
        if self.is_nary_list(arg, op, n, is_left) {
            return Some(arg);
        }
        Some(self.prepend_nary_children(op, n, &[arg], is_left))
    }

    /// The constructor term of a symbol for the application in `children`
    /// (the head and its arguments): the symbol's own, or, if that depends
    /// on type parameters, its instance for the type of the first argument.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires
            old(self).wf(),
            cons matches Some(c) ==> old(self).has(c),
            old(self).has_all(children@),
            // the first is the head
            children@.len() >= 1,
        ensures
            final(self).wf(),
            final(self).keeps(old(self)),
            r matches Some(t) ==> final(self).has(t),
    ))]
    #[cfg_attr(verus_keep_ghost, verifier::exec_allows_no_decreases_clause)]
    pub(crate) fn compute_constructor_term(
        &mut self,
        attr: Attr,
        cons: Option<Term>,
        children: &[Term],
    ) -> Option<Term> {
        let ct = cons?;
        if self.store.kind(ct) != Kind::PARAMETERIZED {
            return Some(ct);
        }
        if children.len() == 1 {
            let msg = self.msg_no_parameters(children[0]);
            self.warn(&msg);
            return None;
        }
        if !attr.is_list_nil() {
            let msg = self.msg_unknown_category(children[0]);
            self.warn(&msg);
            return None;
        }
        let is_left = attr.is_left_nil();
        let arg = children[1];
        let Some(t) = self.type_of(arg) else {
            if self.store.is_ground(arg) {
                let msg = self.msg_type_inference_failed(children[0], arg);
                self.warn(&msg);
            }
            return None;
        };
        // This is still `None` if, say, the type is not ground.
        self.evaluate_nil(children[0], ct, is_left, Some(t), false)
    }
}

/// The messages of the evaluator's warnings and errors. Formatting text is
/// outside what Verus checks here; each takes terms of the store.
#[cfg_attr(verus_keep_ghost, verus_verify)]
impl Checker {
    #[cfg_attr(verus_keep_ghost, verus_verify(external_body), verus_spec(requires self.wf(), self.has(hd),))]
    fn msg_no_program(&self, hd: Term) -> String {
        format!("No program defined for {}", self.show(hd))
    }

    #[cfg_attr(verus_keep_ghost, verus_verify(external_body), verus_spec(requires self.wf(), self.has(pat),))]
    fn msg_bad_arity(&self, pat: Term) -> String {
        format!(
            "*** Bad number of arguments provided in function call to {}",
            self.show(pat)
        )
    }

    #[cfg_attr(verus_keep_ghost, verus_verify(external_body), verus_spec(requires self.wf(), self.has_all(args@),))]
    fn msg_arguments(&self, args: &[Term]) -> String {
        format!("  Arguments: {}", self.show_list(args, " "))
    }

    #[cfg_attr(verus_keep_ghost, verus_verify(external_body), verus_spec(requires self.wf(), self.has(nil), self.has(list),))]
    fn msg_not_a_list(&self, nil: Term, list: Term) -> String {
        format!(
            "...expected associative application to end in {}, got {}",
            self.show(nil),
            self.show(list)
        )
    }

    #[cfg_attr(verus_keep_ghost, verus_verify(external_body), verus_spec(requires self.wf(), self.has_all(args@),))]
    fn msg_too_few_arguments(&self, k: EvalOp, args: &[Term]) -> String {
        format!(
            "Too few arguments when evaluating literal op {}, {} arguments {}",
            Kind::Eval(k),
            args.len(),
            self.show_list(args, " ")
        )
    }

    #[cfg_attr(verus_keep_ghost, verus_verify(external_body), verus_spec(requires self.wf(), self.has_all(args@),))]
    fn msg_wrong_arity(&self, k: EvalOp, args: &[Term]) -> String {
        format!(
            "Wrong number of arguments when applying literal op {}, {} arguments ({})",
            Kind::Eval(k),
            args.len(),
            self.show_list(args, " ")
        )
    }

    #[cfg_attr(verus_keep_ghost, verus_verify(external_body), verus_spec(requires self.wf(), self.has(hd),))]
    fn msg_no_parameters(&self, hd: Term) -> String {
        format!("Failed to determine parameters for {}", self.show(hd))
    }

    #[cfg_attr(verus_keep_ghost, verus_verify(external_body), verus_spec(requires self.wf(), self.has(hd),))]
    fn msg_unknown_category(&self, hd: Term) -> String {
        format!(
            "Unknown category for parameterized operator {}",
            self.show(hd)
        )
    }

    #[cfg_attr(verus_keep_ghost, verus_verify(external_body), verus_spec(requires self.wf(), self.has(hd), self.has(arg),))]
    fn msg_type_inference_failed(&self, hd: Term, arg: Term) -> String {
        format!(
            "Type inference failed for {} applied to {}, failed to type check {}",
            self.show(hd),
            self.show(arg),
            self.show(arg)
        )
    }
}

/// Whether the `eo::` operator takes `nargs` arguments
/// ([`Checker::check_arity`]).
#[cfg_attr(verus_keep_ghost, verus_verify, verus_spec(r => ensures r == Checker::takes(Kind::Eval(k), nargs),))]
fn arity_ok(k: EvalOp, nargs: usize) -> bool {
    Checker::check_arity(Kind::Eval(k), nargs, None)
}

/// The position of the first `elem` in `ts`.
#[cfg_attr(verus_keep_ghost, verus_verify, verus_spec(r => ensures
    r matches Some(i) ==> i < ts@.len() && ts@[i as int] == elem
        && forall|j: int| 0 <= j < i ==> ts@[j] != elem,
    r is None ==> forall|j: int| 0 <= j < ts@.len() ==> ts@[j] != elem,
))]
#[allow(clippy::needless_range_loop, clippy::manual_find)]
fn position(ts: &[Term], elem: Term) -> Option<usize> {
    #[cfg_attr(verus_keep_ghost, verus_spec(invariant
        forall|j: int| 0 <= j < i ==> ts@[j] != elem,
    ))]
    for i in 0..ts.len() {
        if ts[i] == elem {
            return Some(i);
        }
    }
    None
}

/// Reverses the list. (Verus has no specification of `reverse` to use, so
/// this states what is needed of it: the same terms.)
#[cfg_attr(verus_keep_ghost, verus_verify(external_body), verus_spec(
    ensures
        final(ts)@.len() == old(ts)@.len(),
        forall|i: int| 0 <= i < old(ts)@.len() ==> final(ts)@[i] == old(ts)@[old(ts)@.len() - 1 - i],
))]
fn reverse(ts: &mut [Term]) {
    ts.reverse();
}

/// How many times each term is in the list, which has fewer than 2^32
/// elements.
#[cfg_attr(verus_keep_ghost, verus_verify, verifier::loop_isolation(false), verus_spec(count =>
    requires ts@.len() <= u32::MAX,
    ensures forall|t: Term| count@.contains_key(t) ==> #[trigger] count@[t] >= 1,
))]
#[allow(clippy::needless_range_loop)]
fn count_terms(ts: &[Term]) -> HashMap<Term, u32> {
    proof! {
        use_collections();
        broadcast use vstd::std_specs::hash::group_hash_axioms;
        broadcast use vstd::std_specs::btree::group_btree_axioms;
    }
    let mut count: HashMap<Term, u32> = HashMap::new();
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant forall|t: Term| count@.contains_key(t) ==> 1 <= #[trigger] count@[t] <= i,
    ))]
    for i in 0..ts.len() {
        let n = match count.get(&ts[i]) {
            Some(&n) => n,
            None => 0,
        };
        count.insert(ts[i], n + 1);
    }
    count
}

/// Whether every term is at least as often in `count1` as in `count2`; with
/// `equally`, whether each term of `count2` is as often in `count1`.
#[cfg_attr(verus_keep_ghost, verus_verify, verifier::loop_isolation(false))]
fn counts_cover(count1: &HashMap<Term, u32>, count2: &HashMap<Term, u32>, equally: bool) -> bool {
    proof! {
        use_collections();
        broadcast use vstd::std_specs::hash::group_hash_axioms;
        broadcast use vstd::std_specs::btree::group_btree_axioms;
    }
    for (elem, &n2) in count2.iter() {
        let n1 = match count1.get(elem) {
            Some(&n) => n,
            None => 0,
        };
        if if equally { n1 != n2 } else { n1 < n2 } {
            return false;
        }
    }
    true
}

#[cfg(verus_keep_ghost)]
verus! {

/// The trees of terms.
pub open spec fn trees(s: &TermStore, ts: Seq<Term>) -> Seq<Tree> {
    Seq::new(ts.len(), |i: int| s.tree(ts[i].idx()))
}

/// The application `(f x)`.
pub open spec fn app(f: Tree, x: Tree) -> Tree {
    Tree::Node(Kind::Node(NodeKind::Apply), seq![f, x])
}

/// The list with an element in front: `(f head tail)`, or
/// `(f tail head)` for an operator whose lists nest to the left.
pub open spec fn cons_tree(f: Tree, left: bool, head: Tree, tail: Tree) -> Tree {
    if left { app(app(f, tail), head) } else { app(app(f, head), tail) }
}

/// If the tree is `(f head tail)` (or `(f tail head)`), its head and its
/// tail: the pattern `(f x y)` of the plugin's list programs.
pub open spec fn uncons(f: Tree, left: bool, t: Tree) -> Option<(Tree, Tree)> {
    match t {
        Tree::Node(k, cs) => if k == Kind::Node(NodeKind::Apply) && cs.len() == 2 {
            match cs[0] {
                Tree::Node(k2, ds) => if k2 == Kind::Node(NodeKind::Apply) && ds.len() == 2 && ds[0] == f {
                    Some(if left { (cs[1], ds[1]) } else { (ds[1], cs[1]) })
                } else {
                    None
                },
                _ => None,
            }
        } else {
            None
        },
        _ => None,
    }
}

/// The elements of a list (`$eo_get_elements_rec`).
pub open spec fn elems(f: Tree, left: bool, t: Tree) -> Seq<Tree>
    decreases t,
{
    match uncons(f, left, t) {
        Some((head, tail)) => seq![head] + elems(f, left, tail),
        None => Seq::empty(),
    }
}

/// What a list ends in (`$eo_get_nil_rec`, before it asks whether that is
/// the terminator).
pub open spec fn tail_of(f: Tree, left: bool, t: Tree) -> Tree
    decreases t,
{
    match uncons(f, left, t) {
        Some((head, tail)) => tail_of(f, left, tail),
        None => t,
    }
}

/// Whether the tree is an `f`-list: it ends in the terminator
/// (`$eo_is_list`).
pub open spec fn is_list(f: Tree, nil: Tree, left: bool, t: Tree) -> bool {
    tail_of(f, left, t) == nil
}

/// The list without its first `n` elements, or what is left of it.
pub open spec fn nth_tail(f: Tree, left: bool, t: Tree, n: nat) -> Tree
    decreases n,
{
    if n == 0 {
        t
    } else {
        match uncons(f, left, t) {
            Some((head, tail)) => nth_tail(f, left, tail, (n - 1) as nat),
            None => t,
        }
    }
}

/// The list of the elements, in front of a tail.
pub open spec fn build(f: Tree, left: bool, es: Seq<Tree>, tail: Tree) -> Tree
    decreases es.len(),
{
    if es.len() == 0 {
        tail
    } else {
        cons_tree(f, left, es[0], build(f, left, es.drop_first(), tail))
    }
}

/// Two applications made one after the other are the list with one more
/// element, on the trees.
proof fn lemma_cons_built(
    s0: &TermStore,
    s1: &TermStore,
    s2: &TermStore,
    s3: &TermStore,
    op: Term,
    h: Term,
    rest: Term,
    c1: Term,
    c2: Term,
    left: bool,
)
    requires
        s0.wf(), s1.wf(), s2.wf(), s3.wf(),
        s1.extends(s0), s2.extends(s1), s3.extends(s2),
        s0.has(op), s0.has(h), s1.has(rest),
        s2.spec_limit() is None ==> s2.is_node(c1, Kind::Node(NodeKind::Apply), if left { seq![op, rest] } else { seq![op, h] }),
        s3.spec_limit() is None ==> s3.is_node(c2, Kind::Node(NodeKind::Apply), if left { seq![c1, h] } else { seq![c1, rest] }),
        s2.spec_limit() is Some ==> s3.spec_limit() is Some,
        s2.has(c1),
    ensures
        s3.extends(s0),
        s3.spec_limit() is None ==> s3.tree(c2.idx())
            == cons_tree(s0.tree(op.idx()), left, s0.tree(h.idx()), s1.tree(rest.idx())),
{
    s2.lemma_extends_twice(s1, s0);
    s3.lemma_extends_twice(s2, s0);
    s3.lemma_extends_twice(s2, s1);
    if s3.spec_limit() is None {
        s1.theorem_trees_are_kept(s0, op);
        s1.theorem_trees_are_kept(s0, h);
        s2.theorem_trees_are_kept(s1, op);
        s2.theorem_trees_are_kept(s1, h);
        s2.theorem_trees_are_kept(s1, rest);
        s3.theorem_trees_are_kept(s2, op);
        s3.theorem_trees_are_kept(s2, h);
        s3.theorem_trees_are_kept(s2, rest);
        s3.theorem_trees_are_kept(s2, c1);
        s2.lemma_node_tree(c1, Kind::Node(NodeKind::Apply), if left { seq![op, rest] } else { seq![op, h] });
        s3.lemma_node_tree(c2, Kind::Node(NodeKind::Apply), if left { seq![c1, h] } else { seq![c1, rest] });
        let t1 = s2.tree(c1.idx());
        let t2 = s3.tree(c2.idx());
        if left {
            assert(t1->Node_1 =~= seq![s0.tree(op.idx()), s1.tree(rest.idx())]);
            assert(t2->Node_1 =~= seq![t1, s0.tree(h.idx())]);
        } else {
            assert(t1->Node_1 =~= seq![s0.tree(op.idx()), s0.tree(h.idx())]);
            assert(t2->Node_1 =~= seq![t1, s1.tree(rest.idx())]);
        }
    }
}

/// What a list operator gives: a term, or a numeral or a Boolean literal.
pub enum Out {
    Term(Tree),
    Num(int),
    Bool(bool),
}

/// The term is what the specification gives.
pub open spec fn out_is(s: &TermStore, t: Term, o: Out) -> bool {
    match o {
        Out::Term(tree) => s.tree(t.idx()) == tree,
        Out::Num(n) => s.is_lit(t, s.value(t)) && s.value(t)@ == Val::Numeral(n),
        Out::Bool(b) => s.is_lit(t, s.value(t)) && s.value(t)@ == Val::Bool(b),
    }
}

/// The numeral a tree is, if it is one.
pub open spec fn numeral_of(t: Tree) -> Option<int> {
    match t {
        Tree::Lit(l) => match l@ {
            Val::Numeral(n) => Some(n),
            _ => None,
        },
        _ => None,
    }
}

/// The position of the first `z` among the elements, counted from `n`; -1
/// if there is none (`$eo_list_find_rec`).
pub open spec fn find_rec(es: Seq<Tree>, z: Tree, n: int) -> int
    decreases es.len(),
{
    if es.len() == 0 {
        -1
    } else if es[0] == z {
        n
    } else {
        find_rec(es.drop_first(), z, n + 1)
    }
}

/// The elements without the first `z` (`$eo_list_erase_rec`).
pub open spec fn erase_rec(es: Seq<Tree>, z: Tree) -> Seq<Tree>
    decreases es.len(),
{
    if es.len() == 0 {
        es
    } else if es[0] == z {
        es.drop_first()
    } else {
        seq![es[0]] + erase_rec(es.drop_first(), z)
    }
}

/// The elements without any `z` (`$eo_list_erase_all_rec`).
pub open spec fn erase_all_rec(es: Seq<Tree>, z: Tree) -> Seq<Tree>
    decreases es.len(),
{
    if es.len() == 0 {
        es
    } else if es[0] == z {
        erase_all_rec(es.drop_first(), z)
    } else {
        seq![es[0]] + erase_all_rec(es.drop_first(), z)
    }
}

/// The elements, each once, where it first is (`$eo_list_setof_rec`).
pub open spec fn setof_rec(es: Seq<Tree>) -> Seq<Tree>
    decreases es.len(),
{
    if es.len() == 0 {
        es
    } else {
        seq![es[0]] + erase_all_rec(setof_rec(es.drop_first()), es[0])
    }
}

/// The set of a list with one more element at its end: the element is
/// added if it was not there.
proof fn lemma_setof_push(a: Seq<Tree>, x: Tree)
    ensures setof_rec(a.push(x)) == (if a.contains(x) { setof_rec(a) } else { setof_rec(a).push(x) }),
    decreases a.len(),
{
    let ax = a.push(x);
    let nothing = Seq::<Tree>::empty();
    assert(erase_all_rec(nothing, x) =~= nothing);
    if a.len() == 0 {
        assert(ax.drop_first() =~= nothing);
        assert(setof_rec(nothing) =~= nothing);
        assert(setof_rec(ax) =~= seq![x]);
        assert(setof_rec(a).push(x) =~= seq![x]);
    } else {
        let h = a[0];
        let rest = a.drop_first();
        assert(ax.drop_first() =~= rest.push(x));
        assert(ax[0] == h);
        lemma_setof_push(rest, x);
        if rest.contains(x) {
            let j = choose|j: int| 0 <= j < rest.len() && rest[j] == x;
            assert(a[j + 1] == x);
        } else {
            let one = seq![x];
            assert(setof_rec(rest).push(x) =~= setof_rec(rest) + one);
            lemma_erase_all_append(setof_rec(rest), one, h);
            assert(one.drop_first() =~= nothing);
            assert(erase_all_rec(nothing, h) =~= nothing);
            if x == h {
                assert(a[0] == x);
                assert(erase_all_rec(one, h) =~= nothing);
                assert(erase_all_rec(setof_rec(rest), h) + nothing =~= erase_all_rec(setof_rec(rest), h));
            } else {
                assert(erase_all_rec(one, h) =~= one);
                assert(!a.contains(x)) by {
                    if a.contains(x) {
                        let j = choose|j: int| 0 <= j < a.len() && a[j] == x;
                        assert(rest[j - 1] == x);
                    }
                }
                assert(seq![h] + (erase_all_rec(setof_rec(rest), h) + one)
                    =~= (seq![h] + erase_all_rec(setof_rec(rest), h)).push(x));
            }
        }
    }
}

/// The same, for the elements up to a position.
proof fn lemma_setof_step(es: Seq<Tree>, i: int)
    requires 0 <= i < es.len(),
    ensures
        setof_rec(es.take(i + 1)) == (if es.take(i).contains(es[i]) {
            setof_rec(es.take(i))
        } else {
            setof_rec(es.take(i)) + seq![es[i]]
        }),
{
    assert(es.take(i + 1) =~= es.take(i).push(es[i]));
    lemma_setof_push(es.take(i), es[i]);
    assert(setof_rec(es.take(i)).push(es[i]) =~= setof_rec(es.take(i)) + seq![es[i]]);
}

/// Erasing from a list without the element changes nothing.
proof fn lemma_erase_none(es: Seq<Tree>, z: Tree)
    requires forall|j: int| 0 <= j < es.len() ==> es[j] != z,
    ensures erase_rec(es, z) == es, erase_all_rec(es, z) == es,
    decreases es.len(),
{
    if es.len() > 0 {
        assert(es[0] != z);
        lemma_erase_none(es.drop_first(), z);
        assert(seq![es[0]] + es.drop_first() =~= es);
    }
}

/// Erasing the first `z`, which is at position `i`.
proof fn lemma_erase_at(es: Seq<Tree>, z: Tree, i: int)
    requires 0 <= i < es.len(), es[i] == z, forall|j: int| 0 <= j < i ==> es[j] != z,
    ensures erase_rec(es, z) == es.take(i) + es.subrange(i + 1, es.len() as int),
    decreases i,
{
    if i == 0 {
        assert(es.drop_first() =~= es.take(0) + es.subrange(1, es.len() as int));
    } else {
        assert(es[0] != z);
        let rest = es.drop_first();
        lemma_erase_at(rest, z, i - 1);
        assert(seq![es[0]] + (rest.take(i - 1) + rest.subrange(i, rest.len() as int))
            =~= es.take(i) + es.subrange(i + 1, es.len() as int));
    }
}

/// Erasing every `z` from two lists, one after the other.
proof fn lemma_erase_all_append(a: Seq<Tree>, b: Seq<Tree>, z: Tree)
    ensures erase_all_rec(a + b, z) == erase_all_rec(a, z) + erase_all_rec(b, z),
    decreases a.len(),
{
    if a.len() == 0 {
        assert(a + b =~= b);
        assert(erase_all_rec(a, z) + erase_all_rec(b, z) =~= erase_all_rec(b, z));
    } else {
        assert((a + b).drop_first() =~= a.drop_first() + b);
        assert((a + b)[0] == a[0]);
        lemma_erase_all_append(a.drop_first(), b, z);
        if a[0] != z {
            assert(seq![a[0]] + (erase_all_rec(a.drop_first(), z) + erase_all_rec(b, z))
                =~= (seq![a[0]] + erase_all_rec(a.drop_first(), z)) + erase_all_rec(b, z));
        }
    }
}

/// Erasing every `z` from one more element.
proof fn lemma_erase_all_step(es: Seq<Tree>, z: Tree, i: int)
    requires 0 <= i < es.len(),
    ensures
        erase_all_rec(es.take(i + 1), z) == (if es[i] == z {
            erase_all_rec(es.take(i), z)
        } else {
            erase_all_rec(es.take(i), z) + seq![es[i]]
        }),
{
    let one = seq![es[i]];
    assert(es.take(i + 1) =~= es.take(i) + one);
    lemma_erase_all_append(es.take(i), one, z);
    assert(one.drop_first() =~= Seq::<Tree>::empty());
    assert(erase_all_rec(Seq::<Tree>::empty(), z) =~= Seq::<Tree>::empty());
    if es[i] == z {
        assert(erase_all_rec(one, z) =~= Seq::<Tree>::empty());
        assert(erase_all_rec(es.take(i), z) + Seq::<Tree>::empty() =~= erase_all_rec(es.take(i), z));
    } else {
        assert(erase_all_rec(one, z) =~= one);
    }
}

/// Elements in front of elements in front of a tail.
proof fn lemma_build_append(f: Tree, left: bool, a: Seq<Tree>, b: Seq<Tree>, tail: Tree)
    ensures build(f, left, a + b, tail) == build(f, left, a, build(f, left, b, tail)),
    decreases a.len(),
{
    if a.len() == 0 {
        assert(a + b =~= b);
    } else {
        assert((a + b).drop_first() =~= a.drop_first() + b);
        assert((a + b)[0] == a[0]);
        lemma_build_append(f, left, a.drop_first(), b, tail);
    }
}

/// The list without its first `k` elements is the rest of the elements
/// in front of what it ends in.
proof fn lemma_nth_tail(f: Tree, left: bool, t: Tree, k: nat)
    requires k <= elems(f, left, t).len(),
    ensures
        nth_tail(f, left, t, k)
            == build(f, left, elems(f, left, t).subrange(k as int, elems(f, left, t).len() as int), tail_of(f, left, t)),
    decreases k,
{
    let es = elems(f, left, t);
    if k == 0 {
        assert(es.subrange(0, es.len() as int) =~= es);
        lemma_build_elems(f, left, t);
    } else {
        match uncons(f, left, t) {
            Some((head, tail)) => {
                lemma_nth_tail(f, left, tail, (k - 1) as nat);
                assert(es.subrange(k as int, es.len() as int)
                    =~= elems(f, left, tail).subrange(k - 1, elems(f, left, tail).len() as int));
            },
            None => {},
        }
    }
}

/// The number of arguments a list operator takes, the operator among
/// them.
pub open spec fn list_arity(op: EvalOp) -> nat {
    match op {
        EvalOp::ListLength | EvalOp::ListRev | EvalOp::ListSetof | EvalOp::ListSingletonElim
        | EvalOp::ListSingletonIntro | EvalOp::Nil => 2,
        _ => 3,
    }
}

/// What a list operator evaluates to on the trees `a` of its arguments
/// (`a[0]` is the operator's own argument), for the operator `f` whose
/// lists end in `nil` and nest to the left if `left`; `None` if it does
/// not evaluate and the application stays.
///
/// Transcribed from Ethos's desugar plugin (`eo_desugar.eo`), each arm with
/// the program it comes from; "binary:" where this follows the binary.
/// The plugin's lists nest to the right only.
pub open spec fn list_spec(op: EvalOp, f: Tree, nil: Tree, left: bool, a: Seq<Tree>) -> Option<Out> {
    match op {
        // $eo_nil: the terminator, from the signature's table. (Here for an
        // operator whose terminator does not depend on a type; the type
        // given is not looked at.)
        EvalOp::Nil => Some(Out::Term(nil)),
        // $eo_cons
        EvalOp::Cons => if is_list(f, nil, left, a[2]) {
            Some(Out::Term(cons_tree(f, left, a[1], a[2])))
        } else {
            None
        },
        // $eo_list_concat. binary: of lists that nest to the left, the
        // second is put in front of the first
        EvalOp::ListConcat => {
            let (front, back) = if left { (a[2], a[1]) } else { (a[1], a[2]) };
            if is_list(f, nil, left, back) && is_list(f, nil, left, front) {
                Some(Out::Term(build(f, left, elems(f, left, front), back)))
            } else {
                None
            }
        },
        // $eo_list_len
        EvalOp::ListLength => if is_list(f, nil, left, a[1]) {
            Some(Out::Num(elems(f, left, a[1]).len() as int))
        } else {
            None
        },
        // $eo_list_nth: stuck past the end. binary: the index is at most
        // 2^32 - 1
        EvalOp::ListNth => match numeral_of(a[2]) {
            Some(n) => if 0 <= n <= u32::MAX && is_list(f, nil, left, a[1]) && n < elems(f, left, a[1]).len() {
                Some(Out::Term(elems(f, left, a[1])[n]))
            } else {
                None
            },
            None => None,
        },
        // $eo_list_find
        EvalOp::ListFind => if is_list(f, nil, left, a[1]) {
            Some(Out::Num(find_rec(elems(f, left, a[1]), a[2], 0)))
        } else {
            None
        },
        // $eo_list_erase
        EvalOp::ListErase => if is_list(f, nil, left, a[1]) {
            Some(Out::Term(build(f, left, erase_rec(elems(f, left, a[1]), a[2]), nil)))
        } else {
            None
        },
        // $eo_list_erase_all
        EvalOp::ListEraseAll => if is_list(f, nil, left, a[1]) {
            Some(Out::Term(build(f, left, erase_all_rec(elems(f, left, a[1]), a[2]), nil)))
        } else {
            None
        },
        // $eo_list_setof
        EvalOp::ListSetof => if is_list(f, nil, left, a[1]) {
            Some(Out::Term(build(f, left, setof_rec(elems(f, left, a[1])), nil)))
        } else {
            None
        },
        // $eo_list_rev
        EvalOp::ListRev => if is_list(f, nil, left, a[1]) {
            Some(Out::Term(build(f, left, elems(f, left, a[1]).reverse(), nil)))
        } else {
            None
        },
        // $eo_list_singleton_elim
        EvalOp::ListSingletonElim => if is_list(f, nil, left, a[1]) {
            Some(Out::Term(if elems(f, left, a[1]).len() == 1 { elems(f, left, a[1])[0] } else { a[1] }))
        } else {
            None
        },
        // $eo_list_repeat. binary: the count is at most 2^32 - 1
        EvalOp::ListRepeat => match numeral_of(a[2]) {
            Some(n) => if 0 <= n <= u32::MAX {
                Some(Out::Term(build(f, left, Seq::new(n as nat, |i: int| a[1]), nil)))
            } else {
                None
            },
            None => None,
        },
        _ => None,
    }
}

/// The list operators that [`list_spec`] specifies.
pub open spec fn list_specified(op: EvalOp) -> bool {
    matches!(
        op,
        EvalOp::Nil | EvalOp::Cons | EvalOp::ListConcat | EvalOp::ListLength | EvalOp::ListNth
            | EvalOp::ListFind | EvalOp::ListRev | EvalOp::ListSingletonElim | EvalOp::ListRepeat
            | EvalOp::ListErase | EvalOp::ListEraseAll | EvalOp::ListSetof
    )
}

/// The operator that a list operator's first argument stands for: the
/// attributes are on the operator inside `(eo::_ params op)`.
pub open spec fn list_head(s: &TermStore, t: Term) -> Term {
    if s.kind_of(t.idx()) == Kind::Node(NodeKind::Parameterized) { s.kids(t.idx())[1] } else { t }
}

/// What is proved of a list operator: unless the store is full, and for
/// the number of arguments it takes, its result is the specification's.
pub open spec fn list_ok(
    s0: &TermStore,
    s1: &TermStore,
    k: EvalOp,
    op: Term,
    nil: Term,
    left: bool,
    args: Seq<Term>,
    r: Option<Term>,
) -> bool {
    s1.spec_limit() is None && args.len() == list_arity(k) && list_specified(k) ==> (match r {
        Some(t) => list_spec(k, s0.tree(op.idx()), s0.tree(nil.idx()), left, trees(s0, args)) matches Some(o)
            && out_is(s1, t, o),
        None => list_spec(k, s0.tree(op.idx()), s0.tree(nil.idx()), left, trees(s0, args)) is None,
    })
}

/// Elements read into an empty list are the list's elements.
proof fn lemma_read(s: &TermStore, hargs: Seq<Term>, es: Seq<Tree>)
    requires trees(s, hargs) == trees(s, Seq::<Term>::empty()) + es,
    ensures trees(s, hargs) == es, hargs.len() == es.len(),
{
    assert(trees(s, Seq::<Term>::empty()) + es =~= es);
}

/// The numeral a term is, on its tree: that of its value, if it is a
/// literal.
proof fn lemma_numeral_of(s: &TermStore, t: Term)
    requires s.wf(), s.has(t),
    ensures
        numeral_of(s.tree(t.idx())) == (if s.kind_of(t.idx()) is Lit {
            match s.value(t)@ {
                Val::Numeral(n) => Some(n),
                _ => None,
            }
        } else {
            None
        }),
{
    if s.kind_of(t.idx()) is Lit {
        s.lemma_lit_exists(t);
        s.lemma_lit_tree(t, s.value(t));
    } else if s.tree(t.idx()) is Lit {
        s.lemma_tree_lit_kind(t);
    }
}

/// `find_rec` gives the first position.
proof fn lemma_find_at(es: Seq<Tree>, z: Tree, n: int, i: int)
    requires 0 <= i < es.len(), es[i] == z, forall|j: int| 0 <= j < i ==> es[j] != z,
    ensures find_rec(es, z, n) == n + i,
    decreases i,
{
    if i > 0 {
        assert(es[0] != z);
        lemma_find_at(es.drop_first(), z, n + 1, i - 1);
    }
}

/// `find_rec` gives -1 when there is none.
proof fn lemma_find_none(es: Seq<Tree>, z: Tree, n: int)
    requires forall|j: int| 0 <= j < es.len() ==> es[j] != z,
    ensures find_rec(es, z, n) == -1,
    decreases es.len(),
{
    if es.len() > 0 {
        assert(es[0] != z);
        lemma_find_none(es.drop_first(), z, n + 1);
    }
}

/// A list is its elements in front of what it ends in.
pub proof fn lemma_build_elems(f: Tree, left: bool, t: Tree)
    ensures build(f, left, elems(f, left, t), tail_of(f, left, t)) == t,
    decreases t,
{
    match uncons(f, left, t) {
        Some((head, tail)) => {
            lemma_build_elems(f, left, tail);
            let es = elems(f, left, t);
            assert(es.drop_first() =~= elems(f, left, tail));
            assert(t->Node_1 =~= seq![t->Node_1[0], t->Node_1[1]]);
            assert(t->Node_1[0]->Node_1 =~= seq![t->Node_1[0]->Node_1[0], t->Node_1[0]->Node_1[1]]);
        },
        None => {},
    }
}

/// The operators whose result depends on the values of their arguments
/// alone: the literal operators, `eo::eq` and the `eo::is_*` tests.
pub open spec fn is_scalar_op(op: EvalOp) -> bool {
    matches!(
        op,
        EvalOp::Not | EvalOp::And | EvalOp::Or | EvalOp::Xor | EvalOp::Add | EvalOp::Mul | EvalOp::Neg
            | EvalOp::Pow | EvalOp::Log | EvalOp::IntDiv | EvalOp::IntMod | EvalOp::RatDiv | EvalOp::IsNeg
            | EvalOp::Gt | EvalOp::Length | EvalOp::Concat | EvalOp::Extract | EvalOp::Find | EvalOp::ToInt
            | EvalOp::ToRat | EvalOp::ToBin | EvalOp::ToString | EvalOp::Eq | EvalOp::IsZ | EvalOp::IsQ
            | EvalOp::IsBin | EvalOp::IsStr | EvalOp::IsBool | EvalOp::IsVar
    )
}

/// The literal operators: those of [`lit_spec`].
pub open spec fn is_lit_op(op: EvalOp) -> bool {
    is_scalar_op(op) && !matches!(
        op,
        EvalOp::Eq | EvalOp::IsZ | EvalOp::IsQ | EvalOp::IsBin | EvalOp::IsStr | EvalOp::IsBool | EvalOp::IsVar
    )
}

/// The number of arguments such an operator takes.
pub open spec fn scalar_arity(op: EvalOp) -> nat {
    match op {
        EvalOp::Eq => 2,
        EvalOp::IsZ | EvalOp::IsQ | EvalOp::IsBin | EvalOp::IsStr | EvalOp::IsBool | EvalOp::IsVar => 1,
        _ => lit_arity(op),
    }
}

/// The values of terms that are literals.
pub open spec fn values(s: &TermStore, args: Seq<Term>) -> Seq<Val> {
    Seq::new(args.len(), |i: int| s.value(args[i])@)
}

/// No literal string among the arguments has 2^32 code points or more.
pub open spec fn short_args(s: &TermStore, args: Seq<Term>) -> bool {
    forall|i: int| 0 <= i < args.len() ==> ((#[trigger] s.value(args[i])@) matches Val::String(st) ==> st.len() <= u32::MAX)
}

/// What an application of a scalar operator evaluates to: `Some(v)` for
/// the literal with value `v`, `None` if it does not evaluate and stays as
/// it is.
///
/// - An argument that is not ground: it stays.
/// - `eo::eq` (`$eo_eq` of the desugar plugin) on two terms that are
///   values, that is, whose trees hold nothing unevaluated (no `eo::`
///   application, no program symbol, no `eo::?`): whether they are the
///   same term, which is whether their trees are the same. On an
///   unevaluated argument it stays.
/// - The tests (`$eo_is_z` and the like): whether the argument is a
///   literal of that kind, or a variable; `false` also for an unevaluated
///   argument.
/// - A literal operator on literals: [`lit_spec`] of their values. On
///   anything else it stays.
pub open spec fn scalar_spec(s: &TermStore, op: EvalOp, args: Seq<Term>) -> Option<Val> {
    if !(forall|i: int| 0 <= i < args.len() ==> tree_is_ground(s.tree((#[trigger] args[i]).idx()))) {
        None
    } else {
        match op {
            EvalOp::Eq => if !tree_is_evaluatable(s.tree(args[0].idx())) && !tree_is_evaluatable(s.tree(args[1].idx())) {
                Some(Val::Bool(args[0] == args[1]))
            } else {
                None
            },
            EvalOp::IsZ => Some(Val::Bool(s.kind_of(args[0].idx()) == Kind::Lit(LitKind::Numeral))),
            EvalOp::IsQ => Some(Val::Bool(s.kind_of(args[0].idx()) == Kind::Lit(LitKind::Rational))),
            EvalOp::IsBin => Some(Val::Bool(s.kind_of(args[0].idx()) == Kind::Lit(LitKind::Binary))),
            EvalOp::IsStr => Some(Val::Bool(s.kind_of(args[0].idx()) == Kind::Lit(LitKind::String))),
            EvalOp::IsBool => Some(Val::Bool(s.kind_of(args[0].idx()) == Kind::Lit(LitKind::Boolean))),
            EvalOp::IsVar => Some(Val::Bool(s.kind_of(args[0].idx()) == Kind::Node(NodeKind::Variable))),
            _ => if forall|i: int| 0 <= i < args.len() ==> s.kind_of((#[trigger] args[i]).idx()) is Lit {
                lit_spec(op, values(s, args))
            } else {
                None
            },
        }
    }
}

/// Assumed: the `Hash` and `Eq` of a list of term handles agree, which is
/// what a `HashMap` keyed by such lists needs to behave as a map.
#[verifier::external_body]
pub proof fn axiom_term_lists_are_keys()
    ensures vstd::std_specs::hash::obeys_key_model::<Vec<Term>>(),
{
}

/// The results kept of program applications are terms of the store.
spec fn cache_ok(s: &TermStore, cache: Map<Vec<Term>, Option<Term>>) -> bool {
    forall|k: Vec<Term>| #[trigger] cache.contains_key(k) ==> (cache[k] matches Some(t) ==> s.has(t))
}

/// The term is an application of `eo::ite`.
spec fn is_ite(s: &TermStore, t: Term) -> bool {
    s.kind_of(t.idx()) == Kind::Eval(EvalOp::IfThenElse)
}

/// Every level that waits is in order.
spec fn frames_ok(s: &TermStore, frames: Seq<EvFrame>) -> bool {
    forall|i: int| 0 <= i < frames.len() ==> (#[trigger] frames[i]).ok(s)
}

impl EvFrame {
    /// The term has its value.
    spec fn valued(&self, t: Term) -> bool {
        self.visited@.contains_key(t) && self.visited@[t] is Some
    }

    /// The term was looked at once: its children are being evaluated.
    spec fn pending(&self, t: Term) -> bool {
        self.visited@.contains_key(t) && self.visited@[t] is None
    }

    /// The place in the work list where a pending term waits for its
    /// children: everything above it was made before it, as its
    /// subterms are.
    spec fn open(&self, p: int) -> bool {
        &&& 0 <= p < self.visit@.len()
        &&& self.pending(self.visit@[p])
        &&& forall|q: int| p < q < self.visit@.len() ==> (#[trigger] self.visit@[q]).idx() < self.visit@[p].idx()
    }

    /// The term is on the work list above a place.
    spec fn above(&self, p: int, c: Term) -> bool {
        exists|q: int| p < q < self.visit@.len() && #[trigger] self.visit@[q] == c
    }

    /// Everything the level holds is a term of the store.
    spec fn terms_ok(&self, s: &TermStore) -> bool {
        &&& s.has(self.init)
        &&& ctx_ok(s, self.ctx@)
        &&& all_has(s, self.visit@)
        &&& forall|t: Term| #[trigger] self.visited@.contains_key(t) ==> s.has(t)
            && (self.visited@[t] matches Some(v) ==> s.has(v))
        &&& self.result_key matches Some(k) ==> all_has(s, k@)
    }

    /// The traversal is in order: a pending term waits at a place of the
    /// work list, and each of its children has its value or is above that
    /// place. Of `eo::ite`, which has three children when it is pending,
    /// this is said of the condition only.
    spec fn order_ok(&self, s: &TermStore) -> bool {
        &&& forall|t: Term| #[trigger] self.pending(t) ==> exists|p: int| #[trigger] self.open(p) && self.visit@[p] == t
        &&& forall|p: int, m: int| #![trigger self.open(p), s.kids(self.visit@[p].idx())[m]]
            self.open(p) && 0 <= m < s.kids(self.visit@[p].idx()).len() && (is_ite(s, self.visit@[p]) ==> m == 0)
            ==> self.valued(s.kids(self.visit@[p].idx())[m]) || self.above(p, s.kids(self.visit@[p].idx())[m])
        &&& forall|t: Term| #[trigger] self.pending(t) && is_ite(s, t) ==> s.kids(t.idx()).len() == 3
    }

    /// The invariant of a level.
    spec fn ok(&self, s: &TermStore) -> bool {
        self.terms_ok(s) && self.order_ok(s)
    }
}

/// A pending term on top of the work list waits there, so its children
/// have their values (of `eo::ite`, the condition).
proof fn lemma_top_open(f: &EvFrame, s: &TermStore)
    requires f.ok(s), f.visit@.len() > 0, f.pending(f.visit@.last()),
    ensures
        f.open(f.visit@.len() - 1),
        forall|m: int| 0 <= m < s.kids(f.visit@.last().idx()).len() && (is_ite(s, f.visit@.last()) ==> m == 0)
            ==> f.valued(#[trigger] s.kids(f.visit@.last().idx())[m]),
        is_ite(s, f.visit@.last()) ==> s.kids(f.visit@.last().idx()).len() == 3,
{
    let top = f.visit@.len() - 1;
    let cur = f.visit@.last();
    let p = choose|p: int| #[trigger] f.open(p) && f.visit@[p] == cur;
    if p < top {
        assert(f.visit@[top].idx() < f.visit@[p].idx());
    }
    assert(f.open(top));
    assert forall|m: int| 0 <= m < s.kids(cur.idx()).len() && (is_ite(s, cur) ==> m == 0)
        implies f.valued(#[trigger] s.kids(cur.idx())[m]) by {
        let c = s.kids(f.visit@[top].idx())[m];
        assert(f.valued(c) || f.above(top, c));
    }
}

/// A level with the same contents is in order too.
proof fn lemma_same(f0: &EvFrame, f1: &EvFrame, s: &TermStore)
    requires
        f0.ok(s),
        f1.visit@ == f0.visit@,
        f1.visited@ == f0.visited@,
        f1.init == f0.init && f1.ctx == f0.ctx && f1.result_key == f0.result_key,
    ensures f1.ok(s),
{
    assert forall|p: int| f1.open(p) == f0.open(p) by {}
    assert forall|t: Term| #[trigger] f1.pending(t) implies
        exists|p: int| #[trigger] f1.open(p) && f1.visit@[p] == t by {
        assert(f0.pending(t));
        let p0 = choose|p0: int| #[trigger] f0.open(p0) && f0.visit@[p0] == t;
        assert(f1.open(p0));
    }
    assert forall|p: int, m: int| #![trigger f1.open(p), s.kids(f1.visit@[p].idx())[m]]
        f1.open(p) && 0 <= m < s.kids(f1.visit@[p].idx()).len() && (is_ite(s, f1.visit@[p]) ==> m == 0)
        implies f1.valued(s.kids(f1.visit@[p].idx())[m]) || f1.above(p, s.kids(f1.visit@[p].idx())[m]) by {
        let c = s.kids(f0.visit@[p].idx())[m];
        assert(f0.open(p));
        if !f0.valued(c) {
            let q = choose|q: int| p < q < f0.visit@.len() && #[trigger] f0.visit@[q] == c;
            assert(f1.visit@[q] == c);
        }
    }
    assert forall|t: Term| #[trigger] f1.pending(t) && is_ite(s, t) implies s.kids(t.idx()).len() == 3 by {
        assert(f0.pending(t));
    }
}

/// The term on top of the work list gets a value and leaves the list.
proof fn lemma_settle(f0: &EvFrame, f1: &EvFrame, s: &TermStore, v: Term)
    requires
        f0.ok(s),
        f0.visit@.len() > 0,
        s.has(v),
        f1.visit@ == f0.visit@.drop_last(),
        f1.visited@ == f0.visited@.insert(f0.visit@.last(), Some(v)),
        f1.init == f0.init && f1.ctx == f0.ctx && f1.result_key == f0.result_key,
    ensures f1.ok(s),
{
    let cur = f0.visit@.last();
    let top = f0.visit@.len() - 1;
    assert(s.has(f0.visit@[top]));
    assert forall|i: int| 0 <= i < f1.visit@.len() implies s.has(#[trigger] f1.visit@[i]) by {
        assert(s.has(f0.visit@[i]));
    }
    // a place that is open after was open before
    assert forall|p: int| #[trigger] f1.open(p) implies f0.open(p) by {
        let t = f1.visit@[p];
        assert(f0.pending(t));
        let p0 = choose|p0: int| #[trigger] f0.open(p0) && f0.visit@[p0] == t;
        if p0 > p {
            if p0 < top {
                assert(f1.visit@[p0].idx() < f1.visit@[p].idx());
            }
        } else if p0 < p {
            assert(f0.visit@[p].idx() < f0.visit@[p0].idx());
        }
    }
    assert forall|t: Term| #[trigger] f1.pending(t) implies
        exists|p: int| #[trigger] f1.open(p) && f1.visit@[p] == t by {
        assert(f0.pending(t));
        let p0 = choose|p0: int| #[trigger] f0.open(p0) && f0.visit@[p0] == t;
        assert(f1.open(p0));
    }
    assert forall|p: int, m: int| #![trigger f1.open(p), s.kids(f1.visit@[p].idx())[m]]
        f1.open(p) && 0 <= m < s.kids(f1.visit@[p].idx()).len() && (is_ite(s, f1.visit@[p]) ==> m == 0)
        implies f1.valued(s.kids(f1.visit@[p].idx())[m]) || f1.above(p, s.kids(f1.visit@[p].idx())[m]) by {
        let c = s.kids(f0.visit@[p].idx())[m];
        assert(f0.open(p));
        if !f0.valued(c) {
            let q = choose|q: int| p < q < f0.visit@.len() && #[trigger] f0.visit@[q] == c;
            if q < top {
                assert(f1.visit@[q] == c);
            }
        }
    }
    assert forall|t: Term| #[trigger] f1.pending(t) && is_ite(s, t) implies s.kids(t.idx()).len() == 3 by {
        assert(f0.pending(t));
    }
}

/// Terms made before the term on top of the work list are put above it,
/// and it is pending: it was, or it becomes so now with the children it
/// waits for among the terms put there.
proof fn lemma_grow(f0: &EvFrame, f1: &EvFrame, s: &TermStore, pushed: Seq<Term>)
    requires
        s.wf(),
        f0.ok(s),
        f0.visit@.len() > 0,
        f1.visit@ == f0.visit@ + pushed,
        forall|j: int| 0 <= j < pushed.len() ==> s.has(#[trigger] pushed[j])
            && pushed[j].idx() < f0.visit@.last().idx(),
        f1.visited@ == f0.visited@.insert(f0.visit@.last(), None),
        f1.init == f0.init && f1.ctx == f0.ctx && f1.result_key == f0.result_key,
        f0.pending(f0.visit@.last()) || {
            &&& !f0.visited@.contains_key(f0.visit@.last())
            &&& if is_ite(s, f0.visit@.last()) {
                s.kids(f0.visit@.last().idx()).len() == 3 && pushed == seq![s.kids(f0.visit@.last().idx())[0]]
            } else {
                pushed == s.kids(f0.visit@.last().idx())
            }
        },
    ensures f1.ok(s),
{
    let cur = f0.visit@.last();
    let n0 = f0.visit@.len() as int;
    let top = n0 - 1;
    assert(s.has(f0.visit@[top]));
    assert forall|i: int| 0 <= i < f1.visit@.len() implies s.has(#[trigger] f1.visit@[i]) by {
        if i < n0 {
            assert(s.has(f0.visit@[i]));
        } else {
            assert(f1.visit@[i] == pushed[i - n0]);
        }
    }
    assert forall|q: int| n0 <= q < f1.visit@.len() implies (#[trigger] f1.visit@[q]).idx() < cur.idx() by {
        assert(f1.visit@[q] == pushed[q - n0]);
    }
    if f0.pending(cur) {
        assert(f1.visited@ =~= f0.visited@);
        lemma_top_open(f0, s);
    }
    assert(f1.open(top));
    // a place that was open stays open
    assert forall|p: int| #[trigger] f0.open(p) implies f1.open(p) by {
        if p < top {
            assert(f0.visit@[top].idx() < f0.visit@[p].idx());
        }
        assert(f0.visit@[p] != cur || p == top);
    }
    // and no other place is open
    assert forall|p: int| #[trigger] f1.open(p) && p != top implies f0.open(p) && p < top by {
        let t = f1.visit@[p];
        if p >= n0 {
            // a term put above: were it pending, it would wait below the top
            assert(t.idx() < cur.idx());
            assert(f0.pending(t));
            let p0 = choose|p0: int| #[trigger] f0.open(p0) && f0.visit@[p0] == t;
            if p0 < top {
                assert(f0.visit@[top].idx() < f0.visit@[p0].idx());
            }
            assert(false);
        }
        if t == cur {
            assert(f1.visit@[top].idx() < f1.visit@[p].idx());
            assert(false);
        }
        assert(f0.pending(t));
    }
    assert forall|t: Term| #[trigger] f1.pending(t) implies
        exists|p: int| #[trigger] f1.open(p) && f1.visit@[p] == t by {
        if t == cur {
            assert(f1.open(top) && f1.visit@[top] == t);
        } else {
            assert(f0.pending(t));
            let p0 = choose|p0: int| #[trigger] f0.open(p0) && f0.visit@[p0] == t;
            assert(f1.open(p0));
        }
    }
    assert forall|p: int, m: int| #![trigger f1.open(p), s.kids(f1.visit@[p].idx())[m]]
        f1.open(p) && 0 <= m < s.kids(f1.visit@[p].idx()).len() && (is_ite(s, f1.visit@[p]) ==> m == 0)
        implies f1.valued(s.kids(f1.visit@[p].idx())[m]) || f1.above(p, s.kids(f1.visit@[p].idx())[m]) by {
        let c = s.kids(f1.visit@[p].idx())[m];
        if p == top && !f0.pending(cur) {
            assert(f1.visit@[n0 + m] == pushed[m]);
            assert(f1.visit@[n0 + m] == c);
        } else {
            assert(f0.open(p));
            assert(f0.visit@[p] == f1.visit@[p]);
            let c0 = s.kids(f0.visit@[p].idx())[m];
            if !f0.valued(c0) {
                let q = choose|q: int| p < q < f0.visit@.len() && #[trigger] f0.visit@[q] == c0;
                assert(f1.visit@[q] == c);
            } else {
                assert(c0 != cur || f0.pending(cur));
            }
        }
    }
    assert forall|t: Term| #[trigger] f1.pending(t) && is_ite(s, t) implies s.kids(t.idx()).len() == 3 by {
        if t != cur {
            assert(f0.pending(t));
        } else if f0.pending(cur) {
        }
    }
}

/// A level is in order in a store that kept the terms of the one it was
/// in order in.
proof fn lemma_frame_kept(f: &EvFrame, s1: &TermStore, s0: &TermStore)
    requires f.ok(s0), keeps(s1, s0),
    ensures f.ok(s1),
{
    assert forall|i: int| 0 <= i < f.visit@.len() implies s1.has(#[trigger] f.visit@[i]) by {
        assert(s0.has(f.visit@[i]));
    }
    if f.result_key is Some {
        let k = f.result_key->0;
        assert forall|i: int| 0 <= i < k@.len() implies s1.has(#[trigger] k@[i]) by {
            assert(s0.has(k@[i]));
        }
    }
    assert forall|p: int, m: int| #![trigger f.open(p), s1.kids(f.visit@[p].idx())[m]]
        f.open(p) && 0 <= m < s1.kids(f.visit@[p].idx()).len() && (is_ite(s1, f.visit@[p]) ==> m == 0)
        implies f.valued(s1.kids(f.visit@[p].idx())[m]) || f.above(p, s1.kids(f.visit@[p].idx())[m]) by {
        assert(s0.has(f.visit@[p]));
        let c = s0.kids(f.visit@[p].idx())[m];
        assert(f.valued(c) || f.above(p, c));
    }
    assert forall|t: Term| #[trigger] f.pending(t) && is_ite(s1, t) implies s1.kids(t.idx()).len() == 3 by {
        assert(s0.has(t));
    }
}

/// What a store keeps of a store that kept the terms of a third, it keeps
/// of the third.
pub(crate) proof fn lemma_keeps_twice(s2: &TermStore, s1: &TermStore, s0: &TermStore)
    requires keeps(s2, s1), keeps(s1, s0),
    ensures keeps(s2, s0),
{
    assert forall|t: Term| #[trigger] s0.has(t) implies s2.has(t)
        && s2.kind_of(t.idx()) == s0.kind_of(t.idx()) && s2.kids(t.idx()) == s0.kids(t.idx()) by {
        assert(s1.has(t));
    }
}

/// The same of the levels that wait.
proof fn lemma_frames_kept(s1: &TermStore, s0: &TermStore, frames: Seq<EvFrame>)
    requires frames_ok(s0, frames), keeps(s1, s0),
    ensures frames_ok(s1, frames),
{
    assert forall|i: int| 0 <= i < frames.len() implies (#[trigger] frames[i]).ok(s1) by {
        lemma_frame_kept(&frames[i], s1, s0);
    }
}

/// The same of the results kept of program applications.
proof fn lemma_cache_kept(s1: &TermStore, s0: &TermStore, cache: Map<Vec<Term>, Option<Term>>)
    requires cache_ok(s0, cache), keeps(s1, s0),
    ensures cache_ok(s1, cache),
{
}

/// What the maps and sets keyed by terms need, to behave as maps and sets:
/// the assumptions on the derived order and hash of term handles, and
/// Verus's specifications of the collections.
pub(crate) proof fn use_collections()
    ensures
        vstd::laws_cmp::obeys_cmp::<Term>(),
        vstd::std_specs::hash::obeys_key_model::<Term>(),
        vstd::std_specs::hash::obeys_key_model::<(Term, Term)>(),
{
    axiom_terms_are_ordered();
    axiom_terms_are_keys();
    axiom_term_pairs_are_keys();
}

} // verus!
