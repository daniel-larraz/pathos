//! Evaluation (`TypeChecker::evaluate` and the program and `eo::` operator
//! evaluators in Ethos's `type_checker.cpp`).

use std::collections::{HashMap, HashSet};

#[cfg(verus_keep_ghost)]
use pathos_term::TermStore;
use pathos_term::{EvalOp, Integer, Kind, Lit, NodeKind, Term};

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
    #[cfg_attr(verus_keep_ghost, verifier::loop_isolation(false), verus_spec(
        requires self.wf(), self.has_all(ts@),
    ))]
    fn all_ground(&self, ts: &[Term]) -> bool {
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
    #[cfg_attr(verus_keep_ghost, verifier::loop_isolation(false), verus_spec(
        requires self.wf(), self.has_all(ts@),
    ))]
    fn all_literals(&self, ts: &[Term]) -> bool {
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
            check_nil matches Some(n) ==> old(self).has(n),
            old(self).has_all(old(children)@),
        ensures
            final(self).unchanged(old(self)),
            final(self).has_all(final(children)@),
            // a list is no longer than the store is large
            final(children)@.len() <= old(children)@.len() + u32::MAX,
            r matches Some(t) ==> final(self).has(t),
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
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant
                self.has(e),
                0 < e.idx(),
                self.has_all(children@),
                children@.len() + e.idx() <= old(children)@.len() + orig.idx(),
            decreases e.idx(),
        ))]
        while let Some((head, tail)) = self.nary_step(e, op, is_left) {
            children.push(head);
            e = tail;
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
        requires self.wf(), self.has(e),
        ensures r matches Some((head, tail)) ==> self.has(head) && self.has(tail)
            && 0 < head.idx() < e.idx() && 0 < tail.idx() < e.idx(),
    ))]
    fn nary_step(&self, e: Term, op: Term, is_left: bool) -> Option<(Term, Term)> {
        let s = &self.store;
        if s.kind(e) != Kind::APPLY || s.num_children(e) != 2 {
            return None;
        }
        let cop = s.child(e, 0);
        if s.kind(cop) != Kind::APPLY || s.num_children(cop) != 2 || s.child(cop, 0) != op {
            return None;
        }
        proof! {
            s.lemma_children(e);
            s.lemma_children(cop);
        }
        let (a, b) = (s.child(cop, 1), s.child(e, 1));
        Some(if is_left { (b, a) } else { (a, b) })
    }

    /// Whether `e` is an `op`-list ending in `nil`.
    #[cfg_attr(verus_keep_ghost, verifier::loop_isolation(false), verus_spec(
        requires self.wf(), self.has(e),
    ))]
    fn is_nary_list(&self, e: Term, op: Term, nil: Term, is_left: bool) -> bool {
        let mut e = e;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant self.has(e),
            decreases e.idx(),
        ))]
        while let Some((_, tail)) = self.nary_step(e, op, is_left) {
            e = tail;
        }
        e == nil
    }

    /// The `n`-th tail of the `op`-list `e`, which has at least `n`
    /// elements.
    #[cfg_attr(verus_keep_ghost, verifier::loop_isolation(false), verus_spec(r =>
        requires self.wf(), self.has(e),
        ensures self.has(r),
    ))]
    fn get_nary_nth_tail(&self, e: Term, op: Term, is_left: bool, n: usize) -> Term {
        let mut e = e;
        #[cfg_attr(verus_keep_ghost, verus_spec(invariant self.has(e)))]
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
    ))]
    fn prepend_nary_children(
        &mut self,
        op: Term,
        ret: Term,
        hargs: &[Term],
        is_left: bool,
    ) -> Term {
        let mut ret = ret;
        // from the last element to the first
        let mut i = hargs.len();
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant
                self.wf(),
                self.keeps(old(self)),
                self.has(ret),
                i <= hargs@.len(),
            decreases i,
        ))]
        while i > 0 {
            i -= 1;
            let h = hargs[i];
            proof_decl! { let ghost before = *self; }
            ret = if is_left {
                let c1 = self.store.mk_apply(op, ret);
                proof_decl! {
                    self.lemma_stored(&before);
                    let ghost between = *self;
                }
                let c2 = self.store.mk_apply(c1, h);
                proof! { self.lemma_stored(&between); }
                c2
            } else {
                let c1 = self.store.mk_apply(op, h);
                proof_decl! {
                    self.lemma_stored(&before);
                    let ghost between = *self;
                }
                let c2 = self.store.mk_apply(c1, ret);
                proof! { self.lemma_stored(&between); }
                c2
            };
        }
        ret
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires old(self).wf(),
        ensures final(self).wf(), final(self).keeps(old(self)), final(self).has(r),
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
                if !self.store.is_evaluatable(first) && !self.store.is_evaluatable(args[1]) {
                    return Some(self.mk_bool(first == args[1]));
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
                return Some(self.mk_bool(self.store.kind(first) == kk));
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
            if !arity_ok(k, args.len()) {
                let msg = self.msg_wrong_arity(k, args);
                self.warn(&msg);
                return None;
            }
            let mut lits: Vec<&Lit> = Vec::new();
            #[cfg_attr(verus_keep_ghost, verus_spec(
                invariant forall|j: int| 0 <= j < lits@.len() ==> (#[trigger] lits@[j]).wf(),
            ))]
            for i in 0..args.len() {
                if let Some(lit) = self.store.lit(args[i]) {
                    lits.push(lit);
                }
            }
            let eval = Lit::evaluate(k, lits.as_slice())?;
            proof_decl! { let ghost before = *self; }
            let t = self.store.mk_lit(eval);
            proof! { self.lemma_stored(&before); }
            return Some(t);
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
            old(self).wf(),
            old(self).has_all(args@),
            old(self).has(op),
            old(self).has(nil),
        ensures
            final(self).wf(),
            final(self).keeps(old(self)),
            r matches Some(t) ==> final(self).has(t),
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
            old(self).wf(),
            old(self).has_all(args@),
            old(self).has(op),
            old(self).has(nil),
        ensures
            final(self).wf(),
            final(self).keeps(old(self)),
            r matches Some(t) ==> final(self).has(t),
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
        } else {
            let list = arg!(self, k, args, head_index);
            self.get_nary_children(list, op, Some(nil), &mut hargs, is_left)?;
            // nothing to rebuild when the tail is empty
            if ret == nil {
                return Some(arg!(self, k, args, head_index));
            }
        }
        Some(self.prepend_nary_children(op, ret, &hargs, is_left))
    }

    /// `(eo::list_repeat op e n)`: the list of `n` times `e`.
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
        let n = arg!(self, k, args, 2);
        let count = match self.store.lit(n) {
            Some(Lit::Numeral(i)) if i.fits_u32() => i.to_u32(),
            _ => return None,
        };
        let mut ret = nil;
        proof_decl! { let ghost start = *self; }
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant
                self.wf(),
                self.keeps(&start),
                self.has(ret),
        ))]
        for _i in 0..count {
            let elem = arg!(self, k, args, 1);
            ret = self.prepend_nary_children(op, ret, &[elem], is_left);
        }
        Some(ret)
    }

    /// `(eo::list_len op t)`.
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
            old(self).wf(),
            old(self).has_all(args@),
            old(self).has(op),
            old(self).has(nil),
        ensures
            final(self).wf(),
            final(self).keeps(old(self)),
            r matches Some(t) ==> final(self).has(t),
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
        let mut hargs = Vec::new();
        let n = arg!(self, k, args, 2);
        let i = match self.store.lit(n) {
            Some(Lit::Numeral(i)) if i.fits_u32() => i.to_u32() as usize,
            _ => return None,
        };
        // all the elements are read, to check that this is a list
        let list = arg!(self, k, args, 1);
        self.get_nary_children(list, op, Some(nil), &mut hargs, is_left)?;
        hargs.get(i).copied()
    }

    /// `(eo::list_find op t e)`: the position of `e` in `t`, or -1.
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
        let elem = arg!(self, k, args, 2);
        match position(&hargs, elem) {
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
        proof_decl! { let ghost at = *self; }
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant *self == at, self.has_all(result@), change_index <= i,
        ))]
        for i in 0..hargs.len() {
            let h = hargs[i];
            if h == arg!(self, k, args, 2) {
                change_index = i + 1;
                if !is_all {
                    break;
                }
                change_size = result.len();
                continue;
            }
            result.push(h);
        }
        if change_index == 0 {
            return Some(arg!(self, k, args, 1));
        }
        // Keep the list after the last change as it is, and rebuild
        // only what comes before.
        if is_all {
            result.truncate(change_size);
        }
        let list = arg!(self, k, args, 1);
        let ret = self.get_nary_nth_tail(list, op, is_left, change_index);
        Some(self.prepend_nary_children(op, ret, &result, is_left))
    }

    /// `(eo::list_rev op t)`.
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
        reverse(hargs.as_mut_slice());
        Some(self.prepend_nary_children(op, nil, &hargs, is_left))
    }

    /// `(eo::list_setof op t)`: `t` without the later copies of its elements.
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
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant self.has_all(result@), change_index <= i,
        ))]
        for i in 0..hargs.len() {
            let elem = hargs[i];
            if seen.insert(elem) {
                result.push(elem);
            } else {
                change_index = i + 1;
                change_size = result.len();
            }
        }
        if change_index == 0 {
            return Some(arg!(self, k, args, 1));
        }
        result.truncate(change_size);
        let list = arg!(self, k, args, 1);
        let ret = self.get_nary_nth_tail(list, op, is_left, change_index);
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
            old(self).wf(),
            old(self).has_all(args@),
            old(self).has(op),
            old(self).has(nil),
        ensures
            final(self).wf(),
            final(self).keeps(old(self)),
            r matches Some(t) ==> final(self).has(t),
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
#[cfg_attr(verus_keep_ghost, verus_verify)]
fn arity_ok(k: EvalOp, nargs: usize) -> bool {
    Checker::check_arity(Kind::Eval(k), nargs, None)
}

/// The position of the first `elem` in `ts`.
#[cfg_attr(verus_keep_ghost, verus_verify, verus_spec(r => ensures r matches Some(i) ==> i < ts@.len(),))]
#[allow(clippy::needless_range_loop, clippy::manual_find)]
fn position(ts: &[Term], elem: Term) -> Option<usize> {
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
