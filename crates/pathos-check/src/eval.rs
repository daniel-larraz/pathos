//! Evaluation (`TypeChecker::evaluate` and the program and `eo::` operator
//! evaluators in Ethos's `type_checker.cpp`).

use std::collections::{HashMap, HashSet};

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

impl EvFrame {
    fn new(init: Term, ctx: Ctx, result_key: Option<Vec<Term>>) -> EvFrame {
        EvFrame {
            init,
            ctx,
            visited: HashMap::new(),
            visit: vec![init],
            result_key,
        }
    }
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
    /// Trusted for now: the proof of this function is milestone 22.
    #[cfg_attr(verus_keep_ghost, verus_verify(external_body), verus_spec(r =>
        requires old(self).wf(), old(self).has(e), old(self).binds(ctx@),
        ensures
            final(self).wf(),
            final(self).keeps(old(self)),
            final(self).has(r),
    ))]
    pub fn evaluate(&mut self, e: Term, ctx: &Ctx) -> Term {
        // Results of program applications in this call, so that programs
        // recursing over a term visit shared subterms once. `None` is an
        // application that failed: it is not tried again, as in Ethos, so
        // its warnings appear once.
        let mut eval_cache: HashMap<Vec<Term>, Option<Term>> = HashMap::new();
        let mut estack = vec![EvFrame::new(e, ctx.clone(), None)];
        let mut evaluated: Option<Term> = None;
        let mut new_context = false;
        let mut can_evaluate = true;
        while !estack.is_empty() {
            let top = estack.len() - 1;
            while let Some(&cur) = estack[top].visit.last() {
                let evf = &mut estack[top];
                // Not evaluatable, and ground or nothing to substitute: the
                // term stays as it is.
                if !self.store.is_evaluatable(cur)
                    && (self.store.is_ground(cur) || evf.ctx.is_empty())
                {
                    evf.visited.insert(cur, Some(cur));
                    evf.visit.pop();
                    continue;
                }
                let ck = self.store.kind(cur);
                if ck == Kind::PARAM {
                    // a parameter the context does not bind stays
                    let v = evf.ctx.get(&cur).copied().unwrap_or(cur);
                    evf.visited.insert(cur, Some(v));
                    evf.visit.pop();
                    continue;
                }
                match evf.visited.get(&cur).copied() {
                    None => {
                        // a plugin may evaluate the term itself
                        if self.eval_plugin.0.is_some() {
                            let ctx = estack[top].ctx.clone();
                            if let Some(r) = self.plugin_evaluate(cur, &ctx) {
                                let evf = &mut estack[top];
                                evf.visited.insert(cur, Some(r));
                                evf.visit.pop();
                                continue;
                            }
                        }
                        let evf = &mut estack[top];
                        // first visit: evaluate the children
                        evf.visited.insert(cur, None);
                        let children = self.store.children(cur);
                        if ck == Kind::Eval(EvalOp::IfThenElse) {
                            if children.len() != 3 {
                                // malformed: does not evaluate
                                evf.visited.insert(cur, Some(cur));
                                evf.visit.pop();
                                continue;
                            }
                            // only the condition, for now
                            evf.visit.push(children[0]);
                        } else {
                            evf.visit.extend_from_slice(children);
                        }
                        continue;
                    }
                    Some(Some(_)) => {
                        evf.visit.pop();
                        continue;
                    }
                    Some(None) => {}
                }
                // second visit: the children are evaluated (for
                // if-then-else, at least the condition is)
                let children = self.store.children(cur).to_vec();
                let mut cchildren: Vec<Option<Term>> = Vec::with_capacity(children.len());
                let mut cchanged = false;
                for &cp in &children {
                    let v = evf.visited.get(&cp).copied().flatten();
                    if let Some(v) = v {
                        cchanged = cchanged || v != cp;
                    }
                    cchildren.push(v);
                }
                evaluated = None;
                match ck {
                    Kind::Node(NodeKind::Apply | NodeKind::ApplyOpaque) => {
                        let Some(args) = cchildren.iter().copied().collect::<Option<Vec<Term>>>()
                        else {
                            unreachable!("children of an application are evaluated first")
                        };
                        if self.store.kind(args[0]) == Kind::PROGRAM_CONST {
                            if let Some(&r) = eval_cache.get(&args) {
                                evaluated = r;
                            } else {
                                let mut new_ctx = Ctx::new();
                                evaluated = self.evaluate_program_internal(&args, &mut new_ctx);
                                match evaluated {
                                    // a body that needs substitution is
                                    // evaluated at a new level
                                    Some(ev)
                                        if !self.store.is_ground(ev) && !new_ctx.is_empty() =>
                                    {
                                        new_context = true;
                                        estack.push(EvFrame::new(ev, new_ctx, Some(args)));
                                    }
                                    // otherwise the result, or the failure,
                                    // is final
                                    _ => {
                                        eval_cache.insert(args, evaluated);
                                    }
                                }
                            }
                        }
                    }
                    Kind::Eval(EvalOp::IfThenElse) => {
                        let evf = &mut estack[top];
                        let cond = cchildren[0].and_then(|c| match self.store.lit(c) {
                            Some(Lit::Bool(b)) => Some(*b),
                            _ => None,
                        });
                        if let Some(b) = cond {
                            // only the branch taken is evaluated
                            let index = if b { 1 } else { 2 };
                            match cchildren[index] {
                                None => {
                                    can_evaluate = false;
                                    evf.visit.push(children[index]);
                                }
                                Some(v) => evaluated = Some(v),
                            }
                        } else {
                            // Both branches are evaluated, so that
                            // substitution into them is complete.
                            for i in 1..3 {
                                if cchildren[i].is_none() {
                                    evf.visit.push(children[i]);
                                    can_evaluate = false;
                                }
                            }
                        }
                    }
                    Kind::Eval(op) => {
                        let Some(args) = cchildren.iter().copied().collect::<Option<Vec<Term>>>()
                        else {
                            unreachable!("children of an operator are evaluated first")
                        };
                        evaluated = self.evaluate_literal_op_internal(op, &args);
                        if self.fatal.is_some() {
                            // the run is over; see `Checker::take_fatal`
                            return e;
                        }
                    }
                    _ => {}
                }
                if new_context {
                    break;
                }
                if can_evaluate {
                    let ev = match evaluated {
                        Some(ev) => ev,
                        None if cchanged => {
                            let args: Vec<Term> = cchildren
                                .iter()
                                .zip(&children)
                                .map(|(c, &orig)| c.unwrap_or(orig))
                                .collect();
                            self.store.mk(ck, &args)
                        }
                        None => cur,
                    };
                    evaluated = Some(ev);
                    let evf = &mut estack[top];
                    evf.visited.insert(cur, Some(ev));
                    evf.visit.pop();
                } else {
                    can_evaluate = true;
                }
            }
            if new_context {
                // continue with the level just pushed
                new_context = false;
                continue;
            }
            // this level is done: hand its result to the level below
            let Some(evf) = estack.pop() else { break };
            let result = evf
                .visited
                .get(&evf.init)
                .copied()
                .flatten()
                .unwrap_or(evf.init);
            evaluated = Some(result);
            if let Some(key) = evf.result_key {
                eval_cache.insert(key, Some(result));
            }
            if let Some(parent) = estack.last_mut()
                && let Some(app) = parent.visit.pop()
            {
                parent.visited.insert(app, Some(result));
            }
        }
        evaluated.unwrap_or(e)
    }

    /// The plugin's value of `e`, if a plugin evaluates it.
    #[cfg_attr(verus_keep_ghost, verus_verify(external_body))]
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
    ///
    /// Trusted: typing is not verified. It evaluates terms, so this assumes
    /// of the evaluator, one level down, what is proved of it here.
    #[cfg_attr(verus_keep_ghost, verus_verify(external_body), verus_spec(r =>
        requires old(self).wf(), old(self).has(e),
        ensures
            final(self).wf(),
            final(self).keeps(old(self)),
            r matches Some(t) ==> final(self).has(t),
    ))]
    fn type_of(&mut self, e: Term) -> Option<Term> {
        self.get_type(e, None)
    }

    /// [`Checker::mk_list`]. Trusted: building applications is not verified.
    #[cfg_attr(verus_keep_ghost, verus_verify(external_body), verus_spec(r =>
        requires old(self).wf(), old(self).has_all(args@),
        ensures
            final(self).wf(),
            final(self).keeps(old(self)),
            final(self).has(r),
    ))]
    fn list_of(&mut self, args: &[Term]) -> Term {
        self.mk_list(args)
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
        Some(self.list_of(&cargsp))
    }

    /// Evaluates a list operator: `args[0]` is the list constructor.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires old(self).wf(), old(self).has_all(args@), args@.len() >= 1,
        ensures
            final(self).wf(),
            final(self).keeps(old(self)),
            r matches Some(t) ==> final(self).has(t),
    ))]
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
/// ([`Checker::check_arity`], which also writes messages, is not verified).
#[cfg_attr(verus_keep_ghost, verus_verify(external_body))]
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
