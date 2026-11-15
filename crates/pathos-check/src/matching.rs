//! Matching a pattern against a term, and finding the case of a program
//! that matches its arguments (`TypeChecker::match` and the loop of
//! `evaluateProgramInternal` in Ethos).
//!
//! These are functions of the term store alone, apart from the rest of the
//! checker, so that Verus can check them: see `docs/verus-spike.md`. What it
//! proves is that they cannot panic and that every term they read or bind
//! is a term of the store; not yet that the match they find is right.

use std::collections::HashSet;

use pathos_term::{Kind, Term, TermStore};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

use crate::checker::Ctx;

/// Matches the pattern `a` against `b`, extending `ctx` so that `a`
/// instantiated by `ctx` is `b`. `visited` holds the pairs already
/// matched by earlier calls that share `ctx`.
#[cfg_attr(verus_keep_ghost, verus_verify, verifier::exec_allows_no_decreases_clause, verifier::loop_isolation(false), verus_spec(r =>
    requires
        s.wf(),
        s.has(a),
        s.has(b),
        ctx_ok(s, old(ctx)@),
    ensures
        ctx_ok(s, final(ctx)@),
        ctx_kept(old(ctx)@, final(ctx)@),
))]
pub(crate) fn match_terms(
    s: &TermStore,
    a: Term,
    b: Term,
    ctx: &mut Ctx,
    visited: &mut HashSet<(Term, Term)>,
) -> bool {
    proof! { axiom_terms_are_ordered(); }
    let mut stack = vec![(a, b)];
    #[cfg_attr(verus_keep_ghost, verus_spec(invariant
        s.wf(),
        forall|i: int| 0 <= i < stack@.len() ==> s.has((#[trigger] stack@[i]).0) && s.has(stack@[i].1),
        ctx_ok(s, ctx@),
        ctx_kept(old(ctx)@, ctx@),
    ))]
    while let Some((x, y)) = stack.pop() {
        if s.is_ground(x) {
            if x == y {
                continue;
            }
            return false;
        }
        // Equal non-ground terms are still traversed, to bind each of
        // their parameters to itself.
        if !visited.insert((x, y)) {
            continue;
        }
        if s.num_children(x) == 0 {
            if s.kind(x) != Kind::PARAM {
                return false;
            }
            // The types of x and y are not compared here.
            match ctx.get(&x) {
                None => {
                    ctx.insert(x, y);
                }
                Some(&prev) => {
                    if prev != y {
                        return false;
                    }
                }
            }
        } else {
            if s.num_children(x) != s.num_children(y) || s.kind(x) != s.kind(y) {
                return false;
            }
            let (xs, ys) = (s.children(x), s.children(y));
            #[cfg_attr(verus_keep_ghost, verus_spec(invariant
                xs@.len() == ys@.len(),
                forall|i: int| 0 <= i < xs@.len() ==> s.has(#[trigger] xs@[i]),
                forall|i: int| 0 <= i < ys@.len() ==> s.has(#[trigger] ys@[i]),
                forall|i: int| 0 <= i < stack@.len() ==> s.has((#[trigger] stack@[i]).0) && s.has(stack@[i].1),
            ))]
            for i in 0..xs.len() {
                stack.push((xs[i], ys[i]));
            }
        }
    }
    true
}

/// What looking for the case of a program that matches gave.
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) enum CaseMatch {
    /// The body of the first case whose patterns match the arguments.
    Body(Term),
    /// A case, with this pattern, takes another number of arguments.
    BadArity(Term),
    /// No case matches.
    NoCase,
}

/// Finds the first case of the program `prog` whose patterns match the
/// arguments `children[1..]`, and fills `new_ctx` with the match. A program
/// is a list of cases, each a pair of a pattern, which is an application of
/// the program's symbol, and a body.
#[cfg_attr(verus_keep_ghost, verus_verify, verifier::loop_isolation(false), verus_spec(r =>
    requires
        s.wf(),
        s.has(prog),
        is_program(s, prog),
        forall|i: int| 0 <= i < children@.len() ==> s.has(#[trigger] children@[i]),
        ctx_ok(s, old(new_ctx)@),
    ensures
        ctx_ok(s, final(new_ctx)@),
        r matches CaseMatch::Body(t) ==> s.has(t),
        r matches CaseMatch::BadArity(t) ==> s.has(t),
))]
// an indexed loop, which Verus follows without a specification of `enumerate`
#[allow(clippy::needless_range_loop)]
pub(crate) fn match_cases(
    s: &TermStore,
    prog: Term,
    children: &[Term],
    new_ctx: &mut Ctx,
) -> CaseMatch {
    let nargs = children.len();
    #[cfg_attr(verus_keep_ghost, verus_spec(invariant ctx_ok(s, new_ctx@)))]
    for i in 0..s.num_children(prog) {
        let case = s.child(prog, i);
        new_ctx.clear();
        let pat = s.child(case, 0);
        if nargs != s.num_children(pat) {
            return CaseMatch::BadArity(pat);
        }
        let mut matched = true;
        #[cfg_attr(verus_keep_ghost, verus_spec(invariant ctx_ok(s, new_ctx@)))]
        for j in 1..nargs {
            // each argument is matched with its own set of visited pairs
            let mut visited = HashSet::new();
            let pj = s.child(pat, j);
            if !match_terms(s, pj, children[j], new_ctx, &mut visited) {
                matched = false;
                break;
            }
        }
        if matched {
            return CaseMatch::Body(s.child(case, 1));
        }
    }
    CaseMatch::NoCase
}

#[cfg(verus_keep_ghost)]
verus! {

/// Every parameter bound in the substitution, and every term it is bound
/// to, is a term of the store.
pub open spec fn ctx_ok(s: &TermStore, ctx: Map<Term, Term>) -> bool {
    forall|k: Term| #[trigger] ctx.contains_key(k) ==> s.has(k) && s.has(ctx[k])
}

/// Matching only adds bindings: what was bound stays bound to the same
/// term.
pub open spec fn ctx_kept(before: Map<Term, Term>, after: Map<Term, Term>) -> bool {
    forall|k: Term| #[trigger] before.contains_key(k) ==> after.contains_key(k) && after[k] == before[k]
}

/// The term has the shape of a program: each of its children, the cases,
/// has a pattern and a body.
pub open spec fn is_program(s: &TermStore, prog: Term) -> bool {
    forall|i: int| 0 <= i < s.kids(prog.idx()).len() ==> s.kids((#[trigger] s.kids(prog.idx())[i]).idx()).len() >= 2
}

/// Assumed: the derived order of term handles is a total order that agrees
/// with their equality, which is what a `BTreeMap` keyed by them needs to
/// behave as a map.
#[verifier::external_body]
pub proof fn axiom_terms_are_ordered()
    ensures vstd::laws_cmp::obeys_cmp::<Term>(),
{
}

} // verus!
