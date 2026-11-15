//! Matching a pattern against a term, and finding the case of a program
//! that matches its arguments (`TypeChecker::match` and the loop of
//! `evaluateProgramInternal` in Ethos).
//!
//! These are functions of the term store alone, apart from the rest of the
//! checker, so that Verus can check them: see `docs/verus-spike.md`. It
//! proves that they cannot panic, that they end, that every term they read
//! or bind is a term of the store, and that a match they find is one: the
//! substitution applied to the pattern gives the term.

use std::collections::HashSet;

use pathos_term::{Kind, Term, TermStore};
#[cfg(verus_keep_ghost)]
use pathos_term::{SymbolKind, Tree, tree_is_ground};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

use crate::checker::Ctx;

/// Matches the pattern `a` against `b`, extending `ctx` so that `a`
/// instantiated by `ctx` is `b`. `visited` holds the pairs already
/// matched by earlier calls that share `ctx`.
///
/// Three things are as in Ethos, and the specification says so:
///
/// - the type of a parameter and the type of the term it is bound to are
///   not compared: matching is on the terms' trees alone;
/// - a ground pattern matches only itself;
/// - a pattern that is not ground and has no children matches only if it
///   is a parameter, so `eo::?` matches nothing.
#[cfg_attr(verus_keep_ghost, verus_verify, verifier::loop_isolation(false), verifier::rlimit(100), verus_spec(r =>
    requires
        s.wf(),
        s.has(a),
        s.has(b),
        ctx_ok(s, old(ctx)@),
        // the pairs seen before were matched, under this context
        closed(s, old(ctx)@, old(visited)@, Seq::empty()),
    ensures
        ctx_ok(s, final(ctx)@),
        ctx_kept(old(ctx)@, final(ctx)@),
        // a match found is a match: the context instantiates the pattern
        // to the term
        r ==> inst(s, final(ctx)@, a) == s.tree(b.idx()),
        r ==> is_match(s, final(ctx)@, a, b),
        r ==> closed(s, final(ctx)@, final(visited)@, Seq::empty()),
        // a ground pattern matches exactly itself
        tree_is_ground(s.tree(a.idx())) ==> r == (a == b),
        // a pattern without children that is not ground and not a
        // parameter does not match
        !tree_is_ground(s.tree(a.idx())) && s.kids(a.idx()).len() == 0 && !is_param(s, a) ==> !r,
))]
pub(crate) fn match_terms(
    s: &TermStore,
    a: Term,
    b: Term,
    ctx: &mut Ctx,
    visited: &mut HashSet<(Term, Term)>,
) -> bool {
    proof! {
        axiom_terms_are_ordered();
        axiom_term_pairs_are_keys();
        broadcast use vstd::std_specs::hash::group_hash_axioms;
        broadcast use vstd::std_specs::btree::group_btree_axioms;
        lemma_weight_push(s, Seq::empty(), (a, b));
        if !tree_is_ground(s.tree(a.idx())) && s.kids(a.idx()).len() == 0 && !is_param(s, a) {
            // such a pair cannot have been matched before
            assert(!good(s, old(ctx)@, old(visited)@, Seq::empty(), a, b));
        }
    }
    let mut stack = vec![(a, b)];
    proof_decl! {
        assert(stack@ =~= Seq::empty().push((a, b)));
        assert(stack@[0] == (a, b));
        // the stack as it was when the loop last came round
        let ghost mut head = stack@;
    }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            head == stack@,
            forall|i: int| 0 <= i < stack@.len() ==> s.has((#[trigger] stack@[i]).0) && s.has(stack@[i].1),
            ctx_ok(s, ctx@),
            ctx_kept(old(ctx)@, ctx@),
            closed(s, ctx@, visited@, stack@),
            stack@.contains((a, b)) || resolved(s, visited@, a, b),
            tree_is_ground(s.tree(a.idx())) ==>
                stack@ =~= seq![(a, b)] || (stack@.len() == 0 && a == b),
            !tree_is_ground(s.tree(a.idx())) && s.kids(a.idx()).len() == 0 && !is_param(s, a) ==>
                stack@ =~= seq![(a, b)] && !visited@.contains((a, b)),
        decreases stack_weight(s, stack@),
    ))]
    while let Some((x, y)) = stack.pop() {
        proof_decl! {
            let ghost before = stack@.push((x, y));
            let ghost seen = visited@;
            let ghost bound = ctx@;
            assert(before =~= head);
            assert(before[before.len() - 1] == (x, y));
            assert(closed(s, bound, seen, before));
            lemma_weight_push(s, stack@, (x, y));
            lemma_size_positive(s, x);
            assert forall|p: (Term, Term)| #[trigger] before.contains(p) implies stack@.contains(p) || p == (x, y) by {
                let i = choose|i: int| 0 <= i < before.len() && before[i] == p;
                if i < stack@.len() {
                    assert(stack@[i] == p);
                }
            }
        }
        if s.is_ground(x) {
            if x == y {
                proof! {
                    lemma_closed_step(s, bound, bound, seen, seen, before, stack@);
                    head = stack@;
                }
                continue;
            }
            return false;
        }
        // Equal non-ground terms are still traversed, to bind each of
        // their parameters to itself.
        if !visited.insert((x, y)) {
            proof! {
                assert(visited@ =~= seen);
                lemma_closed_step(s, bound, bound, seen, seen, before, stack@);
                head = stack@;
            }
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
            proof! {
                assert(good(s, ctx@, visited@, stack@, x, y));
                lemma_closed_step(s, bound, ctx@, seen, visited@, before, stack@);
                head = stack@;
            }
        } else {
            if s.num_children(x) != s.num_children(y) || s.kind(x) != s.kind(y) {
                return false;
            }
            let (xs, ys) = (s.children(x), s.children(y));
            proof_decl! {
                let ghost rest = stack@;
                s.lemma_children(x);
            }
            #[cfg_attr(verus_keep_ghost, verus_spec(invariant
                xs@.len() == ys@.len(),
                stack@.len() == rest.len() + i,
                forall|m: int| 0 <= m < stack@.len() ==> s.has((#[trigger] stack@[m]).0) && s.has(stack@[m].1),
                forall|m: int| 0 <= m < rest.len() ==> stack@[m] == #[trigger] rest[m],
                forall|m: int| 0 <= m < i ==> stack@[rest.len() + m] == (xs@[m], ys@[m]),
                stack_weight(s, stack@) == stack_weight(s, rest) + kids_size(s, x, i as int),
            ))]
            for i in 0..xs.len() {
                proof! { lemma_weight_push(s, stack@, (xs@[i as int], ys@[i as int])); }
                stack.push((xs[i], ys[i]));
            }
            proof! {
                assert forall|m: int| 0 <= m < xs@.len() implies
                    stack@.contains((#[trigger] s.kids(x.idx())[m], s.kids(y.idx())[m])) by {
                    assert(stack@[rest.len() + m] == (xs@[m], ys@[m]));
                }
                assert forall|p: (Term, Term)| #[trigger] rest.contains(p) implies stack@.contains(p) by {
                    let i = choose|i: int| 0 <= i < rest.len() && rest[i] == p;
                    assert(stack@[i] == p);
                }
                assert(good(s, ctx@, visited@, stack@, x, y));
                lemma_closed_step(s, bound, ctx@, seen, visited@, before, stack@);
                head = stack@;
            }
        }
    }
    proof! {
        assert(stack@ =~= Seq::empty());
        lemma_inst(s, ctx@, visited@, a, b);
    }
    true
}

/// Whether `prog` has the shape of a program: each of its children, the
/// cases, has a pattern and a body, and the pattern is an application, with
/// a head. The parser builds programs so; a snapshot is checked with this.
#[cfg_attr(verus_keep_ghost, verus_verify, verifier::loop_isolation(false), verus_spec(r =>
    requires s.wf(), s.has(prog),
    ensures r ==> is_program(s, prog) && has_patterns(s, prog),
))]
pub(crate) fn is_program_term(s: &TermStore, prog: Term) -> bool {
    #[cfg_attr(verus_keep_ghost, verus_spec(invariant
        forall|m: int| 0 <= m < i ==> case_ok(s, #[trigger] s.kids(prog.idx())[m]),
    ))]
    for i in 0..s.num_children(prog) {
        let case = s.child(prog, i);
        if s.num_children(case) < 2 || s.num_children(s.child(case, 0)) == 0 {
            return false;
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
        // the first is the program's symbol
        children@.len() >= 1,
        ctx_ok(s, old(new_ctx)@),
    ensures
        ctx_ok(s, final(new_ctx)@),
        r matches CaseMatch::BadArity(t) ==> s.has(t),
        // the body returned is that of a case whose patterns the context
        // instantiates to the arguments
        r matches CaseMatch::Body(t) ==> s.has(t) && exists|i: int|
            0 <= i < s.kids(prog.idx()).len() && #[trigger] case_matches(s, final(new_ctx)@, s.kids(prog.idx())[i], children@, t),
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
        #[cfg_attr(verus_keep_ghost, verus_spec(invariant
            ctx_ok(s, new_ctx@),
            matched ==> forall|m: int| 1 <= m < j ==> is_match(s, new_ctx@, #[trigger] s.kids(pat.idx())[m], children@[m]),
            invariant_except_break matched,
        ))]
        for j in 1..nargs {
            // each argument is matched with its own set of visited pairs
            let mut visited = HashSet::new();
            let pj = s.child(pat, j);
            proof_decl! {
                let ghost bound = new_ctx@;
                s.lemma_children(pat);
            }
            if !match_terms(s, pj, children[j], new_ctx, &mut visited) {
                matched = false;
                break;
            }
            proof! {
                // what the earlier arguments matched still holds
                assert forall|m: int| 1 <= m < j implies
                    is_match(s, new_ctx@, #[trigger] s.kids(pat.idx())[m], children@[m]) by {
                    lemma_matched_kept(s, bound, new_ctx@, s.kids(pat.idx())[m], children@[m]);
                }
            }
        }
        if matched {
            proof! {
                s.lemma_children(pat);
                assert forall|m: int| 1 <= m < nargs implies
                    inst(s, new_ctx@, #[trigger] s.kids(pat.idx())[m]) == s.tree(children@[m].idx()) by {
                    lemma_matched_inst(s, new_ctx@, s.kids(pat.idx())[m], children@[m]);
                }
                let body = s.kids(case.idx())[1];
                assert(case == s.kids(prog.idx())[i as int]);
                assert(pat == s.kids(case.idx())[0]);
                assert(s.kids(case.idx()).len() >= 2);
                assert(s.kids(pat.idx()).len() == children@.len());
                assert(case_matches(s, new_ctx@, s.kids(prog.idx())[i as int], children@, body));
                s.lemma_children(case);
                assert(s.has(body));
                assert(0 <= i < s.kids(prog.idx()).len());
                assert(exists|i2: int| 0 <= i2 < s.kids(prog.idx()).len()
                    && #[trigger] case_matches(s, new_ctx@, s.kids(prog.idx())[i2], children@, body));
            }
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

/// A case has a pattern and a body, and the pattern has a head.
pub open spec fn case_ok(s: &TermStore, case: Term) -> bool {
    s.kids(case.idx()).len() >= 2 && s.kids(s.kids(case.idx())[0].idx()).len() >= 1
}

/// Every case of the program has a pattern with a head.
pub open spec fn has_patterns(s: &TermStore, prog: Term) -> bool {
    forall|i: int| 0 <= i < s.kids(prog.idx()).len() ==> case_ok(s, #[trigger] s.kids(prog.idx())[i])
}

/// The term is a parameter.
pub open spec fn is_param(s: &TermStore, x: Term) -> bool {
    s.kind_of(x.idx()) == Kind::Symbol(SymbolKind::Param)
}

// ---- what a match is ----

/// The pattern `x` with the substitution `ctx` applied, as a tree: a
/// parameter that `ctx` binds becomes the tree of the term it is bound to,
/// a term with children is rebuilt from its instantiated children, and
/// anything else is its own tree.
///
/// Types play no part: as in Ethos, matching does not compare the type of a
/// parameter with the type of what it is bound to.
pub open spec fn inst(s: &TermStore, ctx: Map<Term, Term>, x: Term) -> Tree
    decreases x.idx(), 1nat,
{
    if is_param(s, x) {
        if ctx.contains_key(x) { s.tree(ctx[x].idx()) } else { s.tree(x.idx()) }
    } else if s.kids(x.idx()).len() > 0 {
        Tree::Node(s.kind_of(x.idx()), inst_children(s, ctx, x))
    } else {
        s.tree(x.idx())
    }
}

/// The instantiated children of `x`.
pub open spec fn inst_children(s: &TermStore, ctx: Map<Term, Term>, x: Term) -> Seq<Tree>
    decreases x.idx(), 0nat,
{
    Seq::new(s.kids(x.idx()).len(), |m: int| inst_child(s, ctx, x, s.kids(x.idx())[m]))
}

/// The instantiation of the child `c` of `x`. (A child is a term made
/// before its parent; the invariant of the store says so, and the test
/// here is what lets the definition recurse.)
pub open spec fn inst_child(s: &TermStore, ctx: Map<Term, Term>, x: Term, c: Term) -> Tree
    decreases x.idx(), 0nat, 0nat,
{
    if 0 < c.idx() < x.idx() { inst(s, ctx, c) } else { Tree::Null }
}

/// The pattern of a case instantiates to the arguments, and `body` is the
/// case's body. The first child of the pattern is the program's symbol; the
/// others are matched against `children[1..]`.
pub open spec fn case_matches(s: &TermStore, ctx: Map<Term, Term>, case: Term, children: Seq<Term>, body: Term) -> bool {
    let pat = s.kids(case.idx())[0];
    &&& s.kids(case.idx()).len() >= 2
    &&& body == s.kids(case.idx())[1]
    &&& s.kids(pat.idx()).len() == children.len()
    &&& forall|m: int| 1 <= m < children.len() ==>
            inst(s, ctx, #[trigger] s.kids(pat.idx())[m]) == s.tree(children[m].idx())
}

// ---- how the loop finds one ----

/// The pair needs no more work: the pattern is ground and is the term, or
/// the pair is among those seen.
pub open spec fn resolved(s: &TermStore, vis: Set<(Term, Term)>, x: Term, y: Term) -> bool {
    (tree_is_ground(s.tree(x.idx())) && x == y) || vis.contains((x, y))
}

/// What holds of a pair `(x, y)` that was seen: `x` is not ground, and
/// either it is a parameter bound to `y`, or `x` and `y` have the same kind
/// and number of children, and each pair of their children is still to be
/// looked at or needs no more work.
pub open spec fn good(s: &TermStore, ctx: Map<Term, Term>, vis: Set<(Term, Term)>, stack: Seq<(Term, Term)>, x: Term, y: Term) -> bool {
    &&& s.has(x)
    &&& s.has(y)
    &&& !tree_is_ground(s.tree(x.idx()))
    &&& if s.kids(x.idx()).len() == 0 {
        is_param(s, x) && ctx.contains_key(x) && ctx[x] == y
    } else {
        &&& s.kids(y.idx()).len() == s.kids(x.idx()).len()
        &&& s.kind_of(x.idx()) == s.kind_of(y.idx())
        &&& forall|m: int| 0 <= m < s.kids(x.idx()).len() ==>
                stack.contains((#[trigger] s.kids(x.idx())[m], s.kids(y.idx())[m]))
                    || resolved(s, vis, s.kids(x.idx())[m], s.kids(y.idx())[m])
    }
}

/// Every pair seen is good.
pub open spec fn closed(s: &TermStore, ctx: Map<Term, Term>, vis: Set<(Term, Term)>, stack: Seq<(Term, Term)>) -> bool {
    forall|p: (Term, Term)| #[trigger] vis.contains(p) ==> good(s, ctx, vis, stack, p.0, p.1)
}

/// `x` was matched against `y`: with nothing left to look at, the pair
/// needs no more work, for some set of pairs seen.
pub open spec fn is_match(s: &TermStore, ctx: Map<Term, Term>, x: Term, y: Term) -> bool {
    s.has(x) && s.has(y) && exists|vis: Set<(Term, Term)>|
        #[trigger] closed(s, ctx, vis, Seq::empty()) && resolved(s, vis, x, y)
}

/// One step of the loop keeps the pairs seen good: bindings are kept, pairs
/// seen stay seen, a pair taken off the stack needs no more work, and the
/// pairs newly seen are good.
proof fn lemma_closed_step(
    s: &TermStore,
    ctx: Map<Term, Term>,
    ctx2: Map<Term, Term>,
    vis: Set<(Term, Term)>,
    vis2: Set<(Term, Term)>,
    stack: Seq<(Term, Term)>,
    stack2: Seq<(Term, Term)>,
)
    requires
        closed(s, ctx, vis, stack),
        ctx_kept(ctx, ctx2),
        forall|p: (Term, Term)| vis.contains(p) ==> vis2.contains(p),
        forall|p: (Term, Term)| #[trigger] stack.contains(p) ==> stack2.contains(p) || resolved(s, vis2, p.0, p.1),
        forall|p: (Term, Term)| #[trigger] vis2.contains(p) && !vis.contains(p) ==> good(s, ctx2, vis2, stack2, p.0, p.1),
    ensures closed(s, ctx2, vis2, stack2),
{
    assert forall|p: (Term, Term)| #[trigger] vis2.contains(p) implies good(s, ctx2, vis2, stack2, p.0, p.1) by {
        if vis.contains(p) {
            assert(good(s, ctx, vis, stack, p.0, p.1));
            let (x, y) = p;
            if s.kids(x.idx()).len() > 0 {
                assert forall|m: int| 0 <= m < s.kids(x.idx()).len() implies
                    stack2.contains((#[trigger] s.kids(x.idx())[m], s.kids(y.idx())[m]))
                        || resolved(s, vis2, s.kids(x.idx())[m], s.kids(y.idx())[m]) by {
                    let q = (s.kids(x.idx())[m], s.kids(y.idx())[m]);
                    if stack.contains(q) {
                        assert(stack2.contains(q) || resolved(s, vis2, q.0, q.1));
                    }
                }
            }
        }
    }
}

/// A ground pattern instantiates to itself.
proof fn lemma_inst_ground(s: &TermStore, ctx: Map<Term, Term>, x: Term)
    requires s.wf(), s.has(x), tree_is_ground(s.tree(x.idx())),
    ensures inst(s, ctx, x) == s.tree(x.idx()),
    decreases x.idx(),
{
    s.lemma_children(x);
    if is_param(s, x) {
        s.lemma_tree_param(x);
    } else if s.kids(x.idx()).len() > 0 {
        s.lemma_tree_compound(x);
        let ks = s.kids(x.idx());
        let cs = s.tree(x.idx())->Node_1;
        assert forall|m: int| 0 <= m < ks.len() implies inst_children(s, ctx, x)[m] == #[trigger] cs[m] by {
            assert(tree_is_ground(cs[m]));
            lemma_inst_ground(s, ctx, ks[m]);
            assert(inst_child(s, ctx, x, ks[m]) == inst(s, ctx, ks[m]));
        }
        assert(inst_children(s, ctx, x) =~= cs);
    }
}

/// The theorem behind matching: once nothing is left to look at, a pair
/// that needs no more work is a match.
proof fn lemma_inst(s: &TermStore, ctx: Map<Term, Term>, vis: Set<(Term, Term)>, x: Term, y: Term)
    requires
        s.wf(),
        s.has(x),
        s.has(y),
        closed(s, ctx, vis, Seq::empty()),
        resolved(s, vis, x, y),
    ensures inst(s, ctx, x) == s.tree(y.idx()),
    decreases x.idx(),
{
    if tree_is_ground(s.tree(x.idx())) && x == y {
        lemma_inst_ground(s, ctx, x);
    } else {
        assert(vis.contains((x, y)));
        assert(good(s, ctx, vis, Seq::empty(), x, y));
        s.lemma_children(x);
        s.lemma_children(y);
        let (kx, ky) = (s.kids(x.idx()), s.kids(y.idx()));
        if kx.len() > 0 {
            if is_param(s, x) {
                s.lemma_tree_param(x);
            }
            s.lemma_tree_compound(y);
            let cs = s.tree(y.idx())->Node_1;
            assert forall|m: int| 0 <= m < kx.len() implies inst_children(s, ctx, x)[m] == #[trigger] cs[m] by {
                let q = (kx[m], ky[m]);
                assert(!Seq::<(Term, Term)>::empty().contains(q));
                assert(resolved(s, vis, kx[m], ky[m]));
                lemma_inst(s, ctx, vis, kx[m], ky[m]);
                assert(inst_child(s, ctx, x, kx[m]) == inst(s, ctx, kx[m]));
            }
            assert(inst_children(s, ctx, x) =~= cs);
        }
    }
}

/// A pair that was matched is a match.
proof fn lemma_matched_inst(s: &TermStore, ctx: Map<Term, Term>, x: Term, y: Term)
    requires s.wf(), is_match(s, ctx, x, y),
    ensures inst(s, ctx, x) == s.tree(y.idx()),
{
    let vis = choose|vis: Set<(Term, Term)>| #[trigger] closed(s, ctx, vis, Seq::empty()) && resolved(s, vis, x, y);
    lemma_inst(s, ctx, vis, x, y);
}

/// A pair that was matched stays matched when bindings are added.
proof fn lemma_matched_kept(s: &TermStore, ctx: Map<Term, Term>, ctx2: Map<Term, Term>, x: Term, y: Term)
    requires is_match(s, ctx, x, y), ctx_kept(ctx, ctx2),
    ensures is_match(s, ctx2, x, y),
{
    let vis = choose|vis: Set<(Term, Term)>| #[trigger] closed(s, ctx, vis, Seq::empty()) && resolved(s, vis, x, y);
    lemma_closed_step(s, ctx, ctx2, vis, vis, Seq::empty(), Seq::empty());
    assert(closed(s, ctx2, vis, Seq::empty()) && resolved(s, vis, x, y));
}

// ---- why the loop ends ----

/// The number of nodes of the tree of `x`, shared subterms counted each
/// time they occur.
pub open spec fn size(s: &TermStore, x: Term) -> nat
    decreases x.idx(), 1nat, 0int,
{
    1 + kids_size(s, x, s.kids(x.idx()).len() as int)
}

/// The sizes of the first `m` children of `x`, added up.
pub open spec fn kids_size(s: &TermStore, x: Term, m: int) -> nat
    decreases x.idx(), 0nat, m,
{
    if m <= 0 {
        0
    } else {
        let c = s.kids(x.idx())[m - 1];
        kids_size(s, x, m - 1) + (if 0 < c.idx() < x.idx() { size(s, c) } else { 0 })
    }
}

/// The sizes of the patterns on the stack, added up. Each turn of the loop
/// takes a pattern off and puts at most its children on, which are smaller
/// by one in all: so this goes down, and the loop ends.
pub open spec fn stack_weight(s: &TermStore, stack: Seq<(Term, Term)>) -> nat
    decreases stack.len(),
{
    if stack.len() == 0 {
        0
    } else {
        stack_weight(s, stack.drop_last()) + size(s, stack.last().0)
    }
}

proof fn lemma_weight_push(s: &TermStore, stack: Seq<(Term, Term)>, p: (Term, Term))
    ensures stack_weight(s, stack.push(p)) == stack_weight(s, stack) + size(s, p.0),
{
    assert(stack.push(p).drop_last() =~= stack);
}

proof fn lemma_size_positive(s: &TermStore, x: Term)
    ensures size(s, x) >= 1,
{
}

/// Assumed: the derived order of term handles is a total order that agrees
/// with their equality, which is what a `BTreeMap` keyed by them needs to
/// behave as a map.
#[verifier::external_body]
pub proof fn axiom_terms_are_ordered()
    ensures vstd::laws_cmp::obeys_cmp::<Term>(),
{
}

/// Assumed: the derived `Hash` and `Eq` of a pair of term handles agree,
/// which is what a `HashSet` of them needs to behave as a set.
#[verifier::external_body]
pub proof fn axiom_term_pairs_are_keys()
    ensures vstd::std_specs::hash::obeys_key_model::<(Term, Term)>(),
{
}

} // verus!
