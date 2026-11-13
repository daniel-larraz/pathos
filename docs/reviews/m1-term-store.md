# Review: milestone 1 term store

Reviewed 2026-11-13, at `m1-spike` commit `f898b94`, file
`crates/pathos-term/src/store.rs`. The reviewer was a separate Claude session
(Opus 5.5), not the session that wrote the code.

**Verdict:** the design is approved. Fix the three findings below at the start
of milestone 2. None of them affects any harness case.

## What was checked

- **Benchmark, rerun:** `cargo run --release -p pathos-term --example
  intern_bench` gives 4 million terms, 26.2 bytes per term in the store's
  tables, 29.1 bytes per term peak memory and 125 ns per new term. This
  matches the gate report.
- **Flags against Ethos** (`ExprValue::computeFlags` in `src/expr.cpp`,
  `isLiteralOp` in `src/kind.cpp`): the rules are the same. Parameters and
  `eo::?` are non-ground. Program symbols and `eo::?` are evaluatable. Every
  `eo::` operator applied to at least one argument is evaluatable (Ethos's
  `isLiteralOp` covers all 56). A term with no children gets only its own
  kind's flags.
- **Literal interning against Ethos** (`State::mkLiteralInternal`): one term
  per value and kind. Decimal and rational, and hex and binary, stay
  distinct, as in Ethos's separate maps. `true` and `false` exist once.
- **Interning lookup:** it compares the kind tag and the children. The 13
  node kinds and 56 operators cannot collide. A binary `APPLY` stored inline
  and an `APPLY` of another arity in the child pool are looked up alike.
- **Sizes:** `Term` and `Option<Term>` are 4 bytes and `TermData` 12; the
  `layout` test confirms all three.

## Findings to fix

1. **The interning hash is fixed and unseeded** (`mix` and `hash_node`, and
   the probing loop in `TermStore::mk`). Every run hashes a term the same way,
   and collisions are resolved by linear probing. An input built so that many
   terms collide would make lookups scan long runs of entries, so checking
   time could grow quadratically. Ethos interns through a tree of sorted maps
   (`ExprTrie`), which cannot degrade like that. This matters only for proofs
   from untrusted sources, and no such input has been built.

   *Fix:* mix a seed into `hash_node`, chosen once per `TermStore`, for
   example from `std::collections::hash_map::RandomState`. Only the table's
   internal layout depends on it; nothing iterates the table in a way that
   reaches output, so verdicts and messages cannot change. Check that with
   the harness.

2. **Size limits are checked incompletely, and they panic.**
   - `mk` checks that a new node's start position in the child pool fits in
     a `u32`, but not start + length. `children_at` adds the two as `u32`.
     Past 4 billion pool entries that overflows: a release build then panics
     on a backwards slice, a debug build on the overflow itself.
   - Running out of term ids (`Term::from_index`), symbol name ids or literal
     ids is checked, but by `panic!` or `expect`.

   Reaching any of these takes tens of gigabytes, and none is a memory-safety
   hole. But the brief counts a panic on bad input as a bug.

   *Fix:* check start + length when creating the node. Make running out of
   ids an error that reaches the user as a message, unless that clutters
   every caller. If it would, explain the trade-off at the next gate. Match
   Ethos's message if Ethos has one; it most likely has none and simply runs
   out of memory.

3. **Each literal is stored twice:** in `lits` and as the key of `lit_map`
   (`TermStore::mk_lit`). That doubles the memory of large numbers and long
   strings. It is irrelevant for the current corpus.

   *Fix:* intern literals through an id-only table like `ConsTable`, keyed
   by the literal's hash and compared through `lits`.

## Accepted as is

- **Handles don't record which store they belong to.** A `Term` from another
  `TermStore` is accepted silently, or causes a panic if it is out of range.
  With one store per run this cannot happen. Revisit if pathos becomes a
  library that holds several stores.

## Decisions outside this review

- **The number library: decided 2026-11-13, keep `malachite` for now.** The
  user accepts the nine crates with `unsafe` code that it brings (see
  `docs/dependencies.md`). Keep numbers behind `num.rs` so that the library
  can still be swapped, and keep `docs/dependencies.md` current.
- **The changed crate boundaries** and **Latin-1 strings** from the gate-1
  report. The reviewer would accept both.

## Changes made since the gate report

- The harness measured peak memory wrongly: about 30 MiB too much, as the
  gate report suspected. Fixed in `daniel-larraz/ethos` at `c25bfbf8`, and
  `difftest.env` now pins that commit (commit `840c7ad` on this branch,
  `429fcd2` on `main`). With the fix, pathos's peak memory is 36% of Ethos's
  in the median case and 68% at worst, over the 588 cases both accept.
