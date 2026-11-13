# Review: milestone 1 term store

Reviewed 2026-11-13, at `m1-spike` commit `f898b94`, file
`crates/pathos-term/src/store.rs`. The reviewer was a separate Claude session
(Opus 5.5), not the session that wrote the code.

**Verdict:** the design is approved. Fix the three findings below, and add
the two Latin-1 guardrails, at the start of milestone 2. None of them affects
any harness case.

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

## Latin-1 strings: accepted, with two guardrails to add

Decided by the user on 2026-11-13. pathos holds input bytes as the `char`s
with the same numbers (`pathos_syntax::latin1`). This was reviewed
separately from the term store.

**Why it is kept.** It works: besides the gate-1 probes, four more probes
with quoted symbols containing non-ASCII and non-UTF-8 bytes (`|caf\xe9|`,
`|\xff\x85\xa0|`, UTF-8 `\xc3\xa9`), errors after them on the same line,
and string literals with high bytes all gave output byte-identical to Ethos's,
column numbers included. It keeps `format!`, `&str` and string-keyed maps
usable, and it needs no dependency: `bstr` would bring `memchr`, which
contains `unsafe` code.

**Its risks.**

- The type does not enforce the invariant: a `String` can hold any `char`,
  and `latin1::encode` silently writes `?` for one above 255.
- Rust's `char` and `str` methods follow Unicode, unlike Ethos's byte-based
  C++. `char::is_whitespace` is true for 0x85 and 0xA0, `is_alphabetic` for
  0xE9, and `trim` and `split_whitespace` use the same rules. pathos uses
  only ASCII checks today.
- Bytes 0x80 to 0xFF take two bytes in a `String`, so slicing at a computed
  byte offset can split a `char` and panic. The current slices all follow an
  ASCII prefix (`#x`, `#b`, `:`) and are safe.

**Guardrails to add,** with the findings above:

4. **Forbid the Unicode-sensitive methods with Clippy.** Use
   `disallowed-methods` in `clippy.toml`, with a reason pointing here, for at
   least `char::is_whitespace`, `char::is_alphabetic`, `char::is_alphanumeric`,
   `char::is_numeric`, `char::is_lowercase`, `char::is_uppercase`,
   `char::to_lowercase`, `char::to_uppercase`, `str::trim`, `str::trim_start`,
   `str::trim_end`, `str::split_whitespace`, `str::to_lowercase` and
   `str::to_uppercase`. Use the `is_ascii_*` and `*_matches` forms instead. If
   a use is genuinely needed, allow it at that line and say why.
5. **Make a `char` above 255 in `latin1::encode` fail loudly in debug builds
   and tests** (`debug_assert!`), instead of being silently written as `?`.

Converting to byte strings (`Vec<u8>` behind a pathos type) remains possible
later. It is not worth the churn while the harness passes.

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
- **Latin-1 strings: decided 2026-11-13,** accepted with the guardrails
  above.
- **The changed crate boundaries** from the gate-1 report. The reviewer would
  accept them; the user's decision comes with the next instructions.

## Changes made since the gate report

- The harness measured peak memory wrongly: about 30 MiB too much, as the
  gate report suspected. Fixed in `daniel-larraz/ethos` at `c25bfbf8`, and
  `difftest.env` now pins that commit (commit `840c7ad` on this branch,
  `429fcd2` on `main`). With the fix, pathos's peak memory is 36% of Ethos's
  in the median case and 68% at worst, over the 588 cases both accept.
- The harness compared output after replacing every invalid UTF-8 byte with
  U+FFFD, and trimmed and split lines with Python's Unicode rules. So it
  could not tell `\xe9` from `\xff` in output, and ignored a trailing U+00A0.
  It now compares bytes exactly: `daniel-larraz/ethos` at `34b9dc92`, pinned
  in `difftest.env`. pathos still agrees with Ethos on all 630 cases.
