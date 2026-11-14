# pathos: brief

pathos is a reimplementation of the [Ethos](https://github.com/cvc5/ethos)
proof checker in Rust. It has three goals:

1. **Behave exactly like Ethos:** same verdicts and same error messages, on
   the same inputs. A differential testing harness decides what "the same"
   means.
2. **Be memory safe**, unlike the C++ (see "Memory safety" below).
3. **Be about as fast as Ethos and use no more memory.**

pathos is done when the harness reports no differences, the memory-safety
requirements hold, and the performance gate passes.

Background, with measurements behind the design choices below:
[Ethos: current architecture and a Rust reimplementation](https://claude.ai/artifact/BXXqKmQ3n9p853PbNi8U6z)
(written 2026-11-12).

## The reference

- **Behaviour:** Ethos at `REFERENCE_REV` in `difftest.env`: `cvc5/ethos`
  main at `9217112f`, which includes PR #223.
- **Source:** `$ETHOS_HARNESS/src` (about 14,000 lines of C++). Read it, never
  change it.
- **Specification:** `$ETHOS_HARNESS/user_manual.md`. Where the manual and the
  C++ disagree, the C++ wins: match the binary.
- **Out of scope for now:** `$ETHOS_HARNESS/plugins` (the eoc compiler and the
  C++ signature compiler) and the plugin interface in `src/plugin.h`.

Where the main pieces are in the C++:

| Area | C++ files |
| --- | --- |
| Entry point, options, verdict | `main.cpp`, `state.h` (`Options`) |
| Lexer and tokens | `lexer.*`, `tokens.*`, `input.*` |
| Commands and terms | `cmd_parser.*`, `expr_parser.*`, `parser.*` |
| Terms, kinds, literals, attributes | `expr.*`, `kind.*`, `literal.*`, `attr.*`, `expr_info.h`, `expr_trie.h` |
| Symbol tables, scopes, overloads, proof state | `state.*` |
| Typing, matching, evaluation, list operators | `type_checker.*` |
| Numbers and strings | `util/` |

## The harness

`tools/difftest` on branch `difftest-harness` of `daniel-larraz/ethos`,
pinned in `difftest.env`. Its README says exactly what is compared: outcome,
error text without the C++ `Fatal failure within` line, and stdout unless the
run ends in an error. Exit codes are not compared.

`scripts/difftest <gate>` builds pathos in release mode and runs the
harness. It refuses to run if the harness checkout, the reference binary or
the proof corpus is not the pinned one. Inputs:

- Ethos's 230 regressions (`tests/*.eo`, `tests/*.smt2`), run without options.
- 400 cvc5 proofs from cvc5 `2107a003` (29 areas of cvc5's regressions),
  each including the full CPC signature.

## Design decisions

These were made deliberately; change one only with the user's agreement.

1. **Terms are `Copy` handles into an arena.** A `Term` is a `u32` index into a
   `TermStore`. Every term is hash-consed, so structural equality is `==` on
   handles. This replaces the C++'s reference-counted pointers.
2. **The arena never frees, to start with.** Measured on cvc5 proofs: never
   freeing used 2–16% more peak memory than Ethos and was never slower.
   Freeing everything recursively saved up to 44% memory but was up to 56%
   slower. A Rust arena prototype used 88 bytes per term against Ethos's
   about 215. If memory becomes a problem, add mark-and-sweep at proof-step
   or scope boundaries. Don't use `Rc` terms: dropping one frees its whole
   subtree, which is the slow policy.
3. **Term contents are enums.** Something like a `TermData` enum whose
   variants carry their data, a `Lit` enum for literals and an `EvalOp` enum
   for the `eo::` operators, instead of the C++'s single `Kind` plus a child
   vector and a `Literal` subclass with a hand-managed union. The exact
   variants are yours to design.
4. **Applications stay curried and binary.** `(f a b)` is
   `APPLY(APPLY(f, a), b)` in the C++. Partial application, nil terminators
   and the list operators depend on it.
5. **Errors are values.** `Result` with source spans everywhere; no
   `panic!` or `process::exit` on bad input. The binary maps errors to
   messages identical to the C++ ones. The exit code may differ from the
   C++, which aborts.
6. **No global state.** The store and the checker state are passed
   explicitly. The C++ has a static `State*`.
7. **Deterministic order.** The C++ orders some sets and maps by pointer
   address (`Expr::operator<`). pathos orders by term id, which is creation
   order. If the harness ever shows an output that depends on the C++'s
   address order, stop and report it rather than imitate it.
8. **Traversals are iterative.** Matching, typing and evaluation use explicit
   stacks, as in the C++. cvc5 proofs contain terms deep enough to overflow
   the call stack.
9. **Numbers use `malachite`** (`malachite-nz` for integers, `malachite-q`
   for rationals), wrapped in pathos's own types so the library can be
   swapped. It is pure Rust and denies `unsafe` except for an AVX2 FFT path
   used for very large multiplications. GMP, used through `rug`, would bring
   C code and abort on allocation failure. Division, modulo and rounding must
   match GMP's results in the C++ exactly.
10. **No `unsafe` in pathos.** `unsafe_code = "forbid"` is set for the
    workspace. See "Memory safety" below for dependencies.
11. **Crates.** `pathos-term` (term store, literals, numbers),
    `pathos-syntax` (lexer, parser, spans), `pathos-elab` (scopes,
    overloading, attributes: from syntax to terms), `pathos-check` (typing,
    matching, evaluation, proof steps) and the `pathos` binary. Parsing and
    checking cannot be separate passes, because declarations, attributes and
    overload resolution change how later input is parsed. The crates separate
    responsibilities, not phases. Adjust the boundaries if the code shows a
    better split, and say why.

## Memory safety

Ethos manages its term graph by hand and has had memory bugs as a result
(PRs #223 and #256 fixed two). pathos must not have that class of bug:

- **No `unsafe` code in pathos's crates.** The workspace forbids it; never
  relax the lint.
- **Every dependency's `unsafe` code is accounted for.** Keep
  `docs/dependencies.md` listing each dependency, direct and indirect, whether
  it contains `unsafe` code and where, and why it is acceptable. Prefer
  crates without `unsafe`. Adding a dependency that contains `unsafe`, or
  that binds C code, needs the user's agreement. Known case: `malachite-nz`
  denies `unsafe` except in its AVX2 FFT, which calls CPU intrinsics after
  checking CPU support and is used only for very large multiplications.
- **No C or C++ code**, so no GMP. That is why numbers use `malachite`, not
  `rug`.
- **Bad input never causes undefined behaviour.** It produces an error, as
  in Ethos. Panics on bad input are bugs too, even though they are memory
  safe: they lose the error message the harness compares. Stack exhaustion is
  avoided by iterative traversals (decision 8).

At every gate, check that `docs/dependencies.md` matches `Cargo.lock`, and
report any change.

## Milestones

Each gate ends with a stop for the user's review. Stopping there is
intended; everything between gates is not.

1. **Spike.** Term store, lexer, parser, and enough elaboration and checking
   for `scripts/difftest gate1` to pass: 30 small regressions, 19 accepted
   and 11 rejected by Ethos. Also a micro-benchmark that interns about
   4 million terms of realistic shape (mostly binary applications, each with
   a cached type) and reports time and peak memory. **At this gate the user
   reviews the term store before anything more is built on it.**
2. **All regressions:** `scripts/difftest tests`.
3. **The CPC signature loads:** `scripts/difftest gate3`.
4. **All proofs:** `scripts/difftest proofs`.
5. **Performance:** `scripts/difftest perf` reports time and peak memory
   within a margin the user sets at this gate. Profile before optimizing.
   The margin set at gate 5: total time no more than Ethos's; no case taking
   over 50 ms in Ethos more than 10% slower; peak memory no more than
   Ethos's on any case.
6. **Large proofs:** `scripts/difftest large`, the 43 proofs of 1 MB or more
   from cvc5's `regress1` to `regress4` (up to 453 MB), agree, and
   `scripts/difftest perf`, which includes them, stays within the gate-5
   margin.
7. **Options:** `scripts/difftest options` agrees: every regression and
   default-corpus proof under each of Ethos's eight non-default options and
   under all of them together (6,300 runs). Not covered: the `--stats`
   options, `--help`, `--show-config`, `--include=` and `--reference=`.
8. **Fuzzing findings:** `scripts/difftest fuzz` reports no finding that
   still differs. The findings are mutated inputs on which pathos and Ethos
   behaved differently, kept in the harness under
   `tools/difftest/fuzz-findings/`; `docs/reviews/fuzz-1.md` sorts the first
   set by cause. Where Ethos crashes (a segmentation fault, not its normal
   abort on errors), pathos cannot match it; it must still terminate with an
   error, without a panic or a hang. Once the gate passes, add it to CI
   (it runs without the cvc5 corpus and skips the findings that need it).

At every gate, also run `cargo test` and `cargo clippy --all-targets` and
report their results.

## Out of scope until the gates pass

- Changes to what Ethos accepts or rejects, including fixes to Ethos bugs.
  Note them in `docs/ethos-differences.md` instead.
- Speed-ups that could change behaviour, such as compiling program cases
  into decision trees or caching evaluations across calls.
- Plugins and the eoc compiler.
- The `--stats` options, whose output contains timings.
