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
   under all of them together (6,300 runs). The `--stats` options and the
   command line are gate 9.
8. **Fuzzing findings:** `scripts/difftest fuzz` reports no finding that
   still differs. The findings are mutated inputs on which pathos and Ethos
   behaved differently, kept in the harness under
   `tools/difftest/fuzz-findings/`; `docs/reviews/fuzz-1.md` sorts the first
   set by cause. Where Ethos crashes (a segmentation fault, not its normal
   abort on errors), pathos cannot match it; it must still terminate with an
   error, without a panic or a hang. Once the gate passes, add it to CI
   (it runs without the cvc5 corpus and skips the findings that need it).
9. **Command line and statistics:** `scripts/difftest cli` agrees: the
   harness's 38 command-line cases (`CLI_CASES` in `difftest.py`, inputs in
   `tools/difftest/cli/`: `--help`, `-t`, `-v`, unknown options, standard
   input, `--include=`, `--reference=`), and every regression and
   default-corpus proof under `--stats`, `--stats-all`, `--stats-compact`
   and the last two together. The statistics are compared with times and
   Ethos's term-store counters (`mkExprCount`, `newExprCount`,
   `deleteExprCount`, `symCount`, `litCount`) masked: pathos prints those
   lines with its own numbers, and must match the rest, including which
   rules and programs are listed (with Ethos's names for the programs it
   generates, such as `$eo_prog_<rule>`) and how often each ran. Rows are
   compared sorted by name. Once the gate passes, add to CI
   `scripts/difftest tests --cli --stats-option-sets`, which needs no
   corpus. Not covered: `--show-config`, which prints pathos's own name and
   version.
10. **Signature snapshots** (in place of Ethos's `plugins/cpp_compiler`,
    which builds a custom Ethos with a signature compiled in so that it is
    not parsed again; only the loading speed is wanted, not that build). A
    snapshot is the term store and symbol tables after loading a
    signature, saved to a file:
    - `pathos --write-snapshot=FILE SIG.eo` loads the signature and writes
      the snapshot, printing nothing else.
    - `pathos --snapshot=FILE [options] INPUT` loads the snapshot before
      reading the input. An include of a file the snapshot holds (same
      canonical path and content) is then skipped, as Ethos skips a file
      included twice. The snapshot records a content hash of every file it
      holds, the options that affect parsing, and pathos's version; if
      anything differs, or the file is not a valid snapshot (truncated,
      corrupt, empty, another version), pathos ignores it and parses as
      usual. Ignoring it is silent: the output must be what it would be
      without the option. Reading a snapshot is input like any other: no
      panic, no `unsafe`, no allocation sized by the file without a bound.
    - Behaviour with a snapshot is identical to parsing, including the order
      of terms, which shows in the order of some warnings and contexts:
      writing out the store and reading it back as it is keeps that order.

    The gate, `scripts/difftest snapshot`, writes a snapshot of the corpus's
    CPC signature, then compares pathos with `--snapshot` against Ethos
    without it on the regressions and the proofs under every option set
    (6,300 runs; the regressions do not include CPC, so they exercise the
    fallback), and on the proofs with a truncated, a corrupted and an empty
    snapshot. It prints the candidate's time on the proofs with and without
    the snapshot, one job at a time: the target is to save most of the
    10 ms pathos spends loading CPC, on proofs whose median is 25 ms in
    Ethos. The option names are a proposal: the Ethos developers may want
    others, so keep them in one place.
11. **eoc: the plugin interface and the first stages.** Ethos's compiler
    plugins (`plugins/`) run in `ethos-eoc`, which eoc's Python driver
    (`tools/eoc/driver.py`) calls once per stage. Add:
    - a `Plugin` trait with Ethos's hooks (`src/plugin.h`: include, bind,
      define, define a program, mark a constructor kind, set a literal type
      rule, evaluate, notify of assumptions and steps, echo, finalize),
      called from the same places in pathos as in Ethos;
    - a `pathos-eoc` binary with `ethos-eoc`'s command line
      (`plugins/main_eoc.cpp`: `--plugin.<name>`, `--semantics=`,
      `--smt-semantics=`, `--lean-config=`, `--no-parser`, the Ethos
      options it accepts, and its errors), reading the same environment
      variables (`ETHOS_PLUGIN_ROOT`, `ETHOS_PLUGIN_OUTPUT_DIR`) and the same
      templates from the reference source tree;
    - the stages `trim-defs` and `desugar`.

    The gate, `scripts/difftest eoc`, runs eoc's driver with `ethos-eoc` and
    with `pathos-eoc` and compares the outcome, the messages and every file
    each run leaves, byte for byte (the harness's `eoc.py`): every rule of
    the Ethos test signatures under the test semantics, and logos's CPC
    under logos's semantics (https://github.com/cvc5/logos, pinned in
    `difftest.env`; logos is what uses eoc). For this milestone,
    `scripts/difftest eoc --filter '/(trim-defs|desugar|desugar-eo)(/|$)'`
    agrees. Logos's own check, `install/install-cpc.sh --all --cached
    --check`, is the acceptance test at the end of the eoc milestones.
12. **eoc: `model-smt` and `smt-meta`.** The stages that write the
    verification conditions: `model-smt`, and `smt-meta` with
    `smt-meta-sygus`. A `vc` run needs both, so they come together.
    `scripts/difftest eoc --filter
    '/(trim-defs|desugar|desugar-eo|vc|sygus)(/|$)'` agrees. Also give
    `pathos-eoc` the fallback `ethos-eoc` has for `ETHOS_PLUGIN_ROOT` and
    `ETHOS_PLUGIN_OUTPUT_DIR` (directories compiled in), with the
    environment variables still taking precedence: eoc's driver sets
    neither, and logos runs the driver as it is (see
    `docs/reviews/m11-eoc-plugins.md`).
13. **eoc: `lean-meta`**, with the `linear_patterns` utility it uses. The
    whole `scripts/difftest eoc` gate agrees (the `lean` runs and logos's
    `lean --all` included). Then the acceptance test: logos's
    `install/install-cpc.sh --all --cached --check`, run with `pathos-eoc`
    in place of `ethos-eoc` and nothing else changed, reports both packages
    up to date. Add the eoc gate to CI (it needs no cvc5 corpus; it needs
    the reference `ethos-eoc` built, as the regressions job builds the
    reference `ethos`, and a logos checkout at `LOGOS_REV`).

At every gate, also run `cargo test` and `cargo clippy --all-targets` and
report their results.

## Out of scope until the gates pass

- Changes to what Ethos accepts or rejects, including fixes to Ethos bugs.
  Note them in `docs/ethos-differences.md` instead.
- Speed-ups that could change behaviour, such as compiling program cases
  into decision trees or caching evaluations across calls.
- Plugins and the eoc compiler, except as milestones 10 to 13 describe.
