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
14. **The evidence for replacing Ethos.** No change to what pathos does;
    this milestone writes down why the Ethos developers can trust it. The
    developers will replace Ethos with pathos if it is memory safe and does
    what Ethos does, so the documents answer exactly those two questions,
    for a reader who knows Ethos and C++ but not Rust or pathos.
    - **`docs/dependencies.md` up to date and traced.** Bring it in line
      with the current `Cargo.lock`. Then close its open question: which of
      the dependencies' `unsafe` code can pathos's calls reach? Trace it
      (by reading the call paths from the `malachite` functions pathos
      calls, helped by a tool such as `cargo geiger` if it works offline,
      or by building with the `unsafe` paths instrumented), and say for
      each crate: reached, not reached, or not known, with the evidence.
      Check whether a `malachite` feature, or a `[profile]`/`cfg` setting,
      can keep the AVX2 FFT (and so `wide`, `safe_arch`, `bytemuck`) out
      of the build, and what it costs on the `perf` gate. Do not change
      the dependencies: write the options down for the user, who signs the
      file off (its status line still says it awaits that).
    - **`docs/evidence.md`**, one page: what pathos is; the memory-safety
      statement (no `unsafe` in pathos, the workspace lint that enforces
      it, the dependencies in one paragraph with a link, no C or C++, bad
      input gives an error and never undefined behaviour, iterative
      traversals instead of recursion); and a table of every gate, with
      what it compares, the number of cases, the reference revision and
      the command that reruns it: `tests`, `proofs`, `large`, `options`,
      `cli`, `fuzz`, `snapshot`, `eoc`, logos's acceptance check, and
      `perf` with its numbers. Take the counts from runs you make for this
      milestone, not from the reviews. Then the differences from Ethos,
      summarised from `docs/ethos-differences.md` in three groups (Ethos
      crashes or reads out of bounds where pathos reports an error; output
      that differs by design; anything else), with a link for the details.
      Last, the questions for the developers: whether a snapshot is
      trusted like the signature it was made from (a crafted snapshot can
      make pathos panic after its checksum passes;
      `docs/reviews/m10-snapshots.md`), and whether to keep the
      evaluation hooks (`EvalPlugin`), which no eoc stage uses.
    - **Panics.** List every `panic!`, `unreachable!`, `expect`, `unwrap`
      and indexing that could fail on input in the non-test code, grouped
      by crate, and for each say why input cannot reach it or turn it into
      an error. Put the list in `docs/evidence.md`'s appendix or a file it
      links. Fix any that input can reach, with a test, only if the fix
      does not change output; otherwise list it.
    The gate: `scripts/full-check` (without `--quick`) and `scripts/difftest
    eoc` pass, and the two documents are complete. The reviewer runs a
    long fuzzing campaign alongside; its result goes into
    `docs/evidence.md` after the review.
15. **Every platform Ethos supports.** Ethos's CI (`.github/workflows/main.yml`
    at `REFERENCE_REV`, job `build`) builds and runs its regressions on six
    platforms, release and debug: `linux-x86_64` (`ubuntu-22.04`),
    `linux-arm64` (`ubuntu-22.04-arm`), `macOS-x86_64` (`macos-15-intel`),
    `macOS-arm64` (`macos-15`), `windows-x86_64` (`windows-latest`, MSYS2
    MINGW64) and `windows-arm64` (`windows-11-arm`, MSYS2 CLANGARM64). pathos
    has to work, and behave like Ethos, on all six. The repository is public,
    so these runners cost nothing.
    - **Build and test matrix.** A CI job over the same six runners:
      `cargo build --locked --release`, `cargo test --locked` (debug and
      release), and `scripts/unsafe-reach` where binutils are available.
      Release binaries statically linked where Ethos's are (`--static`:
      every release build), and uploaded as artifacts on pushes to `main`,
      as Ethos does. Use the native Rust toolchain per platform (MSVC or
      GNU on Windows: say which and why).
    - **Agreement with Ethos on each platform.** On each of the six, build
      the reference Ethos the way Ethos's CI does (GMP from apt, the
      Homebrew bottles it pins, or MSYS2) and run `scripts/difftest`'s
      `tests`, `cli`, `bignum` and `fuzz` gates there. The cvc5 corpora,
      `options`, `perf` and `eoc` stay on `linux-x86_64`. Where Ethos's own
      output differs by platform (how an abort is reported, path
      separators, line endings), pathos must match Ethos *on that
      platform*; record each such difference in `docs/ethos-differences.md`.
      The harness is not yours to change: it does not yet run on Windows
      (it uses `resource`, `os.wait4`, `killpg`, process sessions,
      `prlimit` and GNU time); the reviewer is porting it. Report what it
      needs, with the failing output, and work on the other platforms
      meanwhile.
    - **`unsafe` on arm64.** `docs/dependencies.md` traces x86-64 only. On
      aarch64, `malachite-nz` has no AVX2 kernels, `safe_arch` drops out and
      `wide` uses NEON intrinsics itself. Run `scripts/unsafe-reach` on both
      arm64 runners (and macOS x86-64, whose linker differs), and give
      `docs/dependencies.md` a reachability and soundness table per
      architecture, as for x86-64. `bignum` on arm64 exercises the FFT
      there. The status line goes back to awaiting Daniel's signature.
    - **Stack.** The main thread has a 1 MB stack on Windows and 8 MB on
      Linux and macOS. pathos's three remaining recursions stop at
      platform-dependent depths. Either show that on each platform they
      fail no differently from Ethos there, or run the checker on a thread
      with an explicit, large stack on every platform; say which, and
      measure the depths (the nested-include case of `docs/panics.md`).
    The gate: the matrix is green on all six platforms, the four gates agree
    with Ethos on each, `docs/dependencies.md` covers every architecture,
    and `docs/evidence.md` says which platforms are checked and how.
    The reviewer pushes branch `m15` to GitHub so that CI can run there;
    commit on `m15` and say when a run is wanted.
16. **The licence notice, and keeping up with Ethos.**
    - **LGPL.** The release binaries link `malachite` (LGPL-3.0-only)
      statically, and its crates ship no licence text. Do what Ethos does
      for GMP: add `licenses/lgpl-3.0.txt` (the FSF text; Ethos's copy is
      the same file), a paragraph in the licence notice saying that pathos
      links against `malachite`, which is under LGPL v3, and that pathos's
      source and the combined binary stay under the BSD licence (compare
      Ethos's `COPYING`), and include both in what `scripts/package` puts
      into the artifact.
    - **The drift job.** pathos matches `REFERENCE_REV`, but Ethos keeps
      changing. Add a scheduled workflow, separate from `ci.yml` and never
      blocking it, that each night builds Ethos at the current `main` of
      https://github.com/cvc5/ethos and compares pathos (at its `main`) with
      it on Linux x86-64: Ethos `main`'s own regressions (its `tests/`, not
      the harness's), the command-line cases, `bignum`, the fuzz replay, and
      the eoc gate on the test signatures with logos at its current `main`.
      Use the pinned harness, run its `difftest.py` directly where
      `scripts/difftest` insists on the pins, and change nothing pinned.
      The job's summary says which Ethos commit was compared, whether
      anything differs, and the differences (the JSON reports as
      artifacts); when Ethos `main` equals `REFERENCE_REV` it says so. It
      fails only when something differs, so a red nightly run means "Ethos
      has changed in a way pathos does not follow yet". It must also run on
      demand (`workflow_dispatch`). Document it in `README.md` and in
      `docs/evidence.md` ("Keeping up with Ethos"), including what to do
      when it is red: port the change, then move `REFERENCE_REV` (and the
      harness, if the change needs it) in a milestone of its own.
    The gate: the package contains the notices, and one on-demand run of the
    drift job is green against today's Ethos `main`. The reviewer pushes and
    starts the runs, as in milestone 15.
17. **A Verus feasibility spike.** Verus (https://github.com/verus-lang/verus)
    proves Rust code against specifications with an SMT solver. The long-term
    question is whether pathos can be verified to be sound: if it answers
    `correct`, every step follows from its premises by the rules of the
    signature. This milestone does not try that. It verifies two small,
    self-contained parts and measures what it costs, so that Daniel can
    decide whether to go further.
    - **Literal operators.** Functional specifications, against Verus's
      mathematical integers and rationals, for the evaluation of `eo::add`,
      `eo::neg`, `eo::mul`, `eo::zdiv`, `eo::zmod` and `eo::qdiv` on numerals
      and rationals, and of `eo::extract`, `eo::concat`, `eo::and`,
      `eo::or`, `eo::xor` and `eo::not` on binaries (widths, wrap-around,
      Ethos's division rules: the specification states what pathos does
      now, which is what Ethos does). `malachite` stays trusted: state what
      pathos relies on from it as assumed specifications
      (`assume_specification` or `external_body`), each one listed.
    - **The term store.** The invariant that every handle the store gives
      out is valid, and that its view, from handles to trees, is injective
      (the same tree always gets the same handle), with the store's own code
      free of panics.
    - **The setup.** Install Verus at a pinned release, decide how verified
      code sits in the workspace, and add a CI job that runs the
      verification. Constraint: the shipped binaries must not gain a
      dependency without Daniel's agreement (see "Memory safety"). Verus's
      crates (`vstd`, its macros) would be new dependencies of the build;
      find out which of them would end up in the binaries, whether they
      contain `unsafe` code, and what the alternatives are (for instance,
      code that compiles without Verus's crates when not verifying, or a
      verified copy kept equal to the shipped code by a check). Write the
      options down; for the spike, use one that leaves the shipped binaries
      and `Cargo.lock` as they are, or stop and ask.
    - **No change in behaviour.** Every gate keeps agreeing with Ethos; if
      verification needs the code restructured, the gates show it is the
      same.
    - **The report** (`docs/verus-spike.md`): what was verified and what was
      assumed; which Rust features of pathos's code Verus accepted, which
      it did not, and what had to be rewritten; lines of specification and
      proof against lines of code; verification time; the CI job; the
      dependency options; and an estimate, from this experience, of what
      the evaluator, matching and step checking would take.
    The gate: the two parts verify in CI, `scripts/full-check --quick`
    passes, and the report is written. The reviewer pushes and starts CI
    runs, as before.

## The `verus` branch

Milestones 18 and later live on the branch `verus`, not on `main`: an
exploration of how far pathos can be verified with Verus, which Daniel
will decide on later. The rules of the branch:

- Each milestone is a branch off `verus` (`m18-verus-matching`, ...),
  reviewed and merged into `verus` as milestones were into `main`.
- `main` is merged into `verus` regularly, never the other way round, so
  that the verified code stays the code that ships.
- Behaviour does not change: every gate keeps agreeing with Ethos. The
  specifications state what pathos does now, Ethos's quirks included.
- No dependency is added to the shipped binaries, and `Cargo.lock` does not
  change, without Daniel's agreement (the spike's option C).
- Each milestone adds a section to `docs/verus-spike.md` (or a file it
  links): what was verified, what is assumed, the cost, and an updated
  estimate for what is left.

18. **Panic freedom of matching.** `match_terms` (in `typing.rs`) and the
    code that calls it to match a program's cases and a rule's premises,
    `:args` and conclusion: prove that it cannot panic, and that every
    handle it reads and every term it builds is valid in the store, using
    the store invariant of milestone 17. Not yet its correctness (that the
    substitution applied to the pattern gives the term), but state the
    lemmas from the store that correctness will need, and say what the
    statement would be. Also: add `verus` to the push triggers of
    `.github/workflows/ci.yml` on this branch, so that every push to it runs
    the whole CI, and the `verify` job covers the new proofs.
    The gate: `scripts/verify` and `scripts/full-check --quick` pass, CI is
    green on the `m18-verus-matching` branch, and the report section is
    written. The reviewer pushes and starts CI runs.
19. **Matching is correct.** Prove the statement milestone 18 wrote down:
    when `match_terms` succeeds, the context it returns, applied to the
    pattern as a substitution (on the store's tree view), gives the term;
    and when `match_cases` returns `Body`, that holds for every argument of
    the chosen case. Add to the store what this needs, starting with what
    milestone 18 found missing: that `is_ground` holds exactly for terms
    whose tree has no parameter. Where Ethos's matching has a quirk that
    the statement must allow (the types of a parameter and of its binding
    are not compared; a ground pattern matches only itself), state it as
    such in the specification rather than leaving it out. Also prove, or
    list as assumed with the reason, that `match_terms` terminates.
    The gate: as for milestone 18, on the branch `m19-verus-matching-correct`.
20. **The snapshot reader cannot panic, whatever the file.** Today a forged
    snapshot (one whose checksum fits) can make pathos panic: the 23
    "Crafted snapshot" rows of `docs/panics.md`. That is why the evidence
    page asks the Ethos developers whether snapshots are trusted like
    signatures. If the reader cannot panic on any input and every state it
    accepts satisfies the invariants the rest of the code relies on, the
    answer no longer matters.
    - **`pathos-term`:** the codec's `Reader`, `Lit::read_from` and the
      store's `read_from`. Prove that they cannot panic on any byte
      sequence, and that a store they return satisfies the invariant of
      milestones 17 and 19 (valid handles, injective tree view, the flags).
      Where that needs the reader to check more than it does now, add the
      check, as a rejection of the snapshot (it is then ignored, as a
      damaged one is today).
    - **The shapes the checker relies on.** What milestones 18 and 19
      assume (`is_program`: every case of a program has two children), and
      what the "Crafted snapshot" rows say the rest of the code assumes, are
      either checked by the reader or proved to hold for every term the
      store can contain. List each.
    - **`pathos-check` and `pathos-elab`** (`read_term`, the checker's and
      the state's `read_image`): as far as Verus reaches without bringing
      the `Checker` itself in; what it does not reach, check in the reader
      with ordinary code and a test, and say so in `docs/panics.md`.
    - **Behaviour:** a snapshot that pathos itself wrote is read exactly as
      before; the `snapshot` gate agrees. A snapshot rejected by a new check
      is ignored with the same (silent) fallback as a damaged one.
    - **Fuzzing:** extend the forged-snapshot test with mutations that keep
      the checksum valid (the reviewer's `snapfuzz.py` in the session
      scratchpad does this; ask for it) and run it long enough to say so.
    The gate: `scripts/verify`, `scripts/full-check --quick` (including the
    `snapshot` gate) pass, CI is green on `m20-verus-snapshot`, the
    "Crafted snapshot" rows of `docs/panics.md` are updated (each removed,
    or with what still holds it), and the report section says whether the
    evidence page's first question for the developers can be withdrawn.
21. **Panic freedom of the evaluator.** `eval.rs` (about 970 lines): `evaluate`
    with its explicit stack of frames, program application, the literal
    operators' entry point (`Lit::evaluate` is already verified), `eo::nil`,
    the n-ary helpers and the list operators. Prove that none of it can
    panic, and that every term it reads, builds or returns is a term of the
    store, building on milestones 17 to 20. Not its correctness.
    - **First, the split.** The evaluator is methods of `Checker`, and calls
      out to the plugin's evaluation hooks, warnings (formatted messages),
      statistics, the program table and typing. As matching did in
      milestone 18, separate what Verus must see (the traversal, the
      frames, the operators) from those side effects, for instance behind
      a small interface whose methods are trusted (`external_body`) with
      stated contracts: what they may return, what they may change.
      Write the design down before proving; if it needs more than moving
      code, say so and stop for review.
    - **The stack.** The proof that frames are well formed (each child
      index in range, each pending term valid, the caches holding store
      terms) is the core of the milestone; state it as one invariant.
    - **Assumptions** stay listed: the plugin's contracts, the hash maps'
      models, termination (not expected: programs need not terminate; say
      what fuel or measure a later proof would use).
    - **Behaviour** unchanged: every gate agrees with Ethos, the order of
      warnings and statistics included.
    - **The estimate** for the rest (typing and step checking, then
      correctness with a semantics) is updated from what this milestone
      cost.
    The gate: `scripts/verify` and `scripts/full-check --quick` pass, CI is
    green on `m21-verus-eval`, and the report section is written. The
    reviewer pushes and starts CI runs.

22. **Panic freedom of `evaluate`** (agreed after milestone 21's design
    review, done): the frame stack and its invariant, the two
    `unreachable!` sites included, on `m22-verus-eval-stack`. Report in
    `docs/verus-spike.md`, "Milestone 22".

23. **Panic freedom of typing.** `typing.rs` (about 460 lines):
    `get_type`, `get_type_internal` with its stack, `get_type_app_internal`,
    `check_arity`, `get_literal_op_type` and the literal type rules. Prove
    that none of it can panic and that every type it returns is a term of
    the store, building on milestones 17 to 22. Not its correctness.
    - **The cycle.** Typing evaluates (`evaluate` is now verified), and the
      evaluator types (`type_of`, trusted since milestone 21). This
      milestone replaces that trusted contract with a proof. Say how the
      two are proved together, for instance one contract that both meet
      and both rely on, and what remains assumed. The circularity paragraph
      of the report is then rewritten, or removed if nothing is left of it.
    - **The callers' preconditions.** Milestone 21 left two preconditions
      to unverified callers in `build.rs` and `step.rs`: an argument list
      has a head, and an `eo::ite` has three arguments. State which of them
      typing discharges. The rest stays for milestone 24 (term building and
      step checking: `build.rs`, `step.rs`), with an estimate.
    - **Design first,** as in milestone 21. If typing's traversal needs
      more than moving code to be visible to Verus, write the design down
      and stop for review before proving.
    - **Assumptions** stay listed; termination as for `evaluate`.
    - **Behaviour** unchanged: every gate agrees with Ethos, the order and
      text of type-error messages included.
    The gate: `scripts/verify` and `scripts/full-check --quick` pass, CI is
    green on `m23-verus-typing`, and the report section is written. The
    reviewer pushes and starts CI runs.

At every gate, also run `cargo test` and `cargo clippy --all-targets` and
report their results.

## Out of scope until the gates pass

- Changes to what Ethos accepts or rejects, including fixes to Ethos bugs.
  Note them in `docs/ethos-differences.md` instead.
- Speed-ups that could change behaviour, such as compiling program cases
  into decision trees or caching evaluations across calls.
- Plugins and the eoc compiler, except as milestones 10 to 13 describe.
