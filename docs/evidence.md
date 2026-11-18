# pathos: the evidence for replacing Ethos

For the Ethos developers. pathos is a reimplementation of the Ethos proof
checker in Rust: the `ethos` binary as `pathos-eo`, and `ethos-eoc` with its
seven compiler stages as `pathos-eoc`. It is meant to replace the C++ if two
things hold: it is memory safe, and it does what Ethos does. This page says
what backs each claim and how to check it. The reference is Ethos
`e51f527c` (cvc5/ethos `main` with PRs #270, #272, #274 and #275,
milestones 26 and 29, and #276 and #277, which change only the `rust-meta`
runtime, so that what pathos is compared with is that of `b8d65127`), built in
release mode. The figures on this page were
measured against `9217112f`, four commits earlier, unless a section says
otherwise; those commits fix the bugs pathos used to reproduce, change
`lean-meta`'s output, add the `rust-meta` stage, and change three corners
of the evaluator (`eo::extract` and `eo::gt` on bit-vectors, list operators
on arguments that did not evaluate) and what the desugaring stage accepts,
not anything the figures measure.

## Memory safety

- **No `unsafe` code in pathos.** In Rust, code that can break memory
  safety (raw pointers, unchecked indexing, calls into C) has to be marked
  `unsafe`; everything else is checked by the compiler or at run time.
  pathos's six crates contain none, and the workspace sets the compiler
  lint `unsafe_code = "forbid"` (`Cargo.toml`), which turns any `unsafe`
  block into a compile error and cannot be switched off from inside a
  crate. `cargo clippy` with warnings as errors runs in CI.
- **No C or C++.** No GMP: numbers use `malachite`, a Rust library. Nothing
  is linked but the Rust standard library and the C library under it.
- **Dependencies.** The twelve crates pathos depends on are all `malachite`
  and what it needs. Nine contain `unsafe` code. Five of those contribute
  no instruction to the binaries. The `unsafe` code that is in the binaries
  (17 lines of vector arithmetic in four crates on x86-64, 19 on macOS; 10
  or 11 lines of one crate on arm64) lies behind `malachite`'s
  FFT multiplication, which runs only for numbers of about 25,000 bits or
  more: an input can reach it, and of the gates below only `bignum`, which
  is there for it, does.
  What could go wrong there is a wrong product, not a memory error, and
  the `bignum` cases check the products on every platform. The versions are pinned.
  [dependencies.md](dependencies.md) has the trace, how to rerun it
  (`scripts/unsafe-reach`), why each reachable `unsafe` line is sound, and
  the build options that were considered.
- **Bad input gives an error, never undefined behaviour.** Where Ethos reads
  past the end of a vector or crashes (the first group of differences
  below), pathos reports an error. Indexing is bounds-checked: the worst a
  mistake in pathos can do is stop the program with a message (a "panic").
  [panics.md](panics.md) goes through all 366 places that could panic and
  says why input does not reach each; the ones a signature or proof did
  reach were found by that review and fixed. A section of its own does the
  same for the 67 places of `pathos`, the checker for CPC, at a later
  commit (seven were reached and are fixed); the generated checker it calls
  is not covered.
- **Iteration instead of recursion.** Parsing, typing a term, evaluating
  programs, matching and printing use explicit stacks, so a term a million
  levels deep, or a program a million calls deep, does not overflow the
  stack. Three recursions that Ethos also has remain, over chains of
  declarations and nested includes. pathos runs the checker on a thread
  with a 64 MiB stack on every platform, and gets 4 to 50 times deeper
  than Ethos before it stops (on Windows, where Ethos's stack is smallest,
  about 40,000 chained declarations against about 1,000).
- **Terms are never freed.** A term is a 32-bit index into a table that
  only grows, so there is no reference counting and no freed term to use
  by mistake, the class of bug PRs #223 and #256 fixed in Ethos. On the
  largest proof (453 MB) pathos peaks at 3.7 GiB where Ethos peaks at
  24.3 GiB.

## Same behaviour as Ethos

Every gate runs both binaries on the same inputs and compares what they do:
the outcome (correct, incomplete, error), the error text with its position
(without Ethos's `Fatal failure within` line), and standard output. The
harness is `tools/difftest` in `daniel-larraz/ethos` at `500f12f`; its
README says exactly what is compared. `scripts/difftest <gate>` builds
pathos and runs it; `scripts/full-check` runs all of them. The counts are
from runs on 2026-11-14 on Linux x86-64, on the source of commit `69f7ece`.
All cases agree in every gate.
"[Platforms](#platforms)" has the gates that also run on the other five.

| Gate | What both binaries are run on | Cases | Result | Rerun |
| --- | --- | --- | --- | --- |
| `tests` | Ethos's regressions (`tests/*.eo`, `*.smt2`) | 230 (188 correct, 42 errors) | all agree | `scripts/difftest tests` |
| `proofs` | cvc5 proofs from 29 areas of cvc5's regressions (cvc5 `2107a003`), each with the full CPC signature | 400 (394 correct, 6 incomplete) | all agree | `scripts/difftest proofs` |
| `large` | The cvc5 proofs of 1 MB or more from `regress1` to `regress4`, up to 453 MB | 43 (37 correct, 4 incomplete, 2 errors) | all agree | `scripts/difftest large` |
| `options` | Regressions and proofs under each of Ethos's eight non-default options, all of them together, and none | 6,300 | all agree | `scripts/difftest options` |
| `cli` | 42 command-line cases (`--help`, `-t`, `-v`, unknown options, standard input, `--include=`, `--reference=`, the byte `0xFF` and bytes above 127 in a file and on standard input), and regressions and proofs under `--stats`, `--stats-all`, `--stats-compact` | 3,192 | all agree (times and term-store counters masked) | `scripts/difftest cli` |
| `bignum` | Generated files of `eo::add`, `mul`, `pow`, division, conversions and the bit-vector operations on operands from 64 bits to a million bits, with each expected value computed independently (Python's integers and fractions). Each file ends with one wrong expectation on purpose, so both checkers print a value of up to 600,000 digits in full | 7 (each stops at its deliberate last line, in both) | all agree, byte for byte; Ethos agrees with every computed value | `scripts/difftest bignum` |
| `fuzz` | The groups of inputs on which two fuzzing runs of mutated regressions and proofs found the two to differ (41 from a first run, 12 from the 24-hour campaign below) | 53 | 37 fixed, 14 accepted differences, 2 Ethos crashes; none still differs | `scripts/difftest fuzz` |
| `snapshot` | Regressions and proofs under every option set, pathos starting from a snapshot of CPC; and the proofs with a truncated, a corrupted and an empty snapshot | 6,300 + 3 × 400 | all agree | `scripts/difftest snapshot` |
| `eoc` | eoc's driver with `ethos-eoc` and with `pathos-eoc`: every stage on every rule of the test signatures and of logos's CPC (logos `a3232131`), and logos's `lean --all`; every file written is compared | 3,507 (3,322 ok, 185 errors) | all agree | `scripts/difftest eoc` |
| logos's acceptance check | `install/install-cpc.sh --all --cached --check` in logos, with `pathos-eoc` in place of `ethos-eoc` | Cpc, CpcMini | "Up to date with the cached signature", exit 0 | commands in [reviews/m13-eoc-lean.md](reviews/m13-eoc-lean.md) |
| `perf` | Regressions, proofs and large proofs, one job at a time, Ethos rerun | 673 | all agree; see below | `scripts/difftest perf` |

Also green: 98 unit and end-to-end tests (`cargo test`, debug and release),
and CI on every push, which runs the gates that need neither the cvc5
corpus nor much time (`tests`, `fuzz`, the `--stats` part of `cli`, and
1,055 of the `eoc` cases).

**Performance** (`perf`, 2026-11-16, Linux x86-64, commit `e3823e0`, an
otherwise idle machine: Intel Core Ultra 7 255HX, 20 cores, 64 GB). Over
the 629 cases both accept, Ethos takes 628.5 s and pathos 274.8 s (44%):
the 41 large proofs 612.7 s and 265.9 s (43%), the 400 proofs 15.5 s and
8.6 s (55%), the regressions 0.32 s and 0.25 s (78%). Of the 85 cases that
take Ethos over 50 ms, none is slower in pathos; the least favourable
takes 74% of Ethos's time. Sixteen regressions of about 1.3 ms are slower
in pathos by 0.1 to 0.3 ms, its start-up cost. pathos uses less memory
than Ethos on all 673 cases; the peaks, both on `regress3/hole10`, are
3.7 GiB and 24.3 GiB (earlier versions of this page said 3.8 GB and
24.9 GB, which were MiB counts divided by 1,000). A second run the same
day gave 43%, and every run since 2026-11-14 has given 41% to 44%. A
snapshot of CPC (pathos only) brings the 400 proofs from 19.1 s to 11.1 s
(measured at milestone 14). The checker's own thread, new in milestone
15, costs 0.17 ms a run.

**A fuzzing campaign** of mutated inputs (seed 3, 24 hours ending
2026-11-15, each run limited to 10 s and 4 GiB) made 22,236,159 runs:
22,226,677 agree, 1,203 run out of time or memory in both, and 8,279
differ, in 13 groups. Only one group was a difference to fix in pathos:
how a type error is reported after a `:let-binder` whose list constructor
is malformed (fixed in milestone 14). One group ran out of memory in
both, which the harness of the time did not recognise in Ethos. Eight are
the first kind below, where Ethos reads past the end of an operator's
arguments, one is an
Ethos abort on a malformed string literal (on which the binary the
campaign ran, from before milestone 14, panicked; pathos now gives a
parse error), one is Ethos's segmentation fault, and one is a term
Ethos forgets (the third kind below). The campaign ran a binary frozen
when it started, so the groups were replayed on the current one; they
are the 12 newer findings of the `fuzz` gate.

**Ethos under AddressSanitizer.** A build of Ethos (the pinned revision)
with AddressSanitizer, a compiler option that stops a program at its
first out-of-bounds or freed-memory access, ran every case of `tests`,
`proofs`, `options`, `cli` and `bignum` (8,869) and every saved fuzzing
finding. It reported one memory error, a read past the end of a variable
made by `(eo::var t)` with one argument (the second item of the first kind
below, reported on cvc5/ethos#257). Nothing else, so in particular no
use of freed memory under `--stats`.

## Platforms

Ethos's CI builds and tests on Linux, macOS and Windows, each on x86-64 and
arm64. pathos's CI (job `platforms`) uses the same six runners and the same
GMP packages, builds the reference Ethos on each, and runs there:

- `cargo build --release` and `cargo test`, debug and release. On Windows
  with Rust's MSVC toolchain; the release binaries are linked statically
  on Linux and Windows, as Ethos's are, and uploaded on pushes to `main`
  with `LICENSE` and `licenses/` (`scripts/package`): the LGPL v3 text for
  `malachite`, as Ethos ships it for GMP, and the other dependencies'
  licence files;
- the `tests`, `cli` (its command-line cases and the regressions under the
  `--stats` options), `bignum` and `fuzz` gates, and on Windows `tests`
  once more on a checkout with CR LF line ends, which is what Ethos's own
  CI tests there;
- `scripts/platform-probe`: both binaries on line endings, Ctrl-Z, bytes
  above 127, how files are named, found and printed, and the depth of the
  three recursions;
- `scripts/unsafe-reach`, for the per-platform tables of
  [dependencies.md](dependencies.md).

Results of CI run 43637950215 (commit `69f7ece`, 2026-11-14); every step
of every job passed:

| Platform (runner) | `tests` | `cli` | `bignum` | `fuzz` | Probe |
| --- | --- | --- | --- | --- | --- |
| Linux x86-64 (`ubuntu-22.04`) | 230 agree | 1,192 agree | 7 agree | none still differs | no differences |
| Linux arm64 (`ubuntu-22.04-arm`) | 230 agree | 1,192 agree | 7 agree | none still differs | no differences |
| macOS x86-64 (`macos-15-intel`) | 230 agree | 1,192 agree | 7 agree | none still differs | no differences |
| macOS arm64 (`macos-15`) | 230 agree | 1,192 agree | 7 agree | none still differs | no differences |
| Windows x86-64 (`windows-latest`, Ethos built with MSYS2 MINGW64) | 230 agree; 230 on the CR LF checkout | 1,192 agree, 4 of them accepted Ethos crashes | 7 agree | none still differs | no differences; 5 Ethos crashes |
| Windows arm64 (`windows-11-arm`, MSYS2 CLANGARM64) | 230 agree; 230 on the CR LF checkout | 1,192 agree, 3 of them accepted Ethos crashes | 7 agree | none still differs | no differences; 5 Ethos crashes |

`fuzz` replays 51 of the 53 saved findings there; two need the cvc5
corpus. The Ethos crashes are all the missing file described below.

The cvc5 proof gates, `options`, `perf` and `eoc` run on Linux x86-64
only. Ethos does not behave the same on the six: on Windows it reads and
writes text with CR LF and Ctrl-Z handling, resolves file names through
the file system and prints them in full, and takes the null device for a
terminal; on Linux arm64 the byte `0xFF` is an ordinary character. pathos
does on each platform what Ethos does there
([ethos-differences.md](ethos-differences.md), "By platform"). What it
cannot match is a crash: on Windows Ethos ends on an uncaught C++
exception when a file does not exist, and pathos reports `Couldn't open
file`; the harness accepts those four cases by name.

## Keeping up with Ethos

Everything above is about one Ethos revision, `REFERENCE_REV` in
`difftest.env` (`e51f527c`). Ethos keeps changing. A workflow of its own,
`.github/workflows/drift.yml` ("Drift from Ethos main"), runs every night
and on demand, apart from CI and blocking nothing. On Linux x86-64 it
builds Ethos and `ethos-eoc` at the current `main` of cvc5/ethos and
compares pathos's `main` with them, using the pinned harness
(`scripts/drift`, which also runs locally):

| Comparison | On |
| --- | --- |
| `tests` | Ethos `main`'s own `tests/`, so new regressions are included the night they land |
| `cli` | the harness's command-line cases, and those regressions under the `--stats` options |
| `bignum` | the large-number cases |
| `fuzz` | the saved fuzzing findings |
| `eoc` | `ethos-eoc` against `pathos-eoc` on the test signatures and on the CPC of logos's `main` (`lean --all` and the two desugar runs) |

The cvc5 proofs are not part of it: they need a cvc5 build and the corpus.

The job's summary names the Ethos commit, says whether it is still
`REFERENCE_REV`, and gives the counts and the cases that differ; the JSON
reports are kept as an artifact. The job is green when everything agrees
and red otherwise, so **a red night means: Ethos has changed in a way
pathos does not follow yet**. It says nothing against pathos at
`REFERENCE_REV`, which CI keeps checking.

Two runs show both outcomes (2026-11-14, pathos `m16`, logos `b3f0b24b`):

| Ethos | Result |
| --- | --- |
| `main`, which is `9217112f`, the pinned revision | green: `tests` 230, `cli` 1,192, `bignum` 7 and `eoc` 1,055 agree, `fuzz` has none still differing. Ethos has not moved since the pin, so this run repeats CI's comparison; it does show that logos's `main` (`b3f0b24b`, newer than the pinned `a3232131`) still compiles the same. CI run 43649112013 (started by the push that merged milestone 16 into `main`), and the same locally. |
| `6cfb7ba7`, three commits before the pin (on demand, input `ethos_rev`) | red: the four checker comparisons agree, `eoc` differs on 156 of 1,055 cases, the `lean` runs, whose output Ethos PR #255 changed after that commit. This is what a night looks like after Ethos changes the Lean output. CI run 43649127728 (on demand), and the same locally. |

When it is red:

1. Read the summary: which Ethos commit, which comparison, which cases.
   `scripts/drift --rev <commit>` reproduces it; going back commit by
   commit from Ethos `main` finds the change that did it.
2. Port the change to pathos, in a milestone of its own, as any other
   behaviour of Ethos: read the C++ of the commit, match the binary, add
   tests. If the red is in `build` (Ethos needs something new to build) or
   the harness cannot handle the new Ethos, the harness needs the change
   first; that is the harness's owner's.
3. Move `REFERENCE_REV` (and `HARNESS_COMMIT`, and `LOGOS_REV` if logos
   moved with it) in `difftest.env` to the new revision in that same
   milestone, and rerun `scripts/full-check` and `scripts/difftest eoc`.
   CI and the nightly job are then green again against the same commit.
4. Until then the job stays red every night, on purpose; it can be
   switched off in GitHub's Actions page if the port will take long.

Two limits: GitHub stops scheduled workflows in a repository without
activity for 60 days (starting one by hand turns them on again), and the
job compares `main` with `main`, so a change on an Ethos branch shows
only once it is merged.

## Where pathos differs from Ethos

The full list, with the Ethos source location of each item, is
[ethos-differences.md](ethos-differences.md). It also lists 16 behaviours
of Ethos that look like bugs and that pathos reproduces on purpose (for
example, the character after a one-letter keyword is lost). Those that
contradict the user manual or change what is accepted or printed, and the
crashes below, were reported to Ethos with reproducers on 2026-11-14 and
2026-11-15: cvc5/ethos#257 to #269 and #271.

**1. Ethos crashes or reads out of bounds; pathos reports an error.** None
is in the corpus; the fuzzing runs found most of them.

- The nil terminator of an operator whose type is not a function type,
  `step-pop` with no assumption: Ethos reads past the end; pathos finds no
  terminator, or fails the step. (The other inputs of this kind that this
  list had for Ethos `9217112f`, such as an `eo::` operator without an
  argument it reads, `(eo::var t)`, `-/5` and a NUL character in a quoted
  symbol, are errors in Ethos since `c7d3db90`, and pathos gives the same
  errors since milestone 26.)
- `ethos-eoc`: a stage that indexes a term's children on the strength of a
  debug-only assertion reads outside the term; `pathos-eoc` stops with
  `<Stage>: unexpected term: ...`.
- Recursion deeper than the stack: a segmentation fault in Ethos, a
  controlled abort in pathos, on fewer inputs.

**2. Output that differs by design.**

- pathos does not print the `Fatal failure within <function> at <file>`
  line and exits with status 1 on an error instead of aborting.
- Under `--stats`, the times and the term-store counters (`mkExprCount`,
  `newExprCount`, `deleteExprCount`, `symCount`, `litCount`) are pathos's
  own; rule and program counts are Ethos's.
- `--show-config` prints pathos's name and version.
- `--write-snapshot=FILE` and `--snapshot=FILE` exist only in pathos.
- `pathos-eoc` reports a stage's fatal error when the command being read
  ends, with exit status 1; its fallback directories come from its own
  build, not from CMake.

**3. Anything else.**

- A size limit: pathos's terms are 32-bit handles, so a run that needs more
  than 2^32 - 1 terms ends with `Term store limit exceeded` (tens of
  gigabytes; Ethos has no such limit). The store also refuses a term with
  a number of children its kind cannot have; nothing in pathos builds one.
- Ethos can forget a term that is still in use when it frees another, and
  then builds a second copy that it does not consider equal to the first:
  `eo::eq` is `false` on two equal terms, and a step can be rejected with
  the same formula as "Proves" and "Expected". It needs a signature with a
  single applied symbol, or an overloaded one, so no gate but `fuzz` shows
  it; pathos keeps one term for equal terms (cvc5/ethos#271).
- Not observed, but possible: `eo::hash` and `eo::cmp` number terms as they
  are first seen, and Ethos forgets a number when it frees the term, which
  pathos never does; and Ethos orders some maps by the address of a term,
  pathos by creation, which shows in the order of a `Context [...]` line
  and of some warnings. No case in any gate depends on either.
- `--stats` on the two largest proofs overflows a fixed-width column in
  both, at different places because the times differ.

## Questions for the Ethos developers

1. **Is a snapshot trusted like the signature it was made from?** A
   snapshot (`--write-snapshot`) stores the checker's state after loading a
   signature, so that proofs need not load CPC again. pathos uses one only
   if the signature files are unchanged and the file's checksum fits; a
   damaged file is ignored. The checksum is not a signature: a file forged
   on purpose can hold a rule that proves anything, exactly as an edited
   signature file can. (It cannot make the checker panic: the reader
   rejects a state that no signature gives where the checker would rely on
   it; [panics.md](panics.md), "Open".) Should a snapshot be trusted like
   the signature it was made from, or does it need more than a checksum,
   such as a signature of its own?
2. **Should the evaluation hooks stay?** Ethos's plugin interface lets a
   plugin take over the evaluation of programs and operators. pathos has
   the same hooks (`EvalPlugin`), but none of the seven eoc stages uses
   them, so no gate exercises them. Keep them for plugins to come, or
   remove them?
