# pathos: the evidence for replacing Ethos

For the Ethos developers. pathos is a reimplementation of the Ethos proof
checker in Rust: the `ethos` binary as `pathos`, and `ethos-eoc` with its
seven compiler stages as `pathos-eoc`. It is meant to replace the C++ if two
things hold: it is memory safe, and it does what Ethos does. This page says
what backs each claim and how to check it. The reference throughout is
Ethos `9217112f` (cvc5/ethos `main` with PR #223), built in release mode.

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
  (17 lines of vector arithmetic in four crates) lies behind `malachite`'s
  FFT multiplication, which runs only for numbers of about 25,000 bits or
  more: an input can reach it, and no case of any gate below does.
  What could go wrong there is a wrong product, not a memory error, and
  the `bignum` cases below check the products. The versions are pinned.
  [dependencies.md](dependencies.md) has the trace, how to rerun it
  (`scripts/unsafe-reach`), why each reachable `unsafe` line is sound, and
  the build options that were considered.
- **Bad input gives an error, never undefined behaviour.** Where Ethos reads
  past the end of a vector or crashes (the first group of differences
  below), pathos reports an error. Indexing is bounds-checked: the worst a
  mistake in pathos can do is stop the program with a message (a "panic").
  [panics.md](panics.md) goes through all 364 places that could panic and
  says why input does not reach each; the ones a signature or proof did
  reach were found by that review and fixed.
- **Iteration instead of recursion.** Parsing, typing a term, evaluating
  programs, matching and printing use explicit stacks, so a term a million
  levels deep, or a program a million calls deep, does not overflow the
  stack. Three recursions that Ethos also has remain, over chains of
  declarations and nested includes; there pathos gets deeper than Ethos
  before it stops (9,700 nested includes against 236, for one).
- **Terms are never freed.** A term is a 32-bit index into a table that
  only grows, so there is no reference counting and no freed term to use
  by mistake, the class of bug PRs #223 and #256 fixed in Ethos. On the
  largest proof (453 MB) pathos peaks at 3.8 GB where Ethos peaks at
  24.9 GB.

## Same behaviour as Ethos

Every gate runs both binaries on the same inputs and compares what they do:
the outcome (correct, incomplete, error), the error text with its position
(without Ethos's `Fatal failure within` line), and standard output. The
harness is `tools/difftest` in `daniel-larraz/ethos` at `6a4fa74`; its
README says exactly what is compared. `scripts/difftest <gate>` builds
pathos and runs it; `scripts/full-check` runs all of them. The counts are
from runs on 2026-11-14 on the source of commit `0bac6d7`. All cases agree in every gate.

| Gate | What both binaries are run on | Cases | Result | Rerun |
| --- | --- | --- | --- | --- |
| `tests` | Ethos's regressions (`tests/*.eo`, `*.smt2`) | 230 (188 correct, 42 errors) | all agree | `scripts/difftest tests` |
| `proofs` | cvc5 proofs from 29 areas of cvc5's regressions (cvc5 `2107a003`), each with the full CPC signature | 400 (394 correct, 6 incomplete) | all agree | `scripts/difftest proofs` |
| `large` | The cvc5 proofs of 1 MB or more from `regress1` to `regress4`, up to 453 MB | 43 (37 correct, 4 incomplete, 2 errors) | all agree | `scripts/difftest large` |
| `options` | Regressions and proofs under each of Ethos's eight non-default options, all of them together, and none | 6,300 | all agree | `scripts/difftest options` |
| `cli` | 38 command-line cases (`--help`, `-t`, `-v`, unknown options, standard input, `--include=`, `--reference=`), and regressions and proofs under `--stats`, `--stats-all`, `--stats-compact` | 3,188 | all agree (times and term-store counters masked) | `scripts/difftest cli` |
| `bignum` | Generated files of `eo::add`, `mul`, `pow`, division, conversions and the bit-vector operations on operands from 64 bits to a million bits, with each expected value computed independently | BIGNUM | BIGNUM | BIGNUM |
| `fuzz` | The 41 groups of inputs on which a fuzzing run of mutated regressions and proofs found the two to differ | 41 | 36 fixed, 4 accepted differences, 1 Ethos crash; none still differs | `scripts/difftest fuzz` |
| `snapshot` | Regressions and proofs under every option set, pathos starting from a snapshot of CPC; and the proofs with a truncated, a corrupted and an empty snapshot | 6,300 + 3 × 400 | all agree | `scripts/difftest snapshot` |
| `eoc` | eoc's driver with `ethos-eoc` and with `pathos-eoc`: every stage on every rule of the test signatures and of logos's CPC (logos `a3232131`), and logos's `lean --all`; every file written is compared | 3,507 (3,322 ok, 185 errors) | all agree | `scripts/difftest eoc` |
| logos's acceptance check | `install/install-cpc.sh --all --cached --check` in logos, with `pathos-eoc` in place of `ethos-eoc` | Cpc, CpcMini | "Up to date with the cached signature", exit 0 | commands in [reviews/m13-eoc-lean.md](reviews/m13-eoc-lean.md) |
| `perf` | Regressions, proofs and large proofs, one job at a time, Ethos rerun | 673 | all agree; see below | `scripts/difftest perf` |

Also green: 91 unit and end-to-end tests (`cargo test`, debug and release),
and CI on every push, which runs the gates that need neither the cvc5
corpus nor much time (`tests`, `fuzz`, the `--stats` part of `cli`, and
1,055 of the `eoc` cases).

**Performance** (`perf`, 2026-11-14). Over the 629 cases both accept,
Ethos takes 1,271 s and pathos 533 s (42%): the 41 large proofs 1,237 s and
513 s, the 400 proofs 33.3 s and 19.1 s, the regressions 0.63 s and 0.47 s.
Of the 441 cases that take Ethos over 50 ms, none is slower in pathos; the
least favourable takes 73% of Ethos's time. pathos uses less memory than
Ethos on every case; the peaks are 3.8 GB and 24.9 GB. A snapshot of CPC
(pathos only) brings the 400 proofs from 19.1 s to 11.1 s. A fuzzing
campaign was running at low priority on the same machine, and both
checkers took about twice the time they take on an idle one (Ethos 658 s,
pathos 269 s in an earlier run); a second run under the same load gave the
same 42%.

**A fuzzing campaign** of mutated inputs runs alongside this review; its
result will be added here.

## Where pathos differs from Ethos

The full list, with the Ethos source location of each item, is
[ethos-differences.md](ethos-differences.md). It also lists 15 behaviours
of Ethos that look like bugs and that pathos reproduces on purpose (for
example, the character after a one-letter keyword is lost).

**1. Ethos crashes or reads out of bounds; pathos reports an error.** None
is in the corpus; the fuzzing runs found most of them.

- An `eo::` operator evaluated without an argument it reads, e.g.
  `(eo::is_eq a)` in a program body: Ethos reads past the end of the
  argument vector (a crash, or a wrong term taken for the argument);
  pathos stops with `Too few arguments when evaluating literal op ...`.
- `(eo::var t)` with one argument, `(eo::nameof (eo::var))`, the nil
  terminator of an operator whose type is not a function type, `step-pop`
  with no assumption: Ethos reads past the end; pathos gives a type error,
  an error, or a failed step.
- A literal such as `-/5`, `(_ bv<n> 0)` in a reference file, a quoted
  symbol cut to `|` by a NUL character: uncaught C++ exception in Ethos, an
  error in pathos.
- `ethos-eoc`: a stage that indexes a term's children on the strength of a
  debug-only assertion reads outside the term; `pathos-eoc` stops with
  `<Stage>: unexpected term: ...`. `(echo "smt-meta <unbound name>")` is a
  segmentation fault in Ethos.
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
  gigabytes; Ethos has no such limit).
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
   signature file can. It can also hold a term of a shape no signature
   produces, on which the checker stops with a panic instead of an error
   (memory safe; 23 places, in [panics.md](panics.md); see also
   [reviews/m10-snapshots.md](reviews/m10-snapshots.md)). If snapshots
   should be treated as untrusted input, the reader has to validate the
   shape of every term and of the checker's tables. If they are trusted
   like signatures, nothing needs to change. Which is it?
2. **Should the evaluation hooks stay?** Ethos's plugin interface lets a
   plugin take over the evaluation of programs and operators. pathos has
   the same hooks (`EvalPlugin`), but none of the seven eoc stages uses
   them, so no gate exercises them. Keep them for plugins to come, or
   remove them?
