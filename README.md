# pathos

A memory-safe reimplementation of the [Ethos](https://github.com/cvc5/ethos)
proof checker in Rust, meant as a drop-in replacement:

- **`pathos`** replaces the `ethos` checker. It takes the same inputs and
  options, and gives the same verdicts and the same error messages, with
  the same positions.
- **`pathos-eoc`** replaces `ethos-eoc`, the Eunoia compiler behind
  [logos](https://github.com/cvc5/logos), with all of its stages
  (`trim-defs`, `desugar`, `model-smt`, `smt-meta`, `lean-meta`). Every
  file it writes is byte for byte what `ethos-eoc` writes.

pathos contains no `unsafe` code (the compiler enforces it) and no C or
C++; its dependencies' `unsafe` code is traced and justified line by line.
It is checked against Ethos `9217112f`, the current `main`, by
differential testing on all six platforms Ethos's CI covers: Linux, macOS
and Windows, each on x86-64 and arm64. On the cvc5 proofs it takes about
40% of Ethos's time and much less memory (3.8 GB against 24.9 GB on the
largest, a 453 MB proof).

**[docs/evidence.md](docs/evidence.md)** is the one page to read: what was
compared, how to rerun each comparison, the differences from Ethos, and
the open questions for the Ethos developers.

## Using it

```sh
cargo build --release --locked
target/release/pathos proof.cpc                  # as `ethos proof.cpc`
target/release/pathos --include=cpc.eo proof.cpc
```

Every option of `ethos` works the same way (`pathos --help`). Two are
pathos's own, and `--help` does not list them, since its output is kept
identical to Ethos's:

- `--write-snapshot=FILE SIG.eo` loads a signature and saves the checker's
  state to `FILE`.
- `--snapshot=FILE` starts from that state instead of loading the
  signature again, which roughly halves the time on cvc5's proofs.
  A snapshot whose signature files have changed, or which is damaged,
  is ignored, and the signature is loaded as usual.

These replace Ethos's `cpp_compiler` plugin, which compiles a signature
into C++ for the same purpose.

`pathos-eoc` is used the way `ethos-eoc` is, through eoc's driver
(`tools/eoc/driver.py` in Ethos) or logos's `install/install-cpc.sh`: put
it where the driver expects `ethos-eoc`. It finds Ethos's plugin templates
through `ETHOS_PLUGIN_ROOT` and `ETHOS_PLUGIN_OUTPUT_DIR`, or the
directories given at build time in `ETHOS_PLUGIN_SOURCE_DIR` and
`ETHOS_PLUGIN_OUTPUT_DIR`, as `ethos-eoc` does with the ones CMake sets.
[docs/reviews/m13-eoc-lean.md](docs/reviews/m13-eoc-lean.md) has the
commands that run logos's own check with it.

Release binaries for the six platforms, statically linked where Ethos's
are, are built by CI on every push to `main` (the `pathos-<platform>`
artifacts of the CI runs). They include the licence notices.

## How it is checked

A harness ([`tools/difftest`](https://github.com/daniel-larraz/ethos/tree/difftest-harness/tools/difftest)
in a fork of Ethos, pinned by commit in [difftest.env](difftest.env)) runs
Ethos and pathos on the same inputs and compares the outcome, every error
message and the output. `scripts/difftest <gate>` runs one comparison:

| Gate | What both checkers run on |
| --- | --- |
| `tests` | Ethos's 230 regressions |
| `cli` | command-line cases, and everything under the `--stats` options |
| `proofs`, `large` | 400 cvc5 proofs, and 43 of 1 MB or more (needs a cvc5 corpus; see the harness README) |
| `options` | the regressions and proofs under every non-default option |
| `bignum` | arithmetic on numbers up to a million bits |
| `fuzz` | the inputs on which fuzzing found the two to differ |
| `snapshot` | the regressions and proofs, pathos starting from a snapshot |
| `eoc` | eoc's driver with `ethos-eoc` and with `pathos-eoc`, every written file compared |
| `perf` | timings, one case at a time |

Set up once:

```sh
git clone -b difftest-harness https://github.com/daniel-larraz/ethos
(cd ethos/tools/difftest && ./difftest.py build-ref <REFERENCE_REV from difftest.env> --eoc)
echo "ETHOS_HARNESS=$PWD/ethos" > .difftest.local
```

then `scripts/difftest tests`, or `scripts/full-check` for everything
(`--quick` leaves out `options` and `perf`).

CI runs, on every push to `main` and every pull request: formatting,
Clippy and the tests in debug and release builds; the `tests`, `cli`,
`bignum` and `fuzz` comparisons on each of the six platforms, with
`scripts/platform-probe` for what depends on the platform (line endings,
file names, stack depth); and the `eoc` comparison, including logos's
whole-signature runs. The cvc5 proof gates need a cvc5 build and up to
24 GB of memory, so they run locally.

Two parts of `pathos-term`, the literal operators and the term store, also
carry specifications that [Verus](https://github.com/verus-lang/verus)
proves: `scripts/verify`, and the `verify` job in CI. This is a feasibility
spike, not a proof that pathos is sound; see
[docs/verus-spike.md](docs/verus-spike.md). pathos does not depend on
Verus's libraries.

## Keeping up with Ethos

pathos is checked against one Ethos revision, `REFERENCE_REV` in
[difftest.env](difftest.env). A separate workflow,
[drift.yml](.github/workflows/drift.yml), compares pathos's `main` with
the current `main` of cvc5/ethos every night (and on demand, with any
revision): Ethos's own regressions at that commit, the command-line
cases, large-number arithmetic, the fuzzing findings, and `ethos-eoc` on
the CPC of logos's `main`. The same runs locally:

```sh
scripts/drift                 # against cvc5/ethos main
scripts/drift --rev <commit>  # against another revision
```

It blocks nothing. A red run means Ethos now does something pathos does
not; [docs/evidence.md](docs/evidence.md#keeping-up-with-ethos) says what
to do then.

## Documents

- [docs/evidence.md](docs/evidence.md): the case for replacing Ethos, on one page.
- [docs/ethos-differences.md](docs/ethos-differences.md): every known difference from Ethos, and the Ethos behaviour pathos reproduces on purpose. What looked like bugs in Ethos was reported as cvc5/ethos#257 to #268.
- [docs/dependencies.md](docs/dependencies.md): every dependency, its `unsafe` code, what of it can run, and why that is sound, per platform.
- [docs/panics.md](docs/panics.md): every place pathos could panic, and why input does not reach it.
- [docs/verus-spike.md](docs/verus-spike.md): what Verus proves about the literal operators and the term store, what it assumes, and what it cost.
- [docs/brief.md](docs/brief.md) and [docs/reviews/](docs/reviews/): how pathos was built.

## How it was built

pathos was written by an AI model (Claude) working milestone by milestone
against [docs/brief.md](docs/brief.md); a second instance reviewed each
milestone and kept the comparison harness, and a milestone was merged only
after its comparisons with Ethos passed. The reviews are in
[docs/reviews/](docs/reviews/).

## License

Modified BSD license, as Ethos; see [LICENSE](LICENSE). pathos links
against `malachite`, which is under the GNU LGPL v3
([licenses/lgpl-3.0.txt](licenses/lgpl-3.0.txt)); as for Ethos with GMP,
pathos and the combined binary stay under the BSD license.
