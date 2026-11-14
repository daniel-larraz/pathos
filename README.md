# pathos

A reimplementation of the [Ethos](https://github.com/cvc5/ethos) proof checker
in Rust. Work in progress: milestone 1 of [docs/brief.md](docs/brief.md) is
done and awaits review.

pathos aims to behave exactly like Ethos (same verdicts and error messages on
the same inputs) while being memory safe: no `unsafe` code in pathos, no C or
C++ dependencies, and every dependency's `unsafe` code accounted for. A
differential testing harness compares the two; see
[docs/brief.md](docs/brief.md) for the goals, the design and the milestones.

## Building

```sh
cargo build --release
```

## Comparing with Ethos

Needs a checkout of the harness and a built reference (pinned in
[difftest.env](difftest.env)):

```sh
git clone -b difftest-harness https://github.com/daniel-larraz/ethos
cd ethos/tools/difftest
./difftest.py build-ref <REFERENCE_REV from difftest.env>
# and, for the proof gates, a cvc5 proof corpus: see the harness README
```

Then, from this repository:

```sh
echo "ETHOS_HARNESS=/path/to/ethos" > .difftest.local
scripts/difftest gate1      # or: tests, gate3, proofs, all, perf
```

## Checks

CI runs formatting, Clippy, the tests in debug and release builds, and the
comparison with Ethos on its 230 regressions, on every push to `main` and every
pull request. The comparisons on cvc5 proofs need a cvc5 build and up to 24 GB
of memory, so they run locally:

```sh
scripts/full-check            # everything, about 25 minutes
scripts/full-check --quick    # without the option and performance gates
```

## License

Modified BSD license, as Ethos; see [LICENSE](LICENSE).
