# pathos

A reimplementation of the [Ethos](https://github.com/cvc5/ethos) proof checker
in Rust. Work in progress: it does not check proofs yet.

pathos aims to behave exactly like Ethos (same verdicts and error messages on
the same inputs) while being memory safe. A differential testing harness
compares the two; see [docs/brief.md](docs/brief.md) for the goal, the design
and the milestones.

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

## License

Modified BSD license, as Ethos; see [LICENSE](LICENSE).
