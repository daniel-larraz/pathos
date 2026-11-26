# generated/cpcmini-checker

Generated code. Do not edit it: change what it is generated from and run
`scripts/generate-mini`, which wrote every file here, this one included.

It is the checker for CpcMini, the calculus of a few rules that logos
develops its proofs on, compiled by the `rust-meta` stage of
`ethos-eoc` as `generated/cpc-checker` is for CPC. Nothing in pathos
links it: it is what the proofs of `proofs/` are about, through the Lean
that Charon and Aeneas write for it.

| Generated from | |
| --- | --- |
| Ethos (`ethos-eoc`, `tools/eoc/driver.py`, the runtime in `plugins/rust_meta/runtime`) | `842dd163d735489fb137615656a5d3a76b1317ab` |
| logos (`install/defs/Cpc.cached.eo`, with `Cpc.eos` as `--semantics` and `smt.eos` as `--smt-semantics`) | `a6b896b544242f5addc81505addb0d2d78504ee8` |
| Rules (those of logos's `install/install-sig.sh --mini`) | `symm contra refl scope trans` |

`CpcMini.eo` is the signature reduced to those rules, as the first stage
of `driver.py lean ... Cpc.cached.eo symm contra refl scope trans` writes it; the crate is
`driver.py rust` on that file. When it was generated, the Lean that the
same command writes was compared with logos's `CpcMini/` at that
revision and found the same, so the crate and logos's CpcMini are compiled
from one signature by one compiler.

It is a workspace of its own (see its `Cargo.toml`), outside pathos's
workspace, so pathos's lints, formatting and tests do not apply to it.
