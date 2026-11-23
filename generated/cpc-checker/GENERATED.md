# generated/cpc-checker

Generated code. Do not edit it: change what it is generated from and run
`scripts/generate-cpc`, which wrote every file here, this one included.

It is the crate `pathos-compiled-checker`: the checker for CPC that the
`rust-meta` stage of `ethos-eoc` (cvc5/ethos#274) compiles from
logos's signature. `crates/pathos` builds its input and calls it.

| Generated from | |
| --- | --- |
| Ethos (`ethos-eoc`, `tools/eoc/driver.py rust`, the runtime in `plugins/rust_meta/runtime`) | `bde41a79a3fb99d41012efa1f0d2c6c7635448a3` |
| logos (`install/defs/Cpc.cached.eo`, with `Cpc.eos` as `--semantics` and `smt.eos` as `--smt-semantics`) | `a32321318164f241d266abc1c8c91b46619b2315` |

`Cpc.cached.eo` is a copy of that signature: `crates/pathos` builds it in
and reads proofs against it, so that the names it gives the checker are the
names the checker was compiled with.

It is a workspace of its own (see its `Cargo.toml`), outside pathos's
workspace, so pathos's lints, formatting and tests do not apply to it.
