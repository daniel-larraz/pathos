# generated/cpc-checker

Generated code. Do not edit it: change what it is generated from and run
`scripts/generate-cpc`, which wrote every file here, this one included.

It is the crate `pathos-compiled-checker`: the checker for CPC that the
`rust-meta` stage of `ethos-eoc` (cvc5/ethos#274) compiles from
logos's signature. `crates/pathos` builds its input and calls it.

| Generated from | |
| --- | --- |
| Ethos (`ethos-eoc`, `tools/eoc/driver.py rust`, the runtime in `plugins/rust_meta/runtime`) | `842dd163d735489fb137615656a5d3a76b1317ab` |
| logos (`install/defs/Cpc.cached.eo`, with `Cpc.eos` as `--semantics` and `smt.eos` as `--smt-semantics`) | `241160d8f66201f08b79a62a557778c9d111a4b6` |

`Cpc.cached.eo` is a copy of that signature: `crates/pathos` builds it in
and reads proofs against it, so that the names it gives the checker are the
names the checker was compiled with.

It is a workspace of its own (see its `Cargo.toml`), outside pathos's
workspace, so pathos's lints, formatting and tests do not apply to it.
