# generated/cpc-checker

Generated code. Do not edit it: change what it is generated from and run
`scripts/generate-cpc`, which wrote every file here, this one included.

It is the crate `pathos-compiled-checker`: the checker for CPC that the
`rust-meta` stage of `ethos-eoc` (cvc5/ethos#274) compiles from
logos's signature. `crates/pathos` builds its input and calls it.

| Generated from | |
| --- | --- |
| Ethos (`ethos-eoc`, `tools/eoc/driver.py rust`, the runtime in `plugins/rust_meta/runtime`) | `0fa2569b4fbae0cb85cc547abb9db63299938435` |
| logos (`install/defs/Cpc.cached.eo`, with `Cpc.eos` as `--semantics` and `smt.eos` as `--smt-semantics`) | `bdcbd95f615627b26b6ebabc0f584e5230b0bf1f` |

`Cpc.cached.eo` is a copy of that signature: `crates/pathos` builds it in
and reads proofs against it, so that the names it gives the checker are the
names the checker was compiled with.

It is a workspace of its own (see its `Cargo.toml`), outside pathos's
workspace, so pathos's lints, formatting and tests do not apply to it.
