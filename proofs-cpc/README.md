# proofs-cpc: the proofs about the full CPC's compiled checker

The Lean project of stage 5 of milestone 32: the proofs of `proofs/`, for the
checker compiled from the whole of logos's CPC (`generated/cpc-checker`)
rather than from CpcMini. `docs/proofs.md` has the report; this says what is
here.

| Path | What | Written by |
| --- | --- | --- |
| `CpcChecker/`, `CpcChecker.lean` | The Lean of `generated/cpc-checker`: the runtime and its 13 parts | Charon and Aeneas (`scripts/aeneas-translate`, then `scripts/aeneas-stitch`); `scripts/proofs-build --cpc --translate TOOLS` checks it |
| `CpcCases.lean` | The cases of CPC's programs, one function each | lean-meta, in the run `scripts/generate-cpc` makes |
| `CpcEmbed.lean`, `CpcCtors.lean` and `CpcCtors/`, `CpcCacheSem.lean`, `CpcProofs.lean` and `CpcProofs/` | The embedding of the checker's values, the constructor lemmas, what the cache holds, the proofs about the generated functions (the lemmas and the proofs in parts, for Lean's memory) | `scripts/proofgen`, in the same run |
| `unproved.toml` | The programs whose generated proof does not build, each with why: proofgen writes none of them (`generated/cpc-checker/proofs.tsv` says why) | by hand, from the build's errors |
| `PathosProofs/`, `PathosProofs.lean`, `audit/` (not in the repository) | `proofs/PathosProofs`, the hand-written library, with its imports named for CPC (`MiniChecker` → `CpcChecker`, `CpcMini.*` → `Cpc.*`, `Mini*` → `Cpc*`) | `scripts/proofs-instance`, which `scripts/proofs-build --cpc` runs |
| `excluded.txt` | What the instance leaves out: CpcMini's top-level theorem | by hand |

The pins are `proofs/`'s (`proofs/pins.env`); the packages are `proofs/`'s
too, through a link (`.lake/packages`), so Mathlib, Aeneas's library and
logos are built once. The allowed axioms are `proofs/axioms-allowed.txt`:
`scripts/proofs-axioms --cpc` checks that `CpcChecker` declares the axioms of
its `[MiniChecker]` section, which are the runtime's.

```sh
scripts/generate-cpc            # the generated Lean, with the crate
scripts/proofs-build --cpc      # the instance, the build, the axiom audit
```

**The top-level theorem's scope** (milestone 9, decided 2026-11-23): the
checker, `check_proof_inner`, as for CpcMini (`proofs/PathosProofs/Top.lean`).
The front end that builds its input from a proof's text (`pathos-elab`,
`crates/pathos/src/adapter.rs`, the untranslated `front.rs`) is tested
against Ethos and logos, not verified.
