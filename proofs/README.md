# proofs

Lean proofs about the compiled checker: that the Rust which Charon and
Aeneas translate does what logos's definitions say. A Lake project of its
own, outside the Rust workspace. What is proved, what is trusted, and what
is missing for a theorem about `pathos` are in
[docs/proofs.md](../docs/proofs.md).

| | |
| --- | --- |
| `MiniChecker/`, `MiniChecker.lean` | Generated: the Lean of `generated/cpcmini-checker`. Never edited (`scripts/proofs-build --translate DIR` writes it again and compares). |
| `PathosProofs/Trusted.lean` | The axioms about the Rust that is not translated. |
| `PathosProofs/Store/` | The store: its table of terms, its invariant, its operations, the cache of program results, and the relation between handles and logos's terms. |
| `PathosProofs/Runtime/` | Written by hand: what the runtime's operations and the signature's constructors do, in the form generated proofs use, and the relations between handles and logos's values. |
| `PathosProofs/Tactic.lean` | Written by hand: the tactics that the lines of generated proofs are written in. |
| `MiniCases.lean`, `MiniCacheSem.lean`, `MiniProofs.lean` | Generated with `generated/cpcmini-checker` (`scripts/generate-mini`): the cases of logos's programs as functions, what the cache of results holds, and the proofs that the generated programs compute what logos's functions do. Never edited. |
| `axioms-allowed.txt` | Every axiom a theorem may rest on. |
| `audit/Axioms.lean` | Collects the axioms in use, for `scripts/proofs-axioms`. |
| `pins.env` | The versions of Lean, Mathlib, Aeneas, Charon and logos. |

```
scripts/proofs-build        # checks the pins, builds under 8 GiB, checks the axioms
```

Needs elan. The first build fetches Mathlib's compiled files and builds
Aeneas's library and logos's CpcMini proofs (a few minutes).
