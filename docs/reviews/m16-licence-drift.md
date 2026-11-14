# Review: milestone 16, the licence notice and keeping up with Ethos

Reviewed branch `m16` at 51ce987 (dc3f546 and 51ce987).

## Results

- `licenses/lgpl-3.0.txt` is byte for byte Ethos's file at `9217112f`
  (checked by the reviewer with `cmp`). `LICENSE`'s paragraph on
  `malachite` follows the GMP paragraph of Ethos's `COPYING`.
  `scripts/package` ships both; checked by Fable on Linux; the artifact
  steps run on the next push to `main`.
- Drift job, run 43646931219 (started by the push of dc3f546, against
  Ethos `main`): green. Ethos `main` is `REFERENCE_REV`, as its summary
  says, so the run repeats CI's comparison: tests 230, cli 1,192, bignum
  7, eoc 1,055 agree, fuzz none still differing; logos at its `main`
  (b3f0b24b, newer than the pin, compiles the same).
- Red demonstration: Fable's local `scripts/drift --rev 6cfb7ba7` (before
  PR #255 changed the Lean output) exits 1, eoc differing on 156 of 1,055
  cases. The same on GitHub needs `workflow_dispatch`, which GitHub allows
  only once `drift.yml` is on `main`: the reviewer runs it after the merge.

## Read

- `scripts/drift`: clones cvc5/ethos and logos into `target/drift` only,
  checks the harness pin, builds the reference with the harness's
  `build-ref --repo --out` (nothing in the harness checkout), runs each
  comparison with its log and status, and writes the summary. A build
  that fails is red ("could not be run"), not skipped.
- `drift.yml`: nightly, on demand with `ethos_rev` and `logos_rev`, and
  on pushes that change the job itself; `contents: read`, no secrets.

## Noted

- GitHub turns scheduled workflows off after 60 days without activity in
  the repository; documented in `README.md`.
