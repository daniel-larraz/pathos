# Review: milestone 13, lean-meta and the end of the eoc port

Reviewed branch `m13` at 0ddbb85 (commits cfc9e66 and 0ddbb85).

## Results, rerun by the reviewer

- `scripts/difftest eoc`, no filter: 3,507 cases, all the same (3,322 ok,
  185 errors in both). This is every stage on every rule of the Ethos test
  signatures and of logos's CPC, and logos's `lean --all`.
- `scripts/full-check --quick` passes. No new dependency.

## Logos's acceptance check

Repeated with Fable's commands, from the pathos checkout, with
`H=<harness>/tools/difftest` and `A` a scratch directory:

```sh
cp -R $H/work/logos $A/logos && cp -R $H/work/ref/9217112fc9b1/src $A/ethos &&
  rm -rf $A/ethos/tools/eoc/out && mkdir -p $A/ethos/build-eoc
ETHOS_PLUGIN_SOURCE_DIR=$A/ethos ETHOS_PLUGIN_OUTPUT_DIR=$A/ethos/build-eoc/out \
  CARGO_TARGET_DIR=$A/target cargo build --release --quiet --bin pathos-eoc &&
  cp $A/target/release/pathos-eoc $A/ethos/build-eoc/ethos-eoc
cd $A/logos && env -u ETHOS_PLUGIN_ROOT -u ETHOS_PLUGIN_OUTPUT_DIR \
  install/install-cpc.sh --all --cached --check --ethos $A/ethos
```

- With `pathos-eoc`: exit 0, "Up to date with the cached signature: Cpc,
  CpcMini.", "Nothing was written." The script used the binary in place
  (it did not try to build one), and the harness's `work/logos` is
  unchanged.
- Negative control, run by the reviewer: the same, with `ethos-eoc` a
  wrapper that runs `pathos-eoc` and then changes one line of
  `lean_meta_checker_gen.lean`: exit 1, "Could not be shown up to date with
  the cached signature: Cpc, CpcMini." So the check does compare what the
  binary writes.

## CI

A new job, `eoc`, builds the reference `ethos-eoc` (cached under its own
key), clones logos at `LOGOS_REV`, and runs the eoc gate on every case of
the test signatures and logos's three whole-signature cases (1,055 cases),
leaving the 2,452 per-rule CPC cases to local runs. It has not run on
GitHub yet: it runs on the first push. Two things only that run can show:
the clone of logos into the harness's work directory, and
`scripts/difftest`'s memory cap, which falls back to a warning without a
systemd user scope.

## Noted

- Outside `pathos-eoc`: `Checker::compute_let_binding` is now public, and
  `State::echo` no longer prints a message when a plugin's echo hook fails
  (Ethos aborts inside the hook). All gates pass.
- The reference segfaults on `(echo "smt-meta <unbound name>")`; pathos
  reports an error. Recorded in `docs/ethos-differences.md`.
- The evaluation hooks (`EvalPlugin`) are still used by no stage.
- Two helper worktrees remain under `.claude/worktrees/`.
