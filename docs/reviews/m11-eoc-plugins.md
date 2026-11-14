# Review: milestone 11, the plugin interface and the first eoc stages

Reviewed commits a7d8aa1 and fa6bc22 on branch `m11`.

## Results, rerun by the reviewer

- `scripts/difftest eoc --filter '/(trim-defs|desugar|desugar-eo)(/|$)'`:
  1,025 cases, all the same (1,021 ok, 4 errors in both).
- `scripts/full-check --quick` passes, including the snapshot gate.
- `pathos-eoc` inherits the workspace lints, so `unsafe_code = "forbid"`
  holds; `Cargo.lock` gains only the new crate.

## To fix before the eoc port is done

1. **No fallback for the plugin directories.** `pathos-eoc` requires
   `ETHOS_PLUGIN_ROOT` and `ETHOS_PLUGIN_OUTPUT_DIR`. `ethos-eoc` falls back
   to directories compiled in by CMake (`ETHOS_PLUGIN_SOURCE_DIR`,
   `ETHOS_PLUGIN_OUTPUT_DIR`), and eoc's driver relies on that: it sets
   neither variable. The harness sets both, so the gate does not show it,
   but logos's `install/install-cpc.sh`, which runs the driver as it is,
   would fail with `pathos-eoc`. Logos's check is the acceptance test of
   the eoc milestones, so this has to work: give `pathos-eoc` the same
   fallback (for instance from variables read at build time with
   `option_env!`, documented in the crate), and keep the environment
   variables taking precedence, as in Ethos.
2. **Queued hooks.** Hooks raised inside the checker are delivered before
   the next parser hook and at the end of each command, and a plugin's own
   changes to the state raise no hooks for itself. Fable flagged that
   model-smt calls `bind` and `reset` from a hook; milestone 12 will show
   whether the order matters there.

## Noted

- The evaluation hooks (`EvalPlugin` in pathos-check) are untested, since
  no eoc stage uses them; `linear_patterns` (milestone 15) may.
- Errors raised by a stage inside a hook are reported when the command
  ends, where the C++ aborts at once. Equal output so far.
