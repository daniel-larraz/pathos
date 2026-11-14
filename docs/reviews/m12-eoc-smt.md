# Review: milestone 12, model-smt and smt-meta

Reviewed branch `m12` at f19d78d (commits 2dbcd9b to f19d78d).

## Results, rerun by the reviewer

- `scripts/difftest eoc --filter '/(trim-defs|desugar|desugar-eo|vc|sygus)(/|$)'`:
  2,679 cases, all the same (2,553 ok, 126 errors in both). The filter
  contains milestone 11's.
- `scripts/full-check --quick` passes.
- No new dependency; no gitlink left in the tree (the one committed by
  mistake in 9b71b82 is removed by 1a7fb0c).

## The points of the milestone 11 review

1. **Directory fallback:** done (2dbcd9b). `pathos-eoc` reads
   `ETHOS_PLUGIN_SOURCE_DIR` and `ETHOS_PLUGIN_OUTPUT_DIR` when it is built
   (`option_env!`), and the run-time variables still win. Unlike the CMake
   build, which always sets them, a `pathos-eoc` built without them has no
   fallback; milestone 13's logos check has to build it with both set.
2. **Queued hooks:** no eoc stage of the reference changes the state from a
   hook (model-smt overrides only `bind` and `finalize`), so the order of
   delivery cannot matter for these stages. The earlier count included
   `cpp_compiler`, which is out of scope.

## Noted

- `smt_meta_sygus.cpp` iterates a map keyed by address; Fable argued that
  the order cannot reach the output, and the 2,679 cases agree.
- Where the C++ trusts an unchecked `Assert` about a term's shape, the
  stages stop with "unexpected term" instead of reading out of bounds.

## Housekeeping

The helper agent's worktree (`.claude/worktrees/agent-ae691b8eff9cf9965`,
branch `worktree-agent-ae691b8eff9cf9965`) is still there; it can be
removed with `git worktree remove` and `git branch -D` once nothing on it
is needed.
