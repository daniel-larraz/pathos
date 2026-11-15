# Review: milestone 18, matching cannot panic (branch `verus`)

Reviewed branch `m18-verus-matching` at 5e80f6b (bbf1d67 to 5e80f6b).

## Results

- CI run 43672981939: every job green. The `verify` job checks both crates
  on GitHub: `pathos_term` 165 verified, `pathos_check` 2 verified, 0
  errors; its two-crate flow (`--compile --export`, then `--extern
  --import`) had only run locally before.
- Fable's local `scripts/full-check --quick`: pass. `Cargo.lock`
  unchanged; `scripts/unsafe-reach` as in milestone 17.

## Read

- `crates/pathos-check/src/matching.rs`: `match_terms` and `match_cases`
  are functions of the term store, so the `Checker` (hash maps, the plugin
  trait object, closures) stays out of Verus. Compared with the code they
  replace in `typing.rs` and `eval.rs`: the same traversal, the context
  cleared for each case, the early return on an arity mismatch (the warning
  stays in the checker, at the same point), a fresh visited set for each
  argument, the body from child 1 of the case. The two loops that became
  indexed visit the children in the same order. No change in behaviour,
  as the gates confirm.
- Proved: neither function panics, and every term read, pushed or bound is
  a term of the store; existing bindings are kept. 49 lines of
  specification and 5 of proof for 83 of code, far under the estimate,
  because the store's contracts from milestone 17 carry it.
- Assumed, and listed: `is_program` (every case has two children), which
  the parser guarantees and a forged snapshot does not; that the derived
  order of `Term` is a total order agreeing with equality. Termination of
  `match_terms`'s loop is not proved.

## Scope

`check_step`, `get_type_app` and `evaluate_nil` are not covered: the rule's
premises, `:args` and conclusion are matched through `match_cases`, and
the rest belongs with the evaluator. That reading of the milestone is
right.

## Next

The statement of matching's correctness and the lemmas it needs are in
the report; the one the store lacks is anything about the `is_ground`
flag.
