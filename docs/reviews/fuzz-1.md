# Fuzzing, first run: findings for milestone 8

Run 2026-11-14 by a separate Claude session (Opus 5.5), with the harness's new
`fuzz` command (`daniel-larraz/ethos` `296197e2`): seed 1, 16 workers,
10 minutes, pathos at `ae68349` against Ethos `9217112f`.

**888,900 mutants; 888,408 agree (99.95%), 44 time out on both sides, and 448
differ, in 40 groups,** plus one group of Ethos crashes. The groups are in
`$ETHOS_HARNESS/tools/difftest/fuzz-findings/2026-11-14-seed1/<id>/`: the
minimized `input.*`, the `original.*` mutant, and `info.json` with the seed
file, the options and both checkers' normalized output.

To reproduce: `scripts/difftest fuzz` replays all of them. To look at one,
run both checkers on its `input.*` from a copy of Ethos's `tests/`
directory (or of the corpus, for the two proof findings), with the options
in its `info.json`; error messages contain the file's path.

## Findings by probable cause

The grouping below is the reviewer's reading of the messages; one cause may
turn out to be several, or two to be one.

1. **A panic** (fix first). `faba74f25eeb`, 50 hits, from `par-dt.eo`:
   `index out of bounds` at `crates/pathos-term/src/store.rs:523`. Ethos
   reports `Type checking failed`.

2. **Two hangs where Ethos crashes** (fix first). `61b51e877e36` and
   `ff54258e0b01`, from `ite-compile-test.eo`: `eo::requires` or `eo::is_eq`
   applied to one argument. Ethos prints `Wrong number of arguments when
   applying literal op ...` and then dies with a segmentation fault; pathos
   runs until the 10-second timeout. pathos must terminate with an error. As
   Ethos gives no message to match, any clear error will do; record the
   choice in `docs/ethos-differences.md`.

3. **Unterminated string literals and quoted symbols** (22 findings). The
   message `Expected ..., got `<token>` (UNTERMINATED_STRING_LITERAL)` (or
   `UNTERMINATED_QUOTED_SYMBOL`) shows a different slice of the input: pathos
   includes more text, or one more space. Probably one cause in the lexer.
   `221e02acf44c 2d04def6c36f 38c3f0545c44 39dbf42b2315 3afa8225bb89
   685fd2339c1f 7c8bcf32c79f 7d8c85737a64 7fdb3160789d 800a2f74b2e1
   8631783028d2 93dc87392741 971aa0d5281f 99f9a2953396 c150d9545bd0
   c69ba665e7cd c907b2ab7a34 d0efcb6c3eb1 db7e354fd2df e717772c5895
   ef5c73624924 fe3429d089c4`. Probably also `52c54ddd9624` (a string token
   in `Expected Eunoia command`).

4. **`eo::nil` in error messages** (3 findings). Ethos prints a list's nil
   terminator evaluated, for example `(@@TypedList.nil Bool)` or `#b0000`;
   pathos prints it unevaluated: `(eo::nil @@TypedList.cons (eo::typeof b))`.
   `6f008521b732 8c77e11502fe cebe255ce77d`.

5. **A missing term printed as `([NONE])`** (1 finding). Ethos prints
   `Expression: ([NONE])` where pathos prints `Expression: (_ = d)`.
   `105429b427d3`, from `chainable.eo`.

6. **Program evaluation in error paths** (10 findings), probably several
   causes. pathos reports a different failure than Ethos: for example
   `*** Bad number of arguments provided in function call to ...` or
   `No program defined for ...` where Ethos reports the failed step, or the
   reverse; or different arguments in the message (`[substitute a b]`
   against Ethos's `[substitute a a]`, `[arith.eval 3 3]` against
   `[arith.eval 0 0]`). `054c1d58d487 0f1e2152e7cc 3736dd030ae7
   41f05f94f41b 439a0d2cb856 51c9af2fb743 727102e9f3df 7d63f43fe9fe
   9dd82f19efb5 e081f9cc584f`.

## Ethos crash, not for pathos to match

`5c8e2fd48d70`, 287 hits: Ethos segfaults on `eo::requires` applied to one
argument inside a rule's `:requires`. pathos reports an error, which is
correct. This is an Ethos bug worth reporting upstream.

## After fixing

Run `scripts/difftest fuzz` until it passes, then the other gates. New
fuzzing runs, with more seeds or longer, are the reviewer's job, in the
harness; they will add directories next to `2026-11-14-seed1`.
