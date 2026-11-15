# Review: milestone 20, the snapshot reader cannot panic (branch `verus`)

Reviewed branch `m20-verus-snapshot` at 0e29750 (19667cc to 0e29750).

## Results

- CI run 43680193033 (see the merge commit).
- Fable's local `scripts/verify` (`pathos_term` 209, `pathos_check` 18
  verified, 0 errors) and `scripts/full-check --quick`, including the
  `snapshot` gate: pass. `Cargo.lock` unchanged; `scripts/unsafe-reach`
  gives the same 17 `unsafe` lines.
- Checked by the reviewer: the stricter reader still accepts the snapshot
  of the real signature. A snapshot of the corpus's `Cpc.eo` written by
  this build is used: 60 cvc5 proofs take 1.9 s with it and 3.1 s without.
  This matters because a new check that rejected a valid snapshot would be
  silent (the fallback loads the signature) and no gate would differ.

## What changed

- `TermStore::read_from` no longer copies a store out of the file: it
  rebuilds it with `mk_symbol`, `mk_lit` and `mk` and rejects the file if a
  term does not come out at its position, so the store it returns
  satisfies the proved invariant by construction. Verus proves that it, the
  codec `Reader` and `Lit::read_from` cannot panic on any bytes.
- The shapes the rest of the code relies on are checked by a reader, each
  listed in the report: child counts per kind, `is_program` (proved to
  follow from `is_program_term`), builtins being compound, the builtin
  terms being the checker's own, strings being Latin-1. Three counters now
  wrap.
- All 23 "Crafted snapshot" rows of `docs/panics.md` are closed, each with
  what holds it; for the store, Verus; for the checker's and the state's
  tables, ordinary checks with tests (unit tests per check, and an
  end-to-end test that forges six states: two of them panicked before, all
  six are now ignored).
- Fuzzing with checksum-preserving mutations: 84,000 runs, no panic. As
  the report says, it also found nothing on the old code, so the forged
  tests, not the fuzzing, are the evidence.

## The first question for the Ethos developers

The report: it can be withdrawn as far as panics go, if milestone 14's
inventory of the checker's tables was complete, and once this reaches
`main`. Agreed. Since the new checks do not depend on Verus, they could be
taken to `main` on their own, without the proofs; that is Daniel's call.

## Noted

- A gate that asserts the snapshot is used (and not silently ignored)
  would make the reviewer's timing check permanent; it belongs in the
  harness.
