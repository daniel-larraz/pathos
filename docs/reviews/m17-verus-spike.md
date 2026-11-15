# Review: milestone 17, a Verus feasibility spike

Reviewed branch `m17` at 6cb32a1 (0b304eb to 6cb32a1, with the flaky-test
fix d886202 and 4e6e716).

## Results

- CI run 43669810237: every job green, including the first run of the new
  `verify` job (Verus downloaded on GitHub, its SHA-256 checked against the
  pin in `scripts/verify` before unpacking, the proofs checked) and the six
  platforms.
- Fable's local `scripts/full-check --quick` and `scripts/verify` (165
  verified, 0 errors, about 30 s): pass. `Cargo.lock` is unchanged and no
  dependency was added: the specifications are behind
  `cfg(verus_keep_ghost)`, which only Verus sets.
- `m17` merges cleanly with `main` (which gained e1dbb44, Daniel's approval
  of `docs/dependencies.md`, meanwhile).

## Read

- The three rewrites in shipped code that are more than cosmetic:
  `mk_count` uses `wrapping_add` (what a release build did anyway; only a
  debug build, which would have panicked on overflow, behaves differently),
  the hash tables' growth test multiplies in `u128` (the same comparison,
  without overflow), and `euclidean_qr` is built from the floor-division
  wrappers and proved to give the Euclidean quotient and remainder (the
  `bignum` gate agrees).
- `docs/verus-spike.md`: what is verified, the trusted list (38 `malachite`
  wrappers, about 35 other assumptions), the Rust features Verus accepted
  and rejected, the cost (about two lines of specification and proof per
  line of code), and the estimate for the checker: panic freedom of
  matching, the evaluator and step checking at four to six times this
  spike, agreement with a written semantics at fifteen to twenty-five
  times, with the semantics itself as the main risk.

## For Daniel

- Whether to go further; the report suggests matching as the next piece.
- The 38 assumed specifications of the `malachite` wrappers (a table in
  the report) are where a mistake would go unnoticed, and deserve a human
  reading.
