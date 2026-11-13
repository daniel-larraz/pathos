# Review: milestone 2 and gate 5

Reviewed 2026-11-13, at `m2` commit `409e705`, by a separate Claude session
(Opus 5.5).

**Verdict:** the review fixes are done as asked, and gate 5 passes. All five
gates in the brief have now passed.

## Gate 5, checked independently

`scripts/difftest perf`, one job at a time, reference rerun, on the harness
that measures time exactly (`daniel-larraz/ethos` `30b17e3b`):

| Criterion | Result |
| --- | --- |
| Total time no more than Ethos's | 8.53 s against 16.16 s (53%), over the 588 cases both accept |
| No case over 50 ms in Ethos more than 10% slower | 44 such cases; none slower; the worst takes 76% of Ethos's time (`proofs/regress1__quantifiers__006-cbqi-ite.cpc`) |
| Peak memory no more than Ethos's on any case | worst 69%; largest 18.5 MiB against 101.7 MiB |

Every run includes about 8 ms to start a process, the same for both
checkers, so the reviewer's count of cases over 50 ms (44) is a little higher
than the gate report's (39), and its worst ratio a little closer to 100%.

## Review fixes (`409e705`)

All five items of `m1-term-store.md` are done as asked: keyed hashing,
checked size limits without panics, literals stored once, the Clippy list,
and the debug check in `latin1::encode`. The decision to report running out
of 32-bit ids after the command, rather than making every constructor return
a `Result`, is accepted; it can only happen past 4 billion terms.

## Changes made in this review

- **Harness timing.** The harness polled for a child's exit with growing
  sleeps, so wall times were rounded up (302 of 630 Ethos runs read exactly
  32 ms), as the gate report found. Fixed in `daniel-larraz/ethos`
  `30b17e3b`, now pinned in `difftest.env`.
- **The Unicode guardrail is now an error.** `disallowed_methods` was a
  warning, so a forbidden call still let `cargo clippy` exit 0. It is now
  `deny` in `[workspace.lints.clippy]`; a test call to `str::trim` fails the
  build.
- **`chars_above_255_are_bugs` runs only with debug assertions.** It expects
  the panic of a `debug_assert!`, so it failed in release builds and stopped
  the crate's other tests there. `cargo test` and `cargo test --release` both
  pass now.
- The gate report cited the fix commit as `9beb...`; it is `409e705`.

## Next

- Merge `m2` (which contains `m1-spike`) into `main` and push, with the
  user's agreement.
- Widen the evidence: large proofs from cvc5's slower regression levels, and
  runs with non-default options. Neither is covered by the harness yet.
