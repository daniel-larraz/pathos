# pathos

pathos reimplements the Ethos proof checker (C++) in Rust. It must behave
exactly like Ethos and, unlike Ethos, be memory safe. Read `docs/brief.md`
first: it has the goals, the reference, the design decisions, the
memory-safety requirements, and the milestones with their gates.

This codebase is yours: how it's built is your call within the design
decisions in the brief, and you'll keep building on it. Restructure when the
code calls for it.

## Commands

- `cargo build`, `cargo test`, `cargo clippy --all-targets`
- `scripts/difftest <gate> [options]` compares pathos with Ethos (see the
  script's header). Options pass through to the harness, e.g.
  `--filter 'tests/simple'`, `--show-all`, `--report /tmp/r.json`.
- `ETHOS_HARNESS` (set in `.difftest.local`) points at the Ethos checkout
  holding the harness, the reference C++ source (`src/`), the user manual and
  the regressions (`tests/`).

## Rules

- **Never edit the Ethos checkout, the harness, the corpus or
  `difftest.env`.** They define what "matches Ethos" means; a change there
  can make differences disappear without fixing them. If the harness looks
  wrong, stop and say so.
- **Match the C++ binary, not your reading of it.** Error messages must be
  identical, including their position and wording. When unsure what Ethos
  does, run the reference binary on a small input.
- **Memory safety is a requirement, not a preference.** Never relax the
  `unsafe_code = "forbid"` lint. Keep `docs/dependencies.md` up to date, and
  ask the user before adding a dependency that contains `unsafe` code or
  binds C code.
- **No special cases for particular tests or proofs.** Every fix must follow
  from Ethos's behaviour in general.
- **Keep the design decisions in the brief** unless the user agrees to change
  one. If one gets in the way, explain the problem and propose the change.
- Behaviour you think is a bug in Ethos still gets matched; record it in
  `docs/ethos-differences.md`.

## Finishing work

Work through each milestone until its gate passes. Errors, failing cases,
timeouts and slow builds are ordinary obstacles: diagnose them and carry on.
Stop before the gate only for a decision that is the user's (a design
decision, the harness, a performance margin) or for something you cannot work
around. Stopping at each gate for review is intended.

## Git

Commit as you go on a branch per milestone (`m1-spike`, `m2-tests`, ...),
with messages that say what changed and why. Don't push, merge into `main` or
rewrite history without the user.

## Reporting

The user reads your report at each gate without having watched the work.
Say which gate passed, the harness numbers, what was hard, what you decided
and why, and what the user needs to look at or decide. Point to files and
commits. Mention anything you changed outside the milestone's scope.
