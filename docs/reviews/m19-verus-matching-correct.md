# Review: milestone 19, matching is correct (branch `verus`)

Reviewed branch `m19-verus-matching-correct` at c5c4824 (e56af58 to
c5c4824; the last two commits are documentation only).

## Results

- CI run 43676096903 on 37ca07c, the last commit that touches code.
- Fable's local `scripts/verify`: `pathos_term` 178, `pathos_check` 15
  verified, 0 errors; `scripts/full-check --quick` passes. Every added line
  of code is behind `cfg(verus_keep_ghost)` or in a proof block, so the
  binaries are the same code as before; the gates agree.

## Proved

- `match_terms`: when it returns true, the context it returns, applied to
  the pattern on the store's tree view (`inst`), gives the term's tree.
- `match_cases`: a returned body belongs to a case whose pattern's
  children instantiate to the arguments.
- `match_terms` terminates (the measure: the sum of the patterns' tree
  sizes on the stack); termination is off the assumed list.
- The store's invariant now covers the flags: `is_ground` holds exactly
  for trees without a parameter.
- Ethos's matching quirks are part of the specification, not omitted: a
  ground pattern matches only itself, and types are not compared.

Not proved: completeness, and that `visited` is only an optimisation.
New assumptions, listed in the report: the derived `==` of `Term` is
equality, and the derived `Hash` and `Eq` of a pair of terms agree.

## Found

Writing the precondition of `match_terms` showed that
`TypeChecker::getTypeAppInternal` rebinds a parameter that is quoted
(`(eo::quote n)`) when an earlier argument's type already bound it, so an
application that does not evaluate gets a type from the quoted argument
alone. Reproduced by the reviewer on Ethos 9217112f with Fable's input; my
first attempt, with a program whose case matched, evaluated the
application before it was typed and hid the quirk. Ethos asserts the
parameter is unbound just before assigning it, so a debug build stops on
the input. pathos reproduces the release behaviour. Reported as
cvc5/ethos#269.
