module
public import CpcMini.Logos
import all CpcMini.Logos
public import CpcMini.SmtEval
import all CpcMini.SmtEval
public import PathosProofs.Util

/-!
# The definitions the library unfolds that depend on the calculus, in CpcMini

For another calculus, `scripts/proofs-instance` writes this file from the
calculus's Lean.

- `eo_list_nil`: what `Runtime/Lists.lean` unfolds to show that the nil of
  a list operator is never an application of two arguments. CpcMini's
  `__eo_is_list_nil` decides it in its own cases; another calculus's calls
  helpers, which are listed too, with what they call in turn.
- `eo_logos_eq`: what `logos_eq` (Tactic.lean) unfolds when the patterns of
  a program repeat a variable, which logos checks with `__eo_eq`, `__eo_and`
  and `__eo_ite`: those of them that the calculus defines, and the natives
  they reduce to.
-/

attribute [eo_list_nil] Eo.__eo_is_list_nil

attribute [eo_logos_eq] Eo.__eo_and SmtEval.native_and SmtEval.native_ite Eo.native_teq
