module
public import CpcMini.Logos
import all CpcMini.Logos
public import PathosProofs.Util

/-!
# Which terms are the nil of a list operator, in CpcMini

The definitions that `Runtime/Lists.lean` unfolds (`simp [eo_list_nil]`)
to show that the nil of a list operator is never an application of two
arguments. They depend on the calculus: CpcMini's `__eo_is_list_nil`
decides it in its own cases. For another calculus, `scripts/proofs-instance`
writes this file from the calculus's Lean, with the helpers that
`__eo_is_list_nil` calls, and the definitions those call in turn.
-/

attribute [eo_list_nil] Eo.__eo_is_list_nil
