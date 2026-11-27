module
public import Cpc.SmtSyntax
public import PathosProofs.Runtime.Embed

/-!
# `Valid` of the CPC's own argument types (CPC only)

As for the other types of the checker's arguments (`Runtime/Embed.lean`),
`Valid` is `True`, since no case tells apart values that a store cannot
hold.
-/

@[expose] public section

namespace pathos_compiled_checker

-- SMT bindings: `$smtx_typeof_bindings` and `$eo_to_smt_bindings_snoc`
-- match their constructors, and pass their SMT terms and types on to
-- `$smtx_typeof` (whose `Valid` is `True`) or into a new binding
instance : Valid Smtm.SmtBindings := ⟨fun _ => True⟩

end pathos_compiled_checker
