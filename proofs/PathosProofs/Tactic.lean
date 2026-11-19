module
public import MiniChecker
public import CpcMini.Logos
public import PathosProofs.Util
public import PathosProofs.Store.Sem

/-!
# The step after a store operation

A proof about a generated function follows its code, and after every
operation on the store it does the same things: name the result and the
new store, take the invariant of the new store, extend the record of how
the store grew, carry every fact about a handle over to the new store, and
on an error finish at once. `store_step` does that, so that a generated
proof has one line per operation.

-/

@[expose] public section

namespace pathos_compiled_checker

open Aeneas Aeneas.Std Result

/-- `carry_one h hg`: the fact `h` about a store, carried over to the store
it has grown to (`hg`). A fact carries over when it is monotone in the
store: what a handle stands for is. Each relation built on that adds its
own rule here (`macro_rules`), next to its monotonicity lemma. -/
syntax "carry_one " ident ppSpace term : tactic
macro_rules
  | `(tactic| carry_one $h $hg) => `(tactic| replace $h:ident := Store.Rep.grows $h $hg)

/-- Carries the facts named over to a store that has grown. -/
syntax "transport " term " at " (ppSpace colGt ident)* : tactic
macro_rules
  | `(tactic| transport $hg at $hs*) => do
    let ts ← hs.mapM fun h => `(tactic| carry_one $h $hg)
    `(tactic| ($[$ts];*))

/-- `store_step with spec as ⟨v, s', hinv, h⟩ growing hG carrying h1 h2 …`:
one operation on the store whose specification `spec` says that the new
store has the invariant, has grown, and what the result is on `Ok`. Leaves
the `Ok` case with the result `v`, the store `s'`, its invariant `hinv`
and the fact `h` about `v`; `hG` (how the store has grown since the
function began) is extended, and the facts after `carrying` are carried
over. An `Err` ends the function, with nothing to prove about its result.
-/
syntax "store_step " "with " term " as " "⟨" ident ", " ident ", " ident ", " ident "⟩"
  " growing " ident (" carrying" (ppSpace colGt ident)*)? : tactic
macro_rules
  | `(tactic| store_step with $e as ⟨$v, $s', $hinv, $h⟩ growing $hG carrying $hs*) => do
    let b (i : Lean.Ident) : Lean.TSyntax ``Lean.binderIdent :=
      ⟨Lean.mkNode ``Lean.binderIdent #[i]⟩
    let r := Lean.mkIdent `r
    let hg := Lean.mkIdent `hg
    `(tactic| (
      step with $e as ⟨$(b r), $(b s'), $(b hinv), $(b hg), $(b h)⟩
      transport $hg at $hs*
      replace $hG:ident := Store.Grows.trans $hG $hg
      cases $r:ident
      case Err => (simp only [WP.dspec_ok, WP.uncurry'_pair]; exact ⟨$hinv, $hG, trivial⟩)
      rename_i $v:ident
      simp only at $h:ident ⊢
      clear $hg))
  | `(tactic| store_step with $e as ⟨$v, $s', $hinv, $h⟩ growing $hG) =>
    `(tactic| store_step with $e as ⟨$v, $s', $hinv, $h⟩ growing $hG carrying)

end pathos_compiled_checker
