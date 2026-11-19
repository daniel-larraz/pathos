module
public import MiniChecker
public import CpcMini.Logos
public import PathosProofs.Util
public import PathosProofs.Store.Sem
public import PathosProofs.Programs.Frame
public import MiniCases
import all MiniCases

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

/-- How a handle stands for a value of the type `α`: logos's terms, proofs,
states, native values each have their relation. The generated theorems
are stated with it, so that they do not name the types of a program's
arguments: Lean finds them from the program's signature. -/
class Represents (α : Type) where
  rep : Store → Term → α → Prop

@[reducible] instance : Represents Eo.Term := ⟨fun s t x => s.Rep t x⟩

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

/-- Ends a case at a place where its pattern does not match: the store has
the invariant `hinv` and has grown as `hG` says, and the case's function
`cd` (of `MiniCases`) answers `none`. The last is found by unfolding it and
using the hypotheses in sight: what `unapply` said of a term that is not
an application, what a comparison of two handles said of the terms they
stand for. -/
macro "nm_close" : tactic =>
  `(tactic| first
    | rfl
    | (simp_all; done)
    | (injections; simp_all; done)
    | (injections; subst_vars; simp_all; done))

syntax "no_match " ident ppSpace ident " in " ident : tactic
macro_rules
  | `(tactic| no_match $hinv $hG in $cd) =>
    `(tactic| (
      simp only [Std.bind_ok, uncurry_apply_pair, ite_true, WP.dspec_ok, WP.uncurry'_pair]
      refine ⟨$hinv, $hG, ?_⟩
      unfold $cd
      first
        | (split <;> nm_close)
        | (simp_all; done)))

/-- `pat_unapply h as ⟨f, a, x, y, hf, ha⟩ else hinv hG in cd`: the pattern
takes the term that `h` speaks of apart as an application. Goes on with
the two handles `f` and `a`, the two terms `x` and `y`, and what the
handles stand for; where the term is not an application the case ends
(`no_match`). -/
syntax "pat_unapply " term " as " "⟨" ident ", " ident ", " ident ", " ident ", " ident ", "
  ident "⟩" " else " ident ppSpace ident " in " ident : tactic
macro_rules
  | `(tactic| pat_unapply $h as ⟨$f, $a, $x, $y, $hf, $ha⟩ else $hinv $hG in $cd) =>
    `(tactic| (
      rcases Store.Rep.unapply $h with ⟨$f, $a, $x, $y, heq, $hf, $ha, hu⟩ | ⟨hne, hu⟩
      case inr => (rw [hu]; no_match $hinv $hG in $cd)
      subst heq
      rw [hu]
      simp only [Std.bind_ok, uncurry_apply_pair]
      clear hu))

/-- `pat_same hv : a = b from hiff else hinv hG in cd`: the generated
`if a != b` on two handles, where `hiff` says that `a = b` exactly when the
two terms are equal. Goes on with `hv : a = b`; where they differ the case
ends. -/
syntax "pat_same " ident " : " term:51 " = " term:51 " from " term " else " ident ppSpace ident
  " in " ident : tactic
macro_rules
  | `(tactic| pat_same $hv : $a = $b from $hiff else $hinv $hG in $cd) =>
    `(tactic| (
      rw [Term.ne_eq]
      simp only [Std.bind_ok]
      rcases Decidable.em ($a = $b) with $hv | $hv
      case inr => (
        rw [show decide ($a ≠ $b) = true from by simpa using $hv]
        have hiff := $hiff
        no_match $hinv $hG in $cd)
      rw [show decide ($a ≠ $b) = false from by simp [$hv:ident]]
      simp only [Bool.false_eq_true, ite_false]))

/-- Ends a case that matched: the result `h` speaks of is what the case's
function `cd` answers. -/
syntax "case_done " ident ppSpace ident " with " term " in " ident : tactic
macro_rules
  | `(tactic| case_done $hinv $hG with $h in $cd) =>
    `(tactic| (
      simp only [WP.dspec_ok, WP.uncurry'_pair]
      refine ⟨$hinv, $hG, _, ?_, $h⟩
      simp [$cd:ident]))

end pathos_compiled_checker
