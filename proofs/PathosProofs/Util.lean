module
public import Aeneas

/-!
# Small tools for the proofs

Admissibility of a partial-correctness statement about a function of
several arguments, which the induction over a function that Aeneas wrote
with `partial_fixpoint` asks for.
-/

@[expose] public section

namespace pathos_compiled_checker

open Aeneas Aeneas.Std Result Lean.Order

theorem dspec_admissible2 {α β γ} (a : α) (b : β) (p : WP.Post γ) :
    admissible (fun f : α → β → Result γ => WP.dspec (f a b) p) :=
  admissible_apply (fun _ (g : β → Result γ) => WP.dspec (g b) p) a
    (WP.dspec_func_admissible b p)

theorem dspec_admissible3 {α β γ δ} (a : α) (b : β) (c : γ) (p : WP.Post δ) :
    admissible (fun f : α → β → γ → Result δ => WP.dspec (f a b c) p) :=
  admissible_apply (fun _ (g : β → γ → Result δ) => WP.dspec (g b c) p) a
    (dspec_admissible2 b c p)

theorem dspec_admissible4 {α β γ δ ε} (a : α) (b : β) (c : γ) (d : δ) (p : WP.Post ε) :
    admissible (fun f : α → β → γ → δ → Result ε => WP.dspec (f a b c d) p) :=
  admissible_apply (fun _ (g : β → γ → δ → Result ε) => WP.dspec (g b c d) p) a
    (dspec_admissible3 b c d p)

theorem getElem!_eq {α} [Inhabited α] (l : List α) (i : Nat) (h : i < l.length) :
    l[i]! = l[i] := by simp [h]

/-- A pure value in a computation, where Aeneas's own lemmas do not know
the function that made it. -/
@[step]
theorem lift_spec {α} (x : α) : lift x ⦃ y => y = x ⦄ := by
  simp [lift]

/-- What a partial specification says of a value the computation returns. -/
theorem dspec_of_ok {α} {m : Result α} {p : WP.Post α} {r : α}
    (h : WP.dspec m p) (hm : m = ok r) : p r := by
  subst hm; simpa using h

/-- A computation that is specified returns the value it returns. -/
theorem dspec_self {α} {m : Result α} {p : WP.Post α} (h : WP.dspec m p) :
    WP.dspec m (fun r => m = ok r ∧ p r) := by
  cases hm : m.match with
  | ok a =>
    have := Result.match.isOk.mp hm
    subst this
    simpa using h
  | vis e k =>
    have := Result.match.isVis.mp hm
    subst this
    simp at h
  | div =>
    have := Result.match.isDiv.mp hm
    subst this
    simp

/-- Proves that a statement `∀ args, hypotheses → f args ⦃ post ⦄div` about
`f` is admissible. -/
macro "prove_adm" : tactic =>
  `(tactic| (
      (repeat' (apply Lean.Order.admissible_pi; intro))
      first
        | apply WP.dspec_func_admissible
        | apply dspec_admissible2
        | apply dspec_admissible3
        | apply dspec_admissible4))

end pathos_compiled_checker
