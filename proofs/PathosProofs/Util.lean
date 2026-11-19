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

/-- The platform has a `usize` of at least 40 bits: in practice, of 64.
The store's table of terms doubles with `len * 2`; with up to 2^32 terms
that is up to 2^35 slots, which a 32-bit `usize` cannot count. Every
theorem that reaches `Store.intern` has this as a hypothesis. -/
def Platform64 : Prop := 2 ^ 40 ≤ Usize.max

theorem getElem!_eq {α} [Inhabited α] (l : List α) (i : Nat) (h : i < l.length) :
    l[i]! = l[i] := by simp [h]

theorem getElem!_append_left {α} [Inhabited α] (l r : List α) (i : Nat) (h : i < l.length) :
    (l ++ r)[i]! = l[i]! := by
  rw [getElem!_eq _ _ (by simp; omega), getElem!_eq _ _ h, List.getElem_append_left h]

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

/-- A computation with a total specification returns a value. -/
theorem spec_returns {α} {m : Result α} {p : WP.Post α} (h : WP.spec m p) :
    ∃ v, m = ok v ∧ p v := by
  cases hm : m.match with
  | ok a =>
    have := Result.match.isOk.mp hm
    subst this
    exact ⟨a, rfl, by simpa using h⟩
  | vis e k =>
    have := Result.match.isVis.mp hm
    subst this
    simp at h
  | div =>
    have := Result.match.isDiv.mp hm
    subst this
    simp at h

theorem dspec_admissible5 {α β γ δ ε ζ} (a : α) (b : β) (c : γ) (d : δ) (e : ε)
    (p : WP.Post ζ) :
    admissible (fun f : α → β → γ → δ → ε → Result ζ => WP.dspec (f a b c d e) p) :=
  admissible_apply (fun _ (g : β → γ → δ → ε → Result ζ) => WP.dspec (g b c d e) p) a
    (dspec_admissible4 b c d e p)

/-- Proves that a statement `∀ args, hypotheses → f args ⦃ post ⦄div` about
`f` is admissible. -/
macro "prove_adm" : tactic =>
  `(tactic| (
      (repeat' (apply Lean.Order.admissible_pi; intro))
      first
        | apply WP.dspec_func_admissible
        | apply dspec_admissible2
        | apply dspec_admissible3
        | apply dspec_admissible4
        | apply dspec_admissible5))

end pathos_compiled_checker
