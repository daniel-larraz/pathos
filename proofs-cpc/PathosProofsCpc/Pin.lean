module
public import CpcChecker
public import Cpc.Logos
import all Cpc.Logos
public import Cpc.SmtEval
import all Cpc.SmtEval
public import PathosProofs.Tactic

/-!
# A requirement that pins a variable to constants (CPC only)

`(eo::requires (eo::or (eo::eq f c1) ... (eo::eq f ck)) true r)`: where
the requirement holds, `f` is one of the constants. The generated proof
splits on which (`pin_split`), and proves `r` once for each constant, so
that the list operators of `f` in `r` are constants there.
-/

@[expose] public section

namespace pathos_compiled_checker

/-- An `eo::or` that is true: one of its sides is. -/
theorem pin_or {a b : Eo.Term} (h : Eo.__eo_or a b = Eo.Term.Boolean true) :
    a = Eo.Term.Boolean true ∨ b = Eo.Term.Boolean true := by
  unfold Eo.__eo_or at h
  split at h
  · rename_i b1 b2
    simp only [SmtEval.native_or, Eo.Term.Boolean.injEq, Bool.or_eq_true] at h
    rcases h with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · simp only [Eo.__eo_requires, SmtEval.native_ite] at h
    split at h
    · split at h <;> cases h
    · cases h
  · cases h

/-- An `eo::eq` that is true: its sides are equal. -/
theorem pin_eq {x c : Eo.Term} (h : Eo.__eo_eq x c = Eo.Term.Boolean true) : x = c := by
  unfold Eo.__eo_eq at h
  split at h
  · cases h
  · cases h
  · simp only [Eo.Term.Boolean.injEq, Eo.native_teq, decide_eq_true_eq] at h
    exact h.symm

/-- Splits a true `eo::or` of `eo::eq`s of a variable and constants into
one goal for each constant, with the variable replaced by it, left to
right. Each step checks the hypothesis's shape first and clears what it
used, so the loop ends. -/
syntax "pin_split " ident : tactic
macro_rules
  | `(tactic| pin_split $h) =>
    `(tactic| repeat' (first
        | (guard_hyp $h :~ Eo.__eo_or _ _ = _; have hp := pin_or $h; clear $h; rcases hp with $h | $h)
        | (guard_hyp $h :~ Eo.__eo_eq _ _ = _; have hp := pin_eq $h; clear $h; subst hp)))

/-- An argument that every call passes one of the constants `cs`
(`[pinned]` in proofgen.toml): the hypothesis its spec takes. -/
def Pinned (cs : List Eo.Term) (x : Eo.Term) : Prop := x ∈ cs

end pathos_compiled_checker
