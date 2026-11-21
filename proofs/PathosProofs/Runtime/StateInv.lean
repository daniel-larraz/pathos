module
public import CpcMini.Logos
import all CpcMini.Logos
public import PathosProofs.Util

/-!
# The checker-state invariant: no formula in a state is `Stuck`

Every state the checker builds starts from `CState.nil` and grows only
through logos's push checks, each of which admits a formula only when
`__eo_is_bool_type` of it is `Boolean true`, which is never so for `Stuck`
(`__eo_is_bool_type Stuck = Stuck`). So no object of a reachable state holds
`Stuck` (`StateOK`), and a premise looked up in one (`__eo_state_proven_nth`)
is never `Stuck`. The generated specs take `StateOK` of their state arguments
as a precondition (a handle can stand for a state holding `Stuck`, so this is
not a `Valid`, which comes from handles); the lemmas here, about logos's
definitions alone, discharge it.

Written by hand.
-/

@[expose] public section

namespace pathos_compiled_checker

open Eo

/-- The formula of a state object. -/
def stateObjFormula : CStateObj → Term
  | CStateObj.assume F => F
  | CStateObj.assume_push F => F
  | CStateObj.proven F => F

/-- No object of the state holds `Stuck`. -/
def StateOK : CState → Prop
  | CState.nil => True
  | CState.cons so s => stateObjFormula so ≠ Term.Stuck ∧ StateOK s
  | CState.Stuck => True

/-- The formula of the proof is not `Stuck`. -/
def ProofOK (p : Proof) : Prop := ∀ G, p = Proof.pf G → G ≠ Term.Stuck

theorem StateOK.nil : StateOK CState.nil := trivial

theorem StateOK.stuck : StateOK CState.Stuck := trivial

theorem StateOK.tail {so : CStateObj} {s : CState} (h : StateOK (CState.cons so s)) : StateOK s :=
  h.2

theorem ProofOK.pf {G : Term} (h : G ≠ Term.Stuck) : ProofOK (Proof.pf G) := by
  intro G' he; cases he; exact h

/-- A premise looked up in an OK state is not `Stuck`. -/
theorem state_proven_nth_ne_stuck {S : CState} (h : StateOK S) (n : SmtEval.native_Int) :
    __eo_state_proven_nth S n ≠ Term.Stuck := by
  induction S generalizing n with
  | nil => simp [__eo_state_proven_nth]
  | Stuck => simp [__eo_state_proven_nth]
  | cons so s ih =>
    obtain ⟨hso, hs⟩ := h
    have ih' := fun n => ih hs n
    cases so <;> unfold __eo_state_proven_nth <;> split <;>
      (try (rename_i heq; obtain ⟨rfl, rfl⟩ := heq)) <;>
      simp_all [__eo_StateObj_proven, stateObjFormula]

/-- `state_proven_nth_ne_stuck`, of the premise a fact `h` speaks of (a
handle's, in the generated proofs): the state and the index are `h`'s. -/
theorem state_proven_nth_ne_stuck_of {α : Sort _} {R : α → Term → Prop} {a : α}
    {S : CState} {n : SmtEval.native_Int} (_h : R a (__eo_state_proven_nth S n))
    (hS : StateOK S) : __eo_state_proven_nth S n ≠ Term.Stuck :=
  state_proven_nth_ne_stuck hS n

/-- `__eo_is_bool_type` is `Boolean true` only on a term that is not `Stuck`. -/
theorem ne_stuck_of_is_bool_type {F : Term} (h : __eo_is_bool_type F = Term.Boolean true) :
    F ≠ Term.Stuck := by
  intro hF; subst hF; simp [__eo_is_bool_type] at h

/-- The guard of an assumption is `Boolean true` only on a term that is not `Stuck`. -/
theorem ne_stuck_of_guard {F X : Term}
    (h : __eo_and (__eo_is_bool_type F) X = Term.Boolean true) : F ≠ Term.Stuck := by
  intro hF; subst hF; simp [__eo_is_bool_type, __eo_and] at h

theorem StateOK.push_assume_check_of {b F : Term} {S : CState} (h : StateOK S)
    (hb : b = Term.Boolean true → F ≠ Term.Stuck) : StateOK (__eo_push_assume_check b F S) := by
  unfold __eo_push_assume_check
  split
  · exact ⟨hb rfl, h⟩
  · exact StateOK.stuck

theorem StateOK.push_input_assume_check_of {b F : Term} {S : CState} (h : StateOK S)
    (hb : b = Term.Boolean true → F ≠ Term.Stuck) :
    StateOK (__eo_push_input_assume_check b F S) := by
  unfold __eo_push_input_assume_check
  split
  · exact ⟨hb rfl, h⟩
  · exact StateOK.stuck

theorem StateOK.push_proven_check_of {b F : Term} {S : CState} (h : StateOK S)
    (hb : b = Term.Boolean true → F ≠ Term.Stuck) : StateOK (__eo_push_proven_check b F S) := by
  unfold __eo_push_proven_check
  split
  · exact ⟨hb rfl, h⟩
  · exact StateOK.stuck

theorem StateOK.push_assume_check {F : Term} {S : CState} (h : StateOK S) :
    StateOK (__eo_push_assume_check (__eo_and (__eo_is_bool_type F) (__eo_is_closed F)) F S) :=
  StateOK.push_assume_check_of h ne_stuck_of_guard

theorem StateOK.push_input_assume_check {F : Term} {S : CState} (h : StateOK S) :
    StateOK (__eo_push_input_assume_check (__eo_and (__eo_is_bool_type F) (__eo_is_closed F)) F S) :=
  StateOK.push_input_assume_check_of h ne_stuck_of_guard

theorem StateOK.push_proven {F : Term} {S : CState} (h : StateOK S) :
    StateOK (__eo_push_proven F S) :=
  StateOK.push_proven_check_of h ne_stuck_of_is_bool_type

theorem StateOK.invoke_cmd_check_proven {S : CState} (h : StateOK S) (proven : Term) :
    StateOK (__eo_invoke_cmd_check_proven S proven) := by
  unfold __eo_invoke_cmd_check_proven
  split
  · rename_i F S'
    obtain ⟨hF, hS'⟩ := h
    exact StateOK.push_proven_check_of hS' (fun _ => hF)
  · exact StateOK.stuck

theorem StateOK.invoke_cmd_step_pop (s : CState) {s2 : CState} (h2 : StateOK s2)
    (r : CRule) (args : CArgList) (premises : CIndexList) :
    StateOK (__eo_invoke_cmd_step_pop s s2 r args premises) := by
  induction s2 with
  | nil => simp [__eo_invoke_cmd_step_pop, StateOK]
  | Stuck => simp [__eo_invoke_cmd_step_pop, StateOK]
  | cons so s2' ih =>
    cases so with
    | assume_push A => simp only [__eo_invoke_cmd_step_pop]; exact StateOK.push_proven h2.2
    | assume F => simp only [__eo_invoke_cmd_step_pop]; exact ih h2.2
    | proven F => simp only [__eo_invoke_cmd_step_pop]; exact ih h2.2

theorem StateOK.invoke_cmd {S : CState} (h : StateOK S) (c : CCmd) :
    StateOK (__eo_invoke_cmd S c) := by
  unfold __eo_invoke_cmd
  split
  · exact StateOK.stuck
  · exact StateOK.push_assume_check h
  · exact StateOK.invoke_cmd_check_proven h _
  · exact StateOK.push_proven h
  · exact StateOK.invoke_cmd_step_pop _ h _ _ _

theorem StateOK.invoke_cmd_list {S : CState} (h : StateOK S) (cs : CCmdList) :
    StateOK (__eo_invoke_cmd_list S cs) := by
  induction cs generalizing S with
  | nil => simpa [__eo_invoke_cmd_list] using h
  | cons c cs ih => simpa [__eo_invoke_cmd_list] using ih (StateOK.invoke_cmd h c)

theorem StateOK.invoke_assume_list {S : CState} (h : StateOK S) (xs : CArgList) :
    StateOK (__eo_invoke_assume_list S xs) := by
  induction xs with
  | nil => simpa [__eo_invoke_assume_list] using h
  | cons F xs ih => simpa [__eo_invoke_assume_list] using StateOK.push_input_assume_check ih

end pathos_compiled_checker
