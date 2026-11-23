module
public import $PROOFS$.Head
public import $CHECKER$
public import $CALC$.Logos
import all $CALC$.Logos
public import $CALC$.SmtTranslate
import all $CALC$.SmtTranslate
public import $CALC$.SmtModel
import all $CALC$.SmtModel
public import $CASES$
import all $CASES$
public import PathosProofs.Generated

/-!
# The proofs about the generated functions

Written by Ethos's rust-meta with the functions: for each program, that its
Rust computes what logos's function of the same name does. Do not edit.
-/

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option maxRecDepth 8000

@[expose] public section

namespace pathos_compiled_checker

open Aeneas Aeneas.Std Result
open Eo hiding Term
open Smtm
open generated generated.part0 generated.part1 generated.part2 generated.part3 generated.part4 generated.part5 generated.part6 generated.part7 generated.part8 generated.part9 generated.part10 generated.part11 generated.part12

theorem case_0_eo__24eo_5fprog_5fite_2dfalse_2dcond_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fite_2dfalse_2dcond s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_ite_false_cond.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_ite_false_cond.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fite_2dfalse_2dcond
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_ite.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  store_step with Store.literal_boolean_spec s2 false hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1
  store_step with Store.apply_rep s3 v1 v2 _ _ hinv3 h64 h_v1 h_v2 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v3 a0 _ _ hinv4 h64 h_v3 h_a0 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3
  store_step with Store.apply_rep s5 v4 a1 _ _ hinv5 h64 h_v4 h_a1 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4
  store_step with Store.apply_rep s6 v0 v5 _ _ hinv6 h64 h_v0 h_v5 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with Store.apply_rep s7 v6 a1 _ _ hinv7 h64 h_v6 h_a1 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  case_done hinv8 hG with h_v7 in EoCases.__eo_prog_ite_false_cond.case_0 using hn_a0 hn_a1

/-- logos's `__eo_prog_ite_false_cond` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fite_2dfalse_2dcond.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_ite_false_cond x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_ite_false_cond.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_ite_false_cond
  unfold EoCases.__eo_prog_ite_false_cond.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fite_2dfalse_2dcond_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5fite_2dfalse_2dcond s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_ite_false_cond x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fite_2dfalse_2dcond.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5fite_2dfalse_2dcond
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fite_2dfalse_2dcond_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_ite_false_cond.case_0

theorem eo__24eo_5fprog_5fite_2dfalse_2dcond_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fite_2dfalse_2dcond.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5fite_2dfalse_2dcond
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fite_2dfalse_2dcond s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_ite_false_cond x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fite_2dfalse_2dcond_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fite_2dneg_2dbranch_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fite_2dneg_2dbranch s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_ite_neg_branch.case_0 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_ite_neg_branch.case_0 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fite_2dneg_2dbranch more_0_eo__24eo_5fprog_5fite_2dneg_2dbranch
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a3 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_ite_neg_branch.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_ite_neg_branch.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_ite_neg_branch.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_ite_neg_branch.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_ite_neg_branch.case_0
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo_not.construct s1 e_v12 (by rw [he_v12]; exact empty_args) hinv1 h64 as ⟨v12, s2, hinv2, h_v12⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11
  pat_same v10 v12 with h_v10 h_v12 using hinv2 else hinv2 hG in EoCases.__eo_prog_ite_neg_branch.case_0
  pat_same v11 a2 with h_v11 h_a2 using hinv2 else hinv2 hG in EoCases.__eo_prog_ite_neg_branch.case_0
  pat_same v4 a1 with h_v4 h_a1 using hinv2 else hinv2 hG in EoCases.__eo_prog_ite_neg_branch.case_0
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo__3d.construct s2 e_v13 (by rw [he_v13]; exact empty_args) hinv2 h64 as ⟨v13, s3, hinv3, h_v13⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo_ite.construct s3 e_v14 (by rw [he_v14]; exact empty_args) hinv3 h64 as ⟨v14, s4, hinv4, h_v14⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13
  store_step with Store.apply_rep s4 v14 a0 _ _ hinv4 h64 h_v14 h_a0 (by ns_tac) (by ns_tac) as ⟨v15, s5, hinv5, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14
  store_step with Store.apply_rep s5 v15 a1 _ _ hinv5 h64 h_v15 h_a1 (by ns_tac) (by ns_tac) as ⟨v16, s6, hinv6, h_v16⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15
  store_step with Store.apply_rep s6 v16 a2 _ _ hinv6 h64 h_v16 h_a2 (by ns_tac) (by ns_tac) as ⟨v17, s7, hinv7, h_v17⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16
  store_step with Store.apply_rep s7 v13 v17 _ _ hinv7 h64 h_v13 h_v17 (by ns_tac) (by ns_tac) as ⟨v18, s8, hinv8, h_v18⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17
  step as ⟨e_v19, he_v19⟩
  store_step with CtorSpec.eo__3d.construct s8 e_v19 (by rw [he_v19]; exact empty_args) hinv8 h64 as ⟨v19, s9, hinv9, h_v19⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18
  store_step with Store.apply_rep s9 v19 a0 _ _ hinv9 h64 h_v19 h_a0 (by ns_tac) (by ns_tac) as ⟨v20, s10, hinv10, h_v20⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19
  store_step with Store.apply_rep s10 v20 a1 _ _ hinv10 h64 h_v20 h_a1 (by ns_tac) (by ns_tac) as ⟨v21, s11, hinv11, h_v21⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20
  store_step with Store.apply_rep s11 v18 v21 _ _ hinv11 h64 h_v18 h_v21 (by ns_tac) (by ns_tac) as ⟨v22, s12, hinv12, h_v22⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21
  case_done hinv12 hG with h_v22 in EoCases.__eo_prog_ite_neg_branch.case_0 using hn_a0 hn_a1 hn_a2 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11

/-- logos's `__eo_prog_ite_neg_branch` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fite_2dneg_2dbranch.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) :
    __eo_prog_ite_neg_branch x_a0 x_a1 x_a2 x_a3 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_ite_neg_branch.case_0 x_a0 x_a1 x_a2 x_a3] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_ite_neg_branch
  unfold EoCases.__eo_prog_ite_neg_branch.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fite_2dneg_2dbranch_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) :
    body_eo__24eo_5fprog_5fite_2dneg_2dbranch s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_ite_neg_branch x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fite_2dneg_2dbranch.rust_eq x_a0 x_a1 x_a2 x_a3 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3)]
  unfold body_eo__24eo_5fprog_5fite_2dneg_2dbranch
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fite_2dneg_2dbranch_spec n ih s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 using hn_a0 hn_a1 hn_a2
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hc0 in EoCases.__eo_prog_ite_neg_branch.case_0

theorem eo__24eo_5fprog_5fite_2dneg_2dbranch_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fite_2dneg_2dbranch.Spec n := by
  intro s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3
  unfold eo__24eo_5fprog_5fite_2dneg_2dbranch
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fite_2dneg_2dbranch s1 a0 a1 a2 a3) (fun s' t => Represents.rep s' t (__eo_prog_ite_neg_branch x_a0 x_a1 x_a2 x_a3))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fite_2dneg_2dbranch_spec m (ih m hm) s1 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fite_2dnot_2dcond_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fite_2dnot_2dcond s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_ite_not_cond.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_ite_not_cond.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fite_2dnot_2dcond more_0_eo__24eo_5fprog_5fite_2dnot_2dcond
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_ite.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo_not.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a0 _ _ hinv3 h64 h_v2 h_a0 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v1 v3 _ _ hinv4 h64 h_v1 h_v3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3
  store_step with Store.apply_rep s5 v4 a1 _ _ hinv5 h64 h_v4 h_a1 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4
  store_step with Store.apply_rep s6 v5 a2 _ _ hinv6 h64 h_v5 h_a2 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with Store.apply_rep s7 v0 v6 _ _ hinv7 h64 h_v0 h_v6 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo_ite.construct s8 e_v8 (by rw [he_v8]; exact empty_args) hinv8 h64 as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  store_step with Store.apply_rep s9 v8 a0 _ _ hinv9 h64 h_v8 h_a0 (by ns_tac) (by ns_tac) as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
  store_step with Store.apply_rep s10 v9 a2 _ _ hinv10 h64 h_v9 h_a2 (by ns_tac) (by ns_tac) as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  store_step with Store.apply_rep s11 v10 a1 _ _ hinv11 h64 h_v10 h_a1 (by ns_tac) (by ns_tac) as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
  store_step with Store.apply_rep s12 v7 v11 _ _ hinv12 h64 h_v7 h_v11 (by ns_tac) (by ns_tac) as ⟨v12, s13, hinv13, h_v12⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11
  case_done hinv13 hG with h_v12 in EoCases.__eo_prog_ite_not_cond.case_0 using hn_a0 hn_a1 hn_a2

/-- logos's `__eo_prog_ite_not_cond` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fite_2dnot_2dcond.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __eo_prog_ite_not_cond x_a0 x_a1 x_a2 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_ite_not_cond.case_0 x_a0 x_a1 x_a2] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_ite_not_cond
  unfold EoCases.__eo_prog_ite_not_cond.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fite_2dnot_2dcond_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24eo_5fprog_5fite_2dnot_2dcond s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_ite_not_cond x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fite_2dnot_2dcond.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24eo_5fprog_5fite_2dnot_2dcond
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fite_2dnot_2dcond_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1 hn_a2
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hc0 in EoCases.__eo_prog_ite_not_cond.case_0

theorem eo__24eo_5fprog_5fite_2dnot_2dcond_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fite_2dnot_2dcond.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24eo_5fprog_5fite_2dnot_2dcond
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fite_2dnot_2dcond s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__eo_prog_ite_not_cond x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fite_2dnot_2dcond_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fite_2dthen_2dfalse_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fite_2dthen_2dfalse s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_ite_then_false.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_ite_then_false.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fite_2dthen_2dfalse more_0_eo__24eo_5fprog_5fite_2dthen_2dfalse
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_ite.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1
  store_step with Store.literal_boolean_spec s3 false hinv3 h64 as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v2 v3 _ _ hinv4 h64 h_v2 h_v3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3
  store_step with Store.apply_rep s5 v4 a1 _ _ hinv5 h64 h_v4 h_a1 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4
  store_step with Store.apply_rep s6 v0 v5 _ _ hinv6 h64 h_v0 h_v5 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo_and.construct s7 e_v7 (by rw [he_v7]; exact empty_args) hinv7 h64 as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo_not.construct s8 e_v8 (by rw [he_v8]; exact empty_args) hinv8 h64 as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  store_step with Store.apply_rep s9 v8 a0 _ _ hinv9 h64 h_v8 h_a0 (by ns_tac) (by ns_tac) as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
  store_step with Store.apply_rep s10 v7 v9 _ _ hinv10 h64 h_v7 h_v9 (by ns_tac) (by ns_tac) as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  step as ⟨e_v11, he_v11⟩
  store_step with CtorSpec.eo_and.construct s11 e_v11 (by rw [he_v11]; exact empty_args) hinv11 h64 as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
  store_step with Store.apply_rep s12 v11 a1 _ _ hinv12 h64 h_v11 h_a1 (by ns_tac) (by ns_tac) as ⟨v12, s13, hinv13, h_v12⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11
  store_step with Store.literal_boolean_spec s13 true hinv13 h64 as ⟨v13, s14, hinv14, h_v13⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
  store_step with Store.apply_rep s14 v12 v13 _ _ hinv14 h64 h_v12 h_v13 (by ns_tac) (by ns_tac) as ⟨v14, s15, hinv15, h_v14⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13
  store_step with Store.apply_rep s15 v10 v14 _ _ hinv15 h64 h_v10 h_v14 (by ns_tac) (by ns_tac) as ⟨v15, s16, hinv16, h_v15⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14
  store_step with Store.apply_rep s16 v6 v15 _ _ hinv16 h64 h_v6 h_v15 (by ns_tac) (by ns_tac) as ⟨v16, s17, hinv17, h_v16⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15
  case_done hinv17 hG with h_v16 in EoCases.__eo_prog_ite_then_false.case_0 using hn_a0 hn_a1

/-- logos's `__eo_prog_ite_then_false` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fite_2dthen_2dfalse.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_ite_then_false x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_ite_then_false.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_ite_then_false
  unfold EoCases.__eo_prog_ite_then_false.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fite_2dthen_2dfalse_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5fite_2dthen_2dfalse s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_ite_then_false x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fite_2dthen_2dfalse.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5fite_2dthen_2dfalse
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fite_2dthen_2dfalse_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_ite_then_false.case_0

theorem eo__24eo_5fprog_5fite_2dthen_2dfalse_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fite_2dthen_2dfalse.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5fite_2dthen_2dfalse
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fite_2dthen_2dfalse s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_ite_then_false x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fite_2dthen_2dfalse_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fite_2dthen_2dlookahead_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fite_2dthen_2dlookahead s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_ite_then_lookahead.case_0 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_ite_then_lookahead.case_0 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fite_2dthen_2dlookahead more_0_eo__24eo_5fprog_5fite_2dthen_2dlookahead
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_ite.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_ite.construct s3 e_v3 (by rw [he_v3]; exact empty_args) hinv3 h64 as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v3 a0 _ _ hinv4 h64 h_v3 h_a0 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3
  store_step with Store.apply_rep s5 v4 a1 _ _ hinv5 h64 h_v4 h_a1 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4
  store_step with Store.apply_rep s6 v5 a2 _ _ hinv6 h64 h_v5 h_a2 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with Store.apply_rep s7 v2 v6 _ _ hinv7 h64 h_v2 h_v6 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  store_step with Store.apply_rep s8 v7 a3 _ _ hinv8 h64 h_v7 h_a3 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  store_step with Store.apply_rep s9 v0 v8 _ _ hinv9 h64 h_v0 h_v8 (by ns_tac) (by ns_tac) as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo_ite.construct s10 e_v10 (by rw [he_v10]; exact empty_args) hinv10 h64 as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  store_step with Store.apply_rep s11 v10 a0 _ _ hinv11 h64 h_v10 h_a0 (by ns_tac) (by ns_tac) as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
  store_step with Store.apply_rep s12 v11 a1 _ _ hinv12 h64 h_v11 h_a1 (by ns_tac) (by ns_tac) as ⟨v12, s13, hinv13, h_v12⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11
  store_step with Store.apply_rep s13 v12 a3 _ _ hinv13 h64 h_v12 h_a3 (by ns_tac) (by ns_tac) as ⟨v13, s14, hinv14, h_v13⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
  store_step with Store.apply_rep s14 v9 v13 _ _ hinv14 h64 h_v9 h_v13 (by ns_tac) (by ns_tac) as ⟨v14, s15, hinv15, h_v14⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13
  case_done hinv15 hG with h_v14 in EoCases.__eo_prog_ite_then_lookahead.case_0 using hn_a0 hn_a1 hn_a2 hn_a3

/-- logos's `__eo_prog_ite_then_lookahead` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fite_2dthen_2dlookahead.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) :
    __eo_prog_ite_then_lookahead x_a0 x_a1 x_a2 x_a3 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_ite_then_lookahead.case_0 x_a0 x_a1 x_a2 x_a3] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_ite_then_lookahead
  unfold EoCases.__eo_prog_ite_then_lookahead.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fite_2dthen_2dlookahead_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) :
    body_eo__24eo_5fprog_5fite_2dthen_2dlookahead s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_ite_then_lookahead x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fite_2dthen_2dlookahead.rust_eq x_a0 x_a1 x_a2 x_a3 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3)]
  unfold body_eo__24eo_5fprog_5fite_2dthen_2dlookahead
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  stuck_check h_a3 : x_a3 as hn_a3 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fite_2dthen_2dlookahead_spec n ih s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2 hn_a3
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 using hn_a0 hn_a1 hn_a2 hn_a3
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hn_a3 hc0 in EoCases.__eo_prog_ite_then_lookahead.case_0

theorem eo__24eo_5fprog_5fite_2dthen_2dlookahead_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fite_2dthen_2dlookahead.Spec n := by
  intro s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3
  unfold eo__24eo_5fprog_5fite_2dthen_2dlookahead
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fite_2dthen_2dlookahead s1 a0 a1 a2 a3) (fun s' t => Represents.rep s' t (__eo_prog_ite_then_lookahead x_a0 x_a1 x_a2 x_a3))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fite_2dthen_2dlookahead_spec m (ih m hm) s1 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fite_2dthen_2dlookahead_2dnot_2dself_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fite_2dthen_2dlookahead_2dnot_2dself s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_ite_then_lookahead_not_self.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_ite_then_lookahead_not_self.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fite_2dthen_2dlookahead_2dnot_2dself more_0_eo__24eo_5fprog_5fite_2dthen_2dlookahead_2dnot_2dself
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_ite.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_not.construct s3 e_v3 (by rw [he_v3]; exact empty_args) hinv3 h64 as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v3 a0 _ _ hinv4 h64 h_v3 h_a0 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3
  store_step with Store.apply_rep s5 v2 v4 _ _ hinv5 h64 h_v2 h_v4 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4
  store_step with Store.apply_rep s6 v5 a1 _ _ hinv6 h64 h_v5 h_a1 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with Store.apply_rep s7 v0 v6 _ _ hinv7 h64 h_v0 h_v6 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo_ite.construct s8 e_v8 (by rw [he_v8]; exact empty_args) hinv8 h64 as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  store_step with Store.apply_rep s9 v8 a0 _ _ hinv9 h64 h_v8 h_a0 (by ns_tac) (by ns_tac) as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
  store_step with Store.literal_boolean_spec s10 false hinv10 h64 as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  store_step with Store.apply_rep s11 v9 v10 _ _ hinv11 h64 h_v9 h_v10 (by ns_tac) (by ns_tac) as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
  store_step with Store.apply_rep s12 v11 a1 _ _ hinv12 h64 h_v11 h_a1 (by ns_tac) (by ns_tac) as ⟨v12, s13, hinv13, h_v12⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11
  store_step with Store.apply_rep s13 v7 v12 _ _ hinv13 h64 h_v7 h_v12 (by ns_tac) (by ns_tac) as ⟨v13, s14, hinv14, h_v13⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
  case_done hinv14 hG with h_v13 in EoCases.__eo_prog_ite_then_lookahead_not_self.case_0 using hn_a0 hn_a1

/-- logos's `__eo_prog_ite_then_lookahead_not_self` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fite_2dthen_2dlookahead_2dnot_2dself.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_ite_then_lookahead_not_self x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_ite_then_lookahead_not_self.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_ite_then_lookahead_not_self
  unfold EoCases.__eo_prog_ite_then_lookahead_not_self.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fite_2dthen_2dlookahead_2dnot_2dself_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5fite_2dthen_2dlookahead_2dnot_2dself s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_ite_then_lookahead_not_self x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fite_2dthen_2dlookahead_2dnot_2dself.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5fite_2dthen_2dlookahead_2dnot_2dself
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fite_2dthen_2dlookahead_2dnot_2dself_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_ite_then_lookahead_not_self.case_0

theorem eo__24eo_5fprog_5fite_2dthen_2dlookahead_2dnot_2dself_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fite_2dthen_2dlookahead_2dnot_2dself.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5fite_2dthen_2dlookahead_2dnot_2dself
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fite_2dthen_2dlookahead_2dnot_2dself s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_ite_then_lookahead_not_self x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fite_2dthen_2dlookahead_2dnot_2dself_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fite_2dthen_2dlookahead_2dself_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fite_2dthen_2dlookahead_2dself s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_ite_then_lookahead_self.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_ite_then_lookahead_self.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fite_2dthen_2dlookahead_2dself
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_ite.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a0 _ _ hinv3 h64 h_v2 h_a0 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v3 a1 _ _ hinv4 h64 h_v3 h_a1 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3
  store_step with Store.apply_rep s5 v0 v4 _ _ hinv5 h64 h_v0 h_v4 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_ite.construct s6 e_v6 (by rw [he_v6]; exact empty_args) hinv6 h64 as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with Store.apply_rep s7 v6 a0 _ _ hinv7 h64 h_v6 h_a0 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  store_step with Store.literal_boolean_spec s8 true hinv8 h64 as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  store_step with Store.apply_rep s9 v7 v8 _ _ hinv9 h64 h_v7 h_v8 (by ns_tac) (by ns_tac) as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
  store_step with Store.apply_rep s10 v9 a1 _ _ hinv10 h64 h_v9 h_a1 (by ns_tac) (by ns_tac) as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  store_step with Store.apply_rep s11 v5 v10 _ _ hinv11 h64 h_v5 h_v10 (by ns_tac) (by ns_tac) as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
  case_done hinv12 hG with h_v11 in EoCases.__eo_prog_ite_then_lookahead_self.case_0 using hn_a0 hn_a1

/-- logos's `__eo_prog_ite_then_lookahead_self` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fite_2dthen_2dlookahead_2dself.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_ite_then_lookahead_self x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_ite_then_lookahead_self.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_ite_then_lookahead_self
  unfold EoCases.__eo_prog_ite_then_lookahead_self.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fite_2dthen_2dlookahead_2dself_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5fite_2dthen_2dlookahead_2dself s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_ite_then_lookahead_self x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fite_2dthen_2dlookahead_2dself.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5fite_2dthen_2dlookahead_2dself
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fite_2dthen_2dlookahead_2dself_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_ite_then_lookahead_self.case_0

theorem eo__24eo_5fprog_5fite_2dthen_2dlookahead_2dself_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fite_2dthen_2dlookahead_2dself.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5fite_2dthen_2dlookahead_2dself
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fite_2dthen_2dlookahead_2dself s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_ite_then_lookahead_self x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fite_2dthen_2dlookahead_2dself_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fite_2dthen_2dneg_2dlookahead_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fite_2dthen_2dneg_2dlookahead s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_ite_then_neg_lookahead.case_0 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_ite_then_neg_lookahead.case_0 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fite_2dthen_2dneg_2dlookahead more_0_eo__24eo_5fprog_5fite_2dthen_2dneg_2dlookahead
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_ite.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_ite.construct s3 e_v3 (by rw [he_v3]; exact empty_args) hinv3 h64 as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo_not.construct s4 e_v4 (by rw [he_v4]; exact empty_args) hinv4 h64 as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3
  store_step with Store.apply_rep s5 v4 a0 _ _ hinv5 h64 h_v4 h_a0 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4
  store_step with Store.apply_rep s6 v3 v5 _ _ hinv6 h64 h_v3 h_v5 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with Store.apply_rep s7 v6 a1 _ _ hinv7 h64 h_v6 h_a1 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  store_step with Store.apply_rep s8 v7 a2 _ _ hinv8 h64 h_v7 h_a2 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  store_step with Store.apply_rep s9 v2 v8 _ _ hinv9 h64 h_v2 h_v8 (by ns_tac) (by ns_tac) as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
  store_step with Store.apply_rep s10 v9 a3 _ _ hinv10 h64 h_v9 h_a3 (by ns_tac) (by ns_tac) as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  store_step with Store.apply_rep s11 v0 v10 _ _ hinv11 h64 h_v0 h_v10 (by ns_tac) (by ns_tac) as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo_ite.construct s12 e_v12 (by rw [he_v12]; exact empty_args) hinv12 h64 as ⟨v12, s13, hinv13, h_v12⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11
  store_step with Store.apply_rep s13 v12 a0 _ _ hinv13 h64 h_v12 h_a0 (by ns_tac) (by ns_tac) as ⟨v13, s14, hinv14, h_v13⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
  store_step with Store.apply_rep s14 v13 a2 _ _ hinv14 h64 h_v13 h_a2 (by ns_tac) (by ns_tac) as ⟨v14, s15, hinv15, h_v14⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13
  store_step with Store.apply_rep s15 v14 a3 _ _ hinv15 h64 h_v14 h_a3 (by ns_tac) (by ns_tac) as ⟨v15, s16, hinv16, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14
  store_step with Store.apply_rep s16 v11 v15 _ _ hinv16 h64 h_v11 h_v15 (by ns_tac) (by ns_tac) as ⟨v16, s17, hinv17, h_v16⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15
  case_done hinv17 hG with h_v16 in EoCases.__eo_prog_ite_then_neg_lookahead.case_0 using hn_a0 hn_a1 hn_a2 hn_a3

/-- logos's `__eo_prog_ite_then_neg_lookahead` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fite_2dthen_2dneg_2dlookahead.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) :
    __eo_prog_ite_then_neg_lookahead x_a0 x_a1 x_a2 x_a3 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_ite_then_neg_lookahead.case_0 x_a0 x_a1 x_a2 x_a3] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_ite_then_neg_lookahead
  unfold EoCases.__eo_prog_ite_then_neg_lookahead.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fite_2dthen_2dneg_2dlookahead_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) :
    body_eo__24eo_5fprog_5fite_2dthen_2dneg_2dlookahead s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_ite_then_neg_lookahead x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fite_2dthen_2dneg_2dlookahead.rust_eq x_a0 x_a1 x_a2 x_a3 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3)]
  unfold body_eo__24eo_5fprog_5fite_2dthen_2dneg_2dlookahead
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  stuck_check h_a3 : x_a3 as hn_a3 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fite_2dthen_2dneg_2dlookahead_spec n ih s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2 hn_a3
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 using hn_a0 hn_a1 hn_a2 hn_a3
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hn_a3 hc0 in EoCases.__eo_prog_ite_then_neg_lookahead.case_0

theorem eo__24eo_5fprog_5fite_2dthen_2dneg_2dlookahead_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fite_2dthen_2dneg_2dlookahead.Spec n := by
  intro s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3
  unfold eo__24eo_5fprog_5fite_2dthen_2dneg_2dlookahead
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fite_2dthen_2dneg_2dlookahead s1 a0 a1 a2 a3) (fun s' t => Represents.rep s' t (__eo_prog_ite_then_neg_lookahead x_a0 x_a1 x_a2 x_a3))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fite_2dthen_2dneg_2dlookahead_spec m (ih m hm) s1 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fite_2dthen_2dtrue_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fite_2dthen_2dtrue s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_ite_then_true.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_ite_then_true.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fite_2dthen_2dtrue more_0_eo__24eo_5fprog_5fite_2dthen_2dtrue
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_ite.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1
  store_step with Store.literal_boolean_spec s3 true hinv3 h64 as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v2 v3 _ _ hinv4 h64 h_v2 h_v3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3
  store_step with Store.apply_rep s5 v4 a1 _ _ hinv5 h64 h_v4 h_a1 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4
  store_step with Store.apply_rep s6 v0 v5 _ _ hinv6 h64 h_v0 h_v5 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo_or.construct s7 e_v7 (by rw [he_v7]; exact empty_args) hinv7 h64 as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  store_step with Store.apply_rep s8 v7 a0 _ _ hinv8 h64 h_v7 h_a0 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_or.construct s9 e_v9 (by rw [he_v9]; exact empty_args) hinv9 h64 as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
  store_step with Store.apply_rep s10 v9 a1 _ _ hinv10 h64 h_v9 h_a1 (by ns_tac) (by ns_tac) as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  store_step with Store.literal_boolean_spec s11 false hinv11 h64 as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
  store_step with Store.apply_rep s12 v10 v11 _ _ hinv12 h64 h_v10 h_v11 (by ns_tac) (by ns_tac) as ⟨v12, s13, hinv13, h_v12⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11
  store_step with Store.apply_rep s13 v8 v12 _ _ hinv13 h64 h_v8 h_v12 (by ns_tac) (by ns_tac) as ⟨v13, s14, hinv14, h_v13⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
  store_step with Store.apply_rep s14 v6 v13 _ _ hinv14 h64 h_v6 h_v13 (by ns_tac) (by ns_tac) as ⟨v14, s15, hinv15, h_v14⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13
  case_done hinv15 hG with h_v14 in EoCases.__eo_prog_ite_then_true.case_0 using hn_a0 hn_a1

/-- logos's `__eo_prog_ite_then_true` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fite_2dthen_2dtrue.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_ite_then_true x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_ite_then_true.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_ite_then_true
  unfold EoCases.__eo_prog_ite_then_true.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fite_2dthen_2dtrue_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5fite_2dthen_2dtrue s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_ite_then_true x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fite_2dthen_2dtrue.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5fite_2dthen_2dtrue
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fite_2dthen_2dtrue_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_ite_then_true.case_0

theorem eo__24eo_5fprog_5fite_2dthen_2dtrue_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fite_2dthen_2dtrue.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5fite_2dthen_2dtrue
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fite_2dthen_2dtrue s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_ite_then_true x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fite_2dthen_2dtrue_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fite_2dtrue_2dcond_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fite_2dtrue_2dcond s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_ite_true_cond.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_ite_true_cond.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fite_2dtrue_2dcond
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_ite.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  store_step with Store.literal_boolean_spec s2 true hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1
  store_step with Store.apply_rep s3 v1 v2 _ _ hinv3 h64 h_v1 h_v2 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v3 a0 _ _ hinv4 h64 h_v3 h_a0 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3
  store_step with Store.apply_rep s5 v4 a1 _ _ hinv5 h64 h_v4 h_a1 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4
  store_step with Store.apply_rep s6 v0 v5 _ _ hinv6 h64 h_v0 h_v5 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with Store.apply_rep s7 v6 a0 _ _ hinv7 h64 h_v6 h_a0 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  case_done hinv8 hG with h_v7 in EoCases.__eo_prog_ite_true_cond.case_0 using hn_a0 hn_a1

/-- logos's `__eo_prog_ite_true_cond` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fite_2dtrue_2dcond.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_ite_true_cond x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_ite_true_cond.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_ite_true_cond
  unfold EoCases.__eo_prog_ite_true_cond.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fite_2dtrue_2dcond_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5fite_2dtrue_2dcond s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_ite_true_cond x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fite_2dtrue_2dcond.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5fite_2dtrue_2dcond
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fite_2dtrue_2dcond_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_ite_true_cond.case_0

theorem eo__24eo_5fprog_5fite_2dtrue_2dcond_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fite_2dtrue_2dcond.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5fite_2dtrue_2dcond
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fite_2dtrue_2dcond s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_ite_true_cond x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fite_2dtrue_2dcond_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fite_5felim1_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24eo_5fprog_5fite_5felim1 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_ite_elim1.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_ite_elim1.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fite_5felim1 more_0_eo__24eo_5fprog_5fite_5felim1
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_ite_elim1.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_ite_elim1.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_ite_elim1.case_0
  pat_unapply h_v6 as ⟨v9, v10, x_v9, x_v10, h_v9, h_v10, hn_v9, hn_v10⟩ using hinv else hinv hG in EoCases.__eo_prog_ite_elim1.case_0
  step as ⟨e_v11, he_v11⟩
  store_step with CtorSpec.eo_ite.construct s e_v11 (by rw [he_v11]; exact empty_args) hinv h64 as ⟨v11, s1, hinv1, h_v11⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v6 h_v7 h_v9 h_v10
  pat_same v9 v11 with h_v9 h_v11 using hinv1 else hinv1 hG in EoCases.__eo_prog_ite_elim1.case_0
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo_or.construct s1 e_v12 (by rw [he_v12]; exact empty_args) hinv1 h64 as ⟨v12, s2, hinv2, h_v12⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v6 h_v7 h_v9 h_v10 h_v11
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo_not.construct s2 e_v13 (by rw [he_v13]; exact empty_args) hinv2 h64 as ⟨v13, s3, hinv3, h_v13⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v6 h_v7 h_v9 h_v10 h_v11 h_v12
  store_step with Store.apply_rep s3 v13 v10 _ _ hinv3 h64 h_v13 h_v10 (by ns_tac) (by ns_tac) as ⟨v14, s4, hinv4, h_v14⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v6 h_v7 h_v9 h_v10 h_v11 h_v12 h_v13
  store_step with Store.apply_rep s4 v12 v14 _ _ hinv4 h64 h_v12 h_v14 (by ns_tac) (by ns_tac) as ⟨v15, s5, hinv5, h_v15⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v6 h_v7 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14
  step as ⟨e_v16, he_v16⟩
  store_step with CtorSpec.eo_or.construct s5 e_v16 (by rw [he_v16]; exact empty_args) hinv5 h64 as ⟨v16, s6, hinv6, h_v16⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v6 h_v7 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15
  store_step with Store.apply_rep s6 v16 v7 _ _ hinv6 h64 h_v16 h_v7 (by ns_tac) (by ns_tac) as ⟨v17, s7, hinv7, h_v17⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v6 h_v7 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16
  store_step with Store.literal_boolean_spec s7 false hinv7 h64 as ⟨v18, s8, hinv8, h_v18⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v6 h_v7 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17
  store_step with Store.apply_rep s8 v17 v18 _ _ hinv8 h64 h_v17 h_v18 (by ns_tac) (by ns_tac) as ⟨v19, s9, hinv9, h_v19⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v6 h_v7 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18
  store_step with Store.apply_rep s9 v15 v19 _ _ hinv9 h64 h_v15 h_v19 (by ns_tac) (by ns_tac) as ⟨v20, s10, hinv10, h_v20⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v6 h_v7 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19
  case_done hinv10 hG with h_v20 in EoCases.__eo_prog_ite_elim1.case_0 using hn_v3 hn_v4 hn_v6 hn_v7 hn_v9 hn_v10

/-- logos's `__eo_prog_ite_elim1` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fite_5felim1.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_ite_elim1 x_a0 =
      (firstSome [EoCases.__eo_prog_ite_elim1.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_ite_elim1
  unfold EoCases.__eo_prog_ite_elim1.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fite_5felim1_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fite_5felim1 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_ite_elim1 x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fite_5felim1.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fite_5felim1
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fprog_5fite_5felim1_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using
  body_stuck hinv1 hG using hc0 in EoCases.__eo_prog_ite_elim1.case_0

theorem eo__24eo_5fprog_5fite_5felim1_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fite_5felim1.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fite_5felim1
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fite_5felim1 s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_ite_elim1 x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fite_5felim1_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fite_5felim2_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24eo_5fprog_5fite_5felim2 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_ite_elim2.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_ite_elim2.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fite_5felim2 more_0_eo__24eo_5fprog_5fite_5felim2
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_ite_elim2.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_ite_elim2.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_ite_elim2.case_0
  pat_unapply h_v6 as ⟨v9, v10, x_v9, x_v10, h_v9, h_v10, hn_v9, hn_v10⟩ using hinv else hinv hG in EoCases.__eo_prog_ite_elim2.case_0
  step as ⟨e_v11, he_v11⟩
  store_step with CtorSpec.eo_ite.construct s e_v11 (by rw [he_v11]; exact empty_args) hinv h64 as ⟨v11, s1, hinv1, h_v11⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v6 h_v7 h_v9 h_v10
  pat_same v9 v11 with h_v9 h_v11 using hinv1 else hinv1 hG in EoCases.__eo_prog_ite_elim2.case_0
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo_or.construct s1 e_v12 (by rw [he_v12]; exact empty_args) hinv1 h64 as ⟨v12, s2, hinv2, h_v12⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v6 h_v7 h_v9 h_v10 h_v11
  store_step with Store.apply_rep s2 v12 v10 _ _ hinv2 h64 h_v12 h_v10 (by ns_tac) (by ns_tac) as ⟨v13, s3, hinv3, h_v13⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v6 h_v7 h_v9 h_v10 h_v11 h_v12
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo_or.construct s3 e_v14 (by rw [he_v14]; exact empty_args) hinv3 h64 as ⟨v14, s4, hinv4, h_v14⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v6 h_v7 h_v9 h_v10 h_v11 h_v12 h_v13
  store_step with Store.apply_rep s4 v14 v4 _ _ hinv4 h64 h_v14 h_v4 (by ns_tac) (by ns_tac) as ⟨v15, s5, hinv5, h_v15⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v6 h_v7 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14
  store_step with Store.literal_boolean_spec s5 false hinv5 h64 as ⟨v16, s6, hinv6, h_v16⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v6 h_v7 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15
  store_step with Store.apply_rep s6 v15 v16 _ _ hinv6 h64 h_v15 h_v16 (by ns_tac) (by ns_tac) as ⟨v17, s7, hinv7, h_v17⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v6 h_v7 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16
  store_step with Store.apply_rep s7 v13 v17 _ _ hinv7 h64 h_v13 h_v17 (by ns_tac) (by ns_tac) as ⟨v18, s8, hinv8, h_v18⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v6 h_v7 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17
  case_done hinv8 hG with h_v18 in EoCases.__eo_prog_ite_elim2.case_0 using hn_v3 hn_v4 hn_v6 hn_v7 hn_v9 hn_v10

/-- logos's `__eo_prog_ite_elim2` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fite_5felim2.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_ite_elim2 x_a0 =
      (firstSome [EoCases.__eo_prog_ite_elim2.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_ite_elim2
  unfold EoCases.__eo_prog_ite_elim2.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fite_5felim2_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fite_5felim2 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_ite_elim2 x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fite_5felim2.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fite_5felim2
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fprog_5fite_5felim2_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using
  body_stuck hinv1 hG using hc0 in EoCases.__eo_prog_ite_elim2.case_0

theorem eo__24eo_5fprog_5fite_5felim2_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fite_5felim2.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fite_5felim2
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fite_5felim2 s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_ite_elim2 x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fite_5felim2_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fite_5feq_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fite_5feq s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_ite_eq.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_ite_eq.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fite_5feq more_0_eo__24eo_5fprog_5fite_5feq
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_prog_ite_eq.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_prog_ite_eq.case_0
  pat_unapply h_v4 as ⟨v7, v8, x_v7, x_v8, h_v7, h_v8, hn_v7, hn_v8⟩ using hinv else hinv hG in EoCases.__eo_prog_ite_eq.case_0
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_ite.construct s e_v9 (by rw [he_v9]; exact empty_args) hinv h64 as ⟨v9, s1, hinv1, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8
  pat_same v7 v9 with h_v7 h_v9 using hinv1 else hinv1 hG in EoCases.__eo_prog_ite_eq.case_0
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo_ite.construct s1 e_v10 (by rw [he_v10]; exact empty_args) hinv1 h64 as ⟨v10, s2, hinv2, h_v10⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9
  store_step with Store.apply_rep s2 v10 v8 _ _ hinv2 h64 h_v10 h_v8 (by ns_tac) (by ns_tac) as ⟨v11, s3, hinv3, h_v11⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo__3d.construct s3 e_v12 (by rw [he_v12]; exact empty_args) hinv3 h64 as ⟨v12, s4, hinv4, h_v12⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo_ite.construct s4 e_v13 (by rw [he_v13]; exact empty_args) hinv4 h64 as ⟨v13, s5, hinv5, h_v13⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
  store_step with Store.apply_rep s5 v13 v8 _ _ hinv5 h64 h_v13 h_v8 (by ns_tac) (by ns_tac) as ⟨v14, s6, hinv6, h_v14⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13
  store_step with Store.apply_rep s6 v14 v5 _ _ hinv6 h64 h_v14 h_v5 (by ns_tac) (by ns_tac) as ⟨v15, s7, hinv7, h_v15⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14
  store_step with Store.apply_rep s7 v15 v2 _ _ hinv7 h64 h_v15 h_v2 (by ns_tac) (by ns_tac) as ⟨v16, s8, hinv8, h_v16⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15
  store_step with Store.apply_rep s8 v12 v16 _ _ hinv8 h64 h_v12 h_v16 (by ns_tac) (by ns_tac) as ⟨v17, s9, hinv9, h_v17⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16
  store_step with Store.apply_rep s9 v17 v5 _ _ hinv9 h64 h_v17 h_v5 (by ns_tac) (by ns_tac) as ⟨v18, s10, hinv10, h_v18⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17
  store_step with Store.apply_rep s10 v11 v18 _ _ hinv10 h64 h_v11 h_v18 (by ns_tac) (by ns_tac) as ⟨v19, s11, hinv11, h_v19⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18
  step as ⟨e_v20, he_v20⟩
  store_step with CtorSpec.eo__3d.construct s11 e_v20 (by rw [he_v20]; exact empty_args) hinv11 h64 as ⟨v20, s12, hinv12, h_v20⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19
  step as ⟨e_v21, he_v21⟩
  store_step with CtorSpec.eo_ite.construct s12 e_v21 (by rw [he_v21]; exact empty_args) hinv12 h64 as ⟨v21, s13, hinv13, h_v21⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20
  store_step with Store.apply_rep s13 v21 v8 _ _ hinv13 h64 h_v21 h_v8 (by ns_tac) (by ns_tac) as ⟨v22, s14, hinv14, h_v22⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21
  store_step with Store.apply_rep s14 v22 v5 _ _ hinv14 h64 h_v22 h_v5 (by ns_tac) (by ns_tac) as ⟨v23, s15, hinv15, h_v23⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22
  store_step with Store.apply_rep s15 v23 v2 _ _ hinv15 h64 h_v23 h_v2 (by ns_tac) (by ns_tac) as ⟨v24, s16, hinv16, h_v24⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23
  store_step with Store.apply_rep s16 v20 v24 _ _ hinv16 h64 h_v20 h_v24 (by ns_tac) (by ns_tac) as ⟨v25, s17, hinv17, h_v25⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24
  store_step with Store.apply_rep s17 v25 v2 _ _ hinv17 h64 h_v25 h_v2 (by ns_tac) (by ns_tac) as ⟨v26, s18, hinv18, h_v26⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25
  store_step with Store.apply_rep s18 v19 v26 _ _ hinv18 h64 h_v19 h_v26 (by ns_tac) (by ns_tac) as ⟨v27, s19, hinv19, h_v27⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26
  case_done hinv19 hG with h_v27 in EoCases.__eo_prog_ite_eq.case_0 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5 hn_v7 hn_v8

/-- logos's `__eo_prog_ite_eq` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fite_5feq.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_ite_eq x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_ite_eq.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_ite_eq
  unfold EoCases.__eo_prog_ite_eq.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fite_5feq_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fite_5feq s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_ite_eq x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fite_5feq.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fite_5feq
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fite_5feq_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_ite_eq.case_0

theorem eo__24eo_5fprog_5fite_5feq_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fite_5feq.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fite_5feq
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fite_5feq s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_ite_eq x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fite_5feq_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fmodus_5fponens_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_0_eo__24eo_5fprog_5fmodus_5fponens s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_modus_ponens.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_modus_ponens.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fmodus_5fponens
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_modus_ponens.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a1 as ⟨v3, x_v3, h_v3⟩ else hinv hG in EoCases.__eo_prog_modus_ponens.case_0
  pat_unapply h_v3 as ⟨v5, v6, x_v5, x_v6, h_v5, h_v6, hn_v5, hn_v6⟩ using hinv else hinv hG in EoCases.__eo_prog_modus_ponens.case_0
  pat_unapply h_v5 as ⟨v8, v9, x_v8, x_v9, h_v8, h_v9, hn_v8, hn_v9⟩ using hinv else hinv hG in EoCases.__eo_prog_modus_ponens.case_0
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo__3d_3e.construct s e_v10 (by rw [he_v10]; exact empty_args) hinv h64 as ⟨v10, s1, hinv1, h_v10⟩ growing hG carrying h_a0 h_a1 h_v1 h_v3 h_v5 h_v6 h_v8 h_v9
  pat_same v8 v10 with h_v8 h_v10 using hinv1 else hinv1 hG in EoCases.__eo_prog_modus_ponens.case_0
  pat_same v9 v1 with h_v9 h_v1 using hinv1 else hinv1 hG in EoCases.__eo_prog_modus_ponens.case_0
  case_done hinv1 hG with h_v6 in EoCases.__eo_prog_modus_ponens.case_0 using hn_v5 hn_v6 hn_v8 hn_v9

/-- logos's `__eo_prog_modus_ponens` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fmodus_5fponens.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_modus_ponens x_a0 x_a1 =
      (firstSome [EoCases.__eo_prog_modus_ponens.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_modus_ponens
  unfold EoCases.__eo_prog_modus_ponens.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fmodus_5fponens_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5fmodus_5fponens s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_modus_ponens x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fmodus_5fponens.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5fmodus_5fponens
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fprog_5fmodus_5fponens_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using
  body_stuck hinv1 hG using hc0 in EoCases.__eo_prog_modus_ponens.case_0

theorem eo__24eo_5fprog_5fmodus_5fponens_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fmodus_5fponens.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5fmodus_5fponens
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fmodus_5fponens s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_modus_ponens x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fmodus_5fponens_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fnary_5fcong_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fnary_5fcong s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_nary_cong.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_nary_cong.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fnary_5fcong
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a1 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_nary_cong.case_0
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__3d.construct s e_v2 (by rw [he_v2]; exact empty_args) hinv h64 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying h_a0 h_a1 h_v1
  store_step with Store.apply_rep s1 v2 a0 _ _ hinv1 h64 h_v2 h_a0 (by ns_tac) (by ns_tac) as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2
  store_step with ih.eo__24mk_5fnary_5fcong_5frhs s2 a0 v1 _ _ hinv2 h64 (hG.rem hrem) h_a0 h_v1 as ⟨v4, s3, hinv3, h_v4⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3
  store_step with Store.apply_mk_rep s3 v3 v4 _ _ hinv3 h64 h_v3 h_v4 as ⟨v5, s4, hinv4, h_v5⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4
  case_done hinv4 hG with h_v5 in EoCases.__eo_prog_nary_cong.case_0 using hn_a0

/-- logos's `__eo_prog_nary_cong` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fnary_5fcong.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_nary_cong x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_nary_cong.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_nary_cong
  unfold EoCases.__eo_prog_nary_cong.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fnary_5fcong_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5fnary_5fcong s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_nary_cong x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fnary_5fcong.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5fnary_5fcong
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fnary_5fcong_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_nary_cong.case_0

theorem eo__24eo_5fprog_5fnary_5fcong_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fnary_5fcong.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5fnary_5fcong
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fnary_5fcong s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_nary_cong x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fnary_5fcong_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fnot_5fand_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24eo_5fprog_5fnot_5fand s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_not_and.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_not_and.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fnot_5fand
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_not_and.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_not_and.case_0
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo_not.construct s e_v5 (by rw [he_v5]; exact empty_args) hinv h64 as ⟨v5, s1, hinv1, h_v5⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4
  pat_same v3 v5 with h_v3 h_v5 using hinv1 else hinv1 hG in EoCases.__eo_prog_not_and.case_0
  store_step with ih.eo__24lower_5fnot_5fand s1 v4 _ hinv1 h64 (hG.rem hrem) h_v4 as ⟨v6, s2, hinv2, h_v6⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5
  case_done hinv2 hG with h_v6 in EoCases.__eo_prog_not_and.case_0 using hn_v3 hn_v4

/-- logos's `__eo_prog_not_and` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fnot_5fand.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_not_and x_a0 =
      (firstSome [EoCases.__eo_prog_not_and.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_not_and
  unfold EoCases.__eo_prog_not_and.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fnot_5fand_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fnot_5fand s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_not_and x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fnot_5fand.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fnot_5fand
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fprog_5fnot_5fand_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using
  body_stuck hinv1 hG using hc0 in EoCases.__eo_prog_not_and.case_0

theorem eo__24eo_5fprog_5fnot_5fand_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fnot_5fand.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fnot_5fand
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fnot_5fand s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_not_and x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fnot_5fand_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fnot_5fequiv_5felim1_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24eo_5fprog_5fnot_5fequiv_5felim1 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_not_equiv_elim1.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_not_equiv_elim1.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fnot_5fequiv_5felim1 more_0_eo__24eo_5fprog_5fnot_5fequiv_5felim1
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_not_equiv_elim1.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_not_equiv_elim1.case_0
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo_not.construct s e_v5 (by rw [he_v5]; exact empty_args) hinv h64 as ⟨v5, s1, hinv1, h_v5⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4
  pat_same v3 v5 with h_v3 h_v5 using hinv1 else hinv1 hG in EoCases.__eo_prog_not_equiv_elim1.case_0
  pat_unapply h_v4 as ⟨v7, v8, x_v7, x_v8, h_v7, h_v8, hn_v7, hn_v8⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_not_equiv_elim1.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_not_equiv_elim1.case_0
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo__3d.construct s1 e_v12 (by rw [he_v12]; exact empty_args) hinv1 h64 as ⟨v12, s2, hinv2, h_v12⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11
  pat_same v10 v12 with h_v10 h_v12 using hinv2 else hinv2 hG in EoCases.__eo_prog_not_equiv_elim1.case_0
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo_or.construct s2 e_v13 (by rw [he_v13]; exact empty_args) hinv2 h64 as ⟨v13, s3, hinv3, h_v13⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12
  store_step with Store.apply_rep s3 v13 v11 _ _ hinv3 h64 h_v13 h_v11 (by ns_tac) (by ns_tac) as ⟨v14, s4, hinv4, h_v14⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo_or.construct s4 e_v15 (by rw [he_v15]; exact empty_args) hinv4 h64 as ⟨v15, s5, hinv5, h_v15⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14
  store_step with Store.apply_rep s5 v15 v8 _ _ hinv5 h64 h_v15 h_v8 (by ns_tac) (by ns_tac) as ⟨v16, s6, hinv6, h_v16⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15
  store_step with Store.literal_boolean_spec s6 false hinv6 h64 as ⟨v17, s7, hinv7, h_v17⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16
  store_step with Store.apply_rep s7 v16 v17 _ _ hinv7 h64 h_v16 h_v17 (by ns_tac) (by ns_tac) as ⟨v18, s8, hinv8, h_v18⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17
  store_step with Store.apply_rep s8 v14 v18 _ _ hinv8 h64 h_v14 h_v18 (by ns_tac) (by ns_tac) as ⟨v19, s9, hinv9, h_v19⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18
  case_done hinv9 hG with h_v19 in EoCases.__eo_prog_not_equiv_elim1.case_0 using hn_v3 hn_v4 hn_v7 hn_v8 hn_v10 hn_v11

/-- logos's `__eo_prog_not_equiv_elim1` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fnot_5fequiv_5felim1.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_not_equiv_elim1 x_a0 =
      (firstSome [EoCases.__eo_prog_not_equiv_elim1.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_not_equiv_elim1
  unfold EoCases.__eo_prog_not_equiv_elim1.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fnot_5fequiv_5felim1_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fnot_5fequiv_5felim1 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_not_equiv_elim1 x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fnot_5fequiv_5felim1.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fnot_5fequiv_5felim1
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fprog_5fnot_5fequiv_5felim1_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using
  body_stuck hinv1 hG using hc0 in EoCases.__eo_prog_not_equiv_elim1.case_0

theorem eo__24eo_5fprog_5fnot_5fequiv_5felim1_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fnot_5fequiv_5felim1.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fnot_5fequiv_5felim1
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fnot_5fequiv_5felim1 s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_not_equiv_elim1 x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fnot_5fequiv_5felim1_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fnot_5fequiv_5felim2_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24eo_5fprog_5fnot_5fequiv_5felim2 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_not_equiv_elim2.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_not_equiv_elim2.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fnot_5fequiv_5felim2 more_0_eo__24eo_5fprog_5fnot_5fequiv_5felim2
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_not_equiv_elim2.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_not_equiv_elim2.case_0
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo_not.construct s e_v5 (by rw [he_v5]; exact empty_args) hinv h64 as ⟨v5, s1, hinv1, h_v5⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4
  pat_same v3 v5 with h_v3 h_v5 using hinv1 else hinv1 hG in EoCases.__eo_prog_not_equiv_elim2.case_0
  pat_unapply h_v4 as ⟨v7, v8, x_v7, x_v8, h_v7, h_v8, hn_v7, hn_v8⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_not_equiv_elim2.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_not_equiv_elim2.case_0
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo__3d.construct s1 e_v12 (by rw [he_v12]; exact empty_args) hinv1 h64 as ⟨v12, s2, hinv2, h_v12⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11
  pat_same v10 v12 with h_v10 h_v12 using hinv2 else hinv2 hG in EoCases.__eo_prog_not_equiv_elim2.case_0
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo_or.construct s2 e_v13 (by rw [he_v13]; exact empty_args) hinv2 h64 as ⟨v13, s3, hinv3, h_v13⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo_not.construct s3 e_v14 (by rw [he_v14]; exact empty_args) hinv3 h64 as ⟨v14, s4, hinv4, h_v14⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13
  store_step with Store.apply_rep s4 v14 v11 _ _ hinv4 h64 h_v14 h_v11 (by ns_tac) (by ns_tac) as ⟨v15, s5, hinv5, h_v15⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14
  store_step with Store.apply_rep s5 v13 v15 _ _ hinv5 h64 h_v13 h_v15 (by ns_tac) (by ns_tac) as ⟨v16, s6, hinv6, h_v16⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15
  step as ⟨e_v17, he_v17⟩
  store_step with CtorSpec.eo_or.construct s6 e_v17 (by rw [he_v17]; exact empty_args) hinv6 h64 as ⟨v17, s7, hinv7, h_v17⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16
  step as ⟨e_v18, he_v18⟩
  store_step with CtorSpec.eo_not.construct s7 e_v18 (by rw [he_v18]; exact empty_args) hinv7 h64 as ⟨v18, s8, hinv8, h_v18⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17
  store_step with Store.apply_rep s8 v18 v8 _ _ hinv8 h64 h_v18 h_v8 (by ns_tac) (by ns_tac) as ⟨v19, s9, hinv9, h_v19⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18
  store_step with Store.apply_rep s9 v17 v19 _ _ hinv9 h64 h_v17 h_v19 (by ns_tac) (by ns_tac) as ⟨v20, s10, hinv10, h_v20⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19
  store_step with Store.literal_boolean_spec s10 false hinv10 h64 as ⟨v21, s11, hinv11, h_v21⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20
  store_step with Store.apply_rep s11 v20 v21 _ _ hinv11 h64 h_v20 h_v21 (by ns_tac) (by ns_tac) as ⟨v22, s12, hinv12, h_v22⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21
  store_step with Store.apply_rep s12 v16 v22 _ _ hinv12 h64 h_v16 h_v22 (by ns_tac) (by ns_tac) as ⟨v23, s13, hinv13, h_v23⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22
  case_done hinv13 hG with h_v23 in EoCases.__eo_prog_not_equiv_elim2.case_0 using hn_v3 hn_v4 hn_v7 hn_v8 hn_v10 hn_v11

/-- logos's `__eo_prog_not_equiv_elim2` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fnot_5fequiv_5felim2.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_not_equiv_elim2 x_a0 =
      (firstSome [EoCases.__eo_prog_not_equiv_elim2.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_not_equiv_elim2
  unfold EoCases.__eo_prog_not_equiv_elim2.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fnot_5fequiv_5felim2_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fnot_5fequiv_5felim2 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_not_equiv_elim2 x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fnot_5fequiv_5felim2.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fnot_5fequiv_5felim2
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fprog_5fnot_5fequiv_5felim2_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using
  body_stuck hinv1 hG using hc0 in EoCases.__eo_prog_not_equiv_elim2.case_0

theorem eo__24eo_5fprog_5fnot_5fequiv_5felim2_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fnot_5fequiv_5felim2.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fnot_5fequiv_5felim2
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fnot_5fequiv_5felim2 s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_not_equiv_elim2 x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fnot_5fequiv_5felim2_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fnot_5fimplies_5felim1_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24eo_5fprog_5fnot_5fimplies_5felim1 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_not_implies_elim1.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_not_implies_elim1.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fnot_5fimplies_5felim1
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_not_implies_elim1.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_not_implies_elim1.case_0
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo_not.construct s e_v5 (by rw [he_v5]; exact empty_args) hinv h64 as ⟨v5, s1, hinv1, h_v5⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4
  pat_same v3 v5 with h_v3 h_v5 using hinv1 else hinv1 hG in EoCases.__eo_prog_not_implies_elim1.case_0
  pat_unapply h_v4 as ⟨v7, v8, x_v7, x_v8, h_v7, h_v8, hn_v7, hn_v8⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_not_implies_elim1.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_not_implies_elim1.case_0
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo__3d_3e.construct s1 e_v12 (by rw [he_v12]; exact empty_args) hinv1 h64 as ⟨v12, s2, hinv2, h_v12⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11
  pat_same v10 v12 with h_v10 h_v12 using hinv2 else hinv2 hG in EoCases.__eo_prog_not_implies_elim1.case_0
  case_done hinv2 hG with h_v11 in EoCases.__eo_prog_not_implies_elim1.case_0 using hn_v3 hn_v4 hn_v7 hn_v8 hn_v10 hn_v11

/-- logos's `__eo_prog_not_implies_elim1` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fnot_5fimplies_5felim1.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_not_implies_elim1 x_a0 =
      (firstSome [EoCases.__eo_prog_not_implies_elim1.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_not_implies_elim1
  unfold EoCases.__eo_prog_not_implies_elim1.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fnot_5fimplies_5felim1_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fnot_5fimplies_5felim1 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_not_implies_elim1 x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fnot_5fimplies_5felim1.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fnot_5fimplies_5felim1
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fprog_5fnot_5fimplies_5felim1_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using
  body_stuck hinv1 hG using hc0 in EoCases.__eo_prog_not_implies_elim1.case_0

theorem eo__24eo_5fprog_5fnot_5fimplies_5felim1_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fnot_5fimplies_5felim1.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fnot_5fimplies_5felim1
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fnot_5fimplies_5felim1 s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_not_implies_elim1 x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fnot_5fimplies_5felim1_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fnot_5fimplies_5felim2_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24eo_5fprog_5fnot_5fimplies_5felim2 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_not_implies_elim2.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_not_implies_elim2.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fnot_5fimplies_5felim2
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_not_implies_elim2.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_not_implies_elim2.case_0
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo_not.construct s e_v5 (by rw [he_v5]; exact empty_args) hinv h64 as ⟨v5, s1, hinv1, h_v5⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4
  pat_same v3 v5 with h_v3 h_v5 using hinv1 else hinv1 hG in EoCases.__eo_prog_not_implies_elim2.case_0
  pat_unapply h_v4 as ⟨v7, v8, x_v7, x_v8, h_v7, h_v8, hn_v7, hn_v8⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_not_implies_elim2.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_not_implies_elim2.case_0
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo__3d_3e.construct s1 e_v12 (by rw [he_v12]; exact empty_args) hinv1 h64 as ⟨v12, s2, hinv2, h_v12⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11
  pat_same v10 v12 with h_v10 h_v12 using hinv2 else hinv2 hG in EoCases.__eo_prog_not_implies_elim2.case_0
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo_not.construct s2 e_v13 (by rw [he_v13]; exact empty_args) hinv2 h64 as ⟨v13, s3, hinv3, h_v13⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12
  store_step with Store.apply_rep s3 v13 v8 _ _ hinv3 h64 h_v13 h_v8 (by ns_tac) (by ns_tac) as ⟨v14, s4, hinv4, h_v14⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13
  case_done hinv4 hG with h_v14 in EoCases.__eo_prog_not_implies_elim2.case_0 using hn_v3 hn_v4 hn_v7 hn_v8 hn_v10 hn_v11

/-- logos's `__eo_prog_not_implies_elim2` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fnot_5fimplies_5felim2.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_not_implies_elim2 x_a0 =
      (firstSome [EoCases.__eo_prog_not_implies_elim2.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_not_implies_elim2
  unfold EoCases.__eo_prog_not_implies_elim2.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fnot_5fimplies_5felim2_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fnot_5fimplies_5felim2 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_not_implies_elim2 x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fnot_5fimplies_5felim2.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fnot_5fimplies_5felim2
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fprog_5fnot_5fimplies_5felim2_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using
  body_stuck hinv1 hG using hc0 in EoCases.__eo_prog_not_implies_elim2.case_0

theorem eo__24eo_5fprog_5fnot_5fimplies_5felim2_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fnot_5fimplies_5felim2.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fnot_5fimplies_5felim2
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fnot_5fimplies_5felim2 s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_not_implies_elim2 x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fnot_5fimplies_5felim2_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fnot_5fite_5felim1_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24eo_5fprog_5fnot_5fite_5felim1 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_not_ite_elim1.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_not_ite_elim1.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fnot_5fite_5felim1 more_0_eo__24eo_5fprog_5fnot_5fite_5felim1
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_not_ite_elim1.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_not_ite_elim1.case_0
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo_not.construct s e_v5 (by rw [he_v5]; exact empty_args) hinv h64 as ⟨v5, s1, hinv1, h_v5⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4
  pat_same v3 v5 with h_v3 h_v5 using hinv1 else hinv1 hG in EoCases.__eo_prog_not_ite_elim1.case_0
  pat_unapply h_v4 as ⟨v7, v8, x_v7, x_v8, h_v7, h_v8, hn_v7, hn_v8⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_not_ite_elim1.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_not_ite_elim1.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_not_ite_elim1.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo_ite.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_not_ite_elim1.case_0
  step as ⟨e_v16, he_v16⟩
  store_step with CtorSpec.eo_or.construct s2 e_v16 (by rw [he_v16]; exact empty_args) hinv2 h64 as ⟨v16, s3, hinv3, h_v16⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15
  step as ⟨e_v17, he_v17⟩
  store_step with CtorSpec.eo_not.construct s3 e_v17 (by rw [he_v17]; exact empty_args) hinv3 h64 as ⟨v17, s4, hinv4, h_v17⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16
  store_step with Store.apply_rep s4 v17 v14 _ _ hinv4 h64 h_v17 h_v14 (by ns_tac) (by ns_tac) as ⟨v18, s5, hinv5, h_v18⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17
  store_step with Store.apply_rep s5 v16 v18 _ _ hinv5 h64 h_v16 h_v18 (by ns_tac) (by ns_tac) as ⟨v19, s6, hinv6, h_v19⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18
  step as ⟨e_v20, he_v20⟩
  store_step with CtorSpec.eo_or.construct s6 e_v20 (by rw [he_v20]; exact empty_args) hinv6 h64 as ⟨v20, s7, hinv7, h_v20⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19
  step as ⟨e_v21, he_v21⟩
  store_step with CtorSpec.eo_not.construct s7 e_v21 (by rw [he_v21]; exact empty_args) hinv7 h64 as ⟨v21, s8, hinv8, h_v21⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20
  store_step with Store.apply_rep s8 v21 v11 _ _ hinv8 h64 h_v21 h_v11 (by ns_tac) (by ns_tac) as ⟨v22, s9, hinv9, h_v22⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21
  store_step with Store.apply_rep s9 v20 v22 _ _ hinv9 h64 h_v20 h_v22 (by ns_tac) (by ns_tac) as ⟨v23, s10, hinv10, h_v23⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22
  store_step with Store.literal_boolean_spec s10 false hinv10 h64 as ⟨v24, s11, hinv11, h_v24⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23
  store_step with Store.apply_rep s11 v23 v24 _ _ hinv11 h64 h_v23 h_v24 (by ns_tac) (by ns_tac) as ⟨v25, s12, hinv12, h_v25⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24
  store_step with Store.apply_rep s12 v19 v25 _ _ hinv12 h64 h_v19 h_v25 (by ns_tac) (by ns_tac) as ⟨v26, s13, hinv13, h_v26⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25
  case_done hinv13 hG with h_v26 in EoCases.__eo_prog_not_ite_elim1.case_0 using hn_v3 hn_v4 hn_v7 hn_v8 hn_v10 hn_v11 hn_v13 hn_v14

/-- logos's `__eo_prog_not_ite_elim1` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fnot_5fite_5felim1.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_not_ite_elim1 x_a0 =
      (firstSome [EoCases.__eo_prog_not_ite_elim1.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_not_ite_elim1
  unfold EoCases.__eo_prog_not_ite_elim1.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fnot_5fite_5felim1_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fnot_5fite_5felim1 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_not_ite_elim1 x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fnot_5fite_5felim1.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fnot_5fite_5felim1
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fprog_5fnot_5fite_5felim1_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using
  body_stuck hinv1 hG using hc0 in EoCases.__eo_prog_not_ite_elim1.case_0

theorem eo__24eo_5fprog_5fnot_5fite_5felim1_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fnot_5fite_5felim1.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fnot_5fite_5felim1
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fnot_5fite_5felim1 s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_not_ite_elim1 x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fnot_5fite_5felim1_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fnot_5fite_5felim2_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24eo_5fprog_5fnot_5fite_5felim2 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_not_ite_elim2.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_not_ite_elim2.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fnot_5fite_5felim2 more_0_eo__24eo_5fprog_5fnot_5fite_5felim2
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_not_ite_elim2.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_not_ite_elim2.case_0
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo_not.construct s e_v5 (by rw [he_v5]; exact empty_args) hinv h64 as ⟨v5, s1, hinv1, h_v5⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4
  pat_same v3 v5 with h_v3 h_v5 using hinv1 else hinv1 hG in EoCases.__eo_prog_not_ite_elim2.case_0
  pat_unapply h_v4 as ⟨v7, v8, x_v7, x_v8, h_v7, h_v8, hn_v7, hn_v8⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_not_ite_elim2.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_not_ite_elim2.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_not_ite_elim2.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo_ite.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_not_ite_elim2.case_0
  step as ⟨e_v16, he_v16⟩
  store_step with CtorSpec.eo_or.construct s2 e_v16 (by rw [he_v16]; exact empty_args) hinv2 h64 as ⟨v16, s3, hinv3, h_v16⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15
  store_step with Store.apply_rep s3 v16 v14 _ _ hinv3 h64 h_v16 h_v14 (by ns_tac) (by ns_tac) as ⟨v17, s4, hinv4, h_v17⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16
  step as ⟨e_v18, he_v18⟩
  store_step with CtorSpec.eo_or.construct s4 e_v18 (by rw [he_v18]; exact empty_args) hinv4 h64 as ⟨v18, s5, hinv5, h_v18⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17
  step as ⟨e_v19, he_v19⟩
  store_step with CtorSpec.eo_not.construct s5 e_v19 (by rw [he_v19]; exact empty_args) hinv5 h64 as ⟨v19, s6, hinv6, h_v19⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18
  store_step with Store.apply_rep s6 v19 v8 _ _ hinv6 h64 h_v19 h_v8 (by ns_tac) (by ns_tac) as ⟨v20, s7, hinv7, h_v20⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19
  store_step with Store.apply_rep s7 v18 v20 _ _ hinv7 h64 h_v18 h_v20 (by ns_tac) (by ns_tac) as ⟨v21, s8, hinv8, h_v21⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20
  store_step with Store.literal_boolean_spec s8 false hinv8 h64 as ⟨v22, s9, hinv9, h_v22⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21
  store_step with Store.apply_rep s9 v21 v22 _ _ hinv9 h64 h_v21 h_v22 (by ns_tac) (by ns_tac) as ⟨v23, s10, hinv10, h_v23⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22
  store_step with Store.apply_rep s10 v17 v23 _ _ hinv10 h64 h_v17 h_v23 (by ns_tac) (by ns_tac) as ⟨v24, s11, hinv11, h_v24⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23
  case_done hinv11 hG with h_v24 in EoCases.__eo_prog_not_ite_elim2.case_0 using hn_v3 hn_v4 hn_v7 hn_v8 hn_v10 hn_v11 hn_v13 hn_v14

/-- logos's `__eo_prog_not_ite_elim2` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fnot_5fite_5felim2.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_not_ite_elim2 x_a0 =
      (firstSome [EoCases.__eo_prog_not_ite_elim2.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_not_ite_elim2
  unfold EoCases.__eo_prog_not_ite_elim2.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fnot_5fite_5felim2_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fnot_5fite_5felim2 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_not_ite_elim2 x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fnot_5fite_5felim2.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fnot_5fite_5felim2
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fprog_5fnot_5fite_5felim2_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using
  body_stuck hinv1 hG using hc0 in EoCases.__eo_prog_not_ite_elim2.case_0

theorem eo__24eo_5fprog_5fnot_5fite_5felim2_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fnot_5fite_5felim2.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fnot_5fite_5felim2
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fnot_5fite_5felim2 s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_not_ite_elim2 x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fnot_5fite_5felim2_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fnot_5fnot_5felim_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24eo_5fprog_5fnot_5fnot_5felim s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_not_not_elim.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_not_not_elim.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fnot_5fnot_5felim
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_not_not_elim.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_not_not_elim.case_0
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo_not.construct s e_v5 (by rw [he_v5]; exact empty_args) hinv h64 as ⟨v5, s1, hinv1, h_v5⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4
  pat_same v3 v5 with h_v3 h_v5 using hinv1 else hinv1 hG in EoCases.__eo_prog_not_not_elim.case_0
  pat_unapply h_v4 as ⟨v7, v8, x_v7, x_v8, h_v7, h_v8, hn_v7, hn_v8⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_not_not_elim.case_0
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_not.construct s1 e_v9 (by rw [he_v9]; exact empty_args) hinv1 h64 as ⟨v9, s2, hinv2, h_v9⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8
  pat_same v7 v9 with h_v7 h_v9 using hinv2 else hinv2 hG in EoCases.__eo_prog_not_not_elim.case_0
  case_done hinv2 hG with h_v8 in EoCases.__eo_prog_not_not_elim.case_0 using hn_v3 hn_v4 hn_v7 hn_v8

/-- logos's `__eo_prog_not_not_elim` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fnot_5fnot_5felim.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_not_not_elim x_a0 =
      (firstSome [EoCases.__eo_prog_not_not_elim.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_not_not_elim
  unfold EoCases.__eo_prog_not_not_elim.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fnot_5fnot_5felim_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fnot_5fnot_5felim s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_not_not_elim x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fnot_5fnot_5felim.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fnot_5fnot_5felim
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fprog_5fnot_5fnot_5felim_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using
  body_stuck hinv1 hG using hc0 in EoCases.__eo_prog_not_not_elim.case_0

theorem eo__24eo_5fprog_5fnot_5fnot_5felim_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fnot_5fnot_5felim.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fnot_5fnot_5felim
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fnot_5fnot_5felim s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_not_not_elim x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fnot_5fnot_5felim_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fnot_5fxor_5felim1_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24eo_5fprog_5fnot_5fxor_5felim1 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_not_xor_elim1.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_not_xor_elim1.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fnot_5fxor_5felim1 more_0_eo__24eo_5fprog_5fnot_5fxor_5felim1
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_not_xor_elim1.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_not_xor_elim1.case_0
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo_not.construct s e_v5 (by rw [he_v5]; exact empty_args) hinv h64 as ⟨v5, s1, hinv1, h_v5⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4
  pat_same v3 v5 with h_v3 h_v5 using hinv1 else hinv1 hG in EoCases.__eo_prog_not_xor_elim1.case_0
  pat_unapply h_v4 as ⟨v7, v8, x_v7, x_v8, h_v7, h_v8, hn_v7, hn_v8⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_not_xor_elim1.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_not_xor_elim1.case_0
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo_xor.construct s1 e_v12 (by rw [he_v12]; exact empty_args) hinv1 h64 as ⟨v12, s2, hinv2, h_v12⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11
  pat_same v10 v12 with h_v10 h_v12 using hinv2 else hinv2 hG in EoCases.__eo_prog_not_xor_elim1.case_0
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo_or.construct s2 e_v13 (by rw [he_v13]; exact empty_args) hinv2 h64 as ⟨v13, s3, hinv3, h_v13⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12
  store_step with Store.apply_rep s3 v13 v11 _ _ hinv3 h64 h_v13 h_v11 (by ns_tac) (by ns_tac) as ⟨v14, s4, hinv4, h_v14⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo_or.construct s4 e_v15 (by rw [he_v15]; exact empty_args) hinv4 h64 as ⟨v15, s5, hinv5, h_v15⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14
  step as ⟨e_v16, he_v16⟩
  store_step with CtorSpec.eo_not.construct s5 e_v16 (by rw [he_v16]; exact empty_args) hinv5 h64 as ⟨v16, s6, hinv6, h_v16⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15
  store_step with Store.apply_rep s6 v16 v8 _ _ hinv6 h64 h_v16 h_v8 (by ns_tac) (by ns_tac) as ⟨v17, s7, hinv7, h_v17⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16
  store_step with Store.apply_rep s7 v15 v17 _ _ hinv7 h64 h_v15 h_v17 (by ns_tac) (by ns_tac) as ⟨v18, s8, hinv8, h_v18⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17
  store_step with Store.literal_boolean_spec s8 false hinv8 h64 as ⟨v19, s9, hinv9, h_v19⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18
  store_step with Store.apply_rep s9 v18 v19 _ _ hinv9 h64 h_v18 h_v19 (by ns_tac) (by ns_tac) as ⟨v20, s10, hinv10, h_v20⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19
  store_step with Store.apply_rep s10 v14 v20 _ _ hinv10 h64 h_v14 h_v20 (by ns_tac) (by ns_tac) as ⟨v21, s11, hinv11, h_v21⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20
  case_done hinv11 hG with h_v21 in EoCases.__eo_prog_not_xor_elim1.case_0 using hn_v3 hn_v4 hn_v7 hn_v8 hn_v10 hn_v11

/-- logos's `__eo_prog_not_xor_elim1` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fnot_5fxor_5felim1.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_not_xor_elim1 x_a0 =
      (firstSome [EoCases.__eo_prog_not_xor_elim1.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_not_xor_elim1
  unfold EoCases.__eo_prog_not_xor_elim1.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fnot_5fxor_5felim1_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fnot_5fxor_5felim1 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_not_xor_elim1 x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fnot_5fxor_5felim1.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fnot_5fxor_5felim1
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fprog_5fnot_5fxor_5felim1_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using
  body_stuck hinv1 hG using hc0 in EoCases.__eo_prog_not_xor_elim1.case_0

theorem eo__24eo_5fprog_5fnot_5fxor_5felim1_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fnot_5fxor_5felim1.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fnot_5fxor_5felim1
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fnot_5fxor_5felim1 s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_not_xor_elim1 x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fnot_5fxor_5felim1_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fnot_5fxor_5felim2_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24eo_5fprog_5fnot_5fxor_5felim2 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_not_xor_elim2.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_not_xor_elim2.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fnot_5fxor_5felim2 more_0_eo__24eo_5fprog_5fnot_5fxor_5felim2
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_not_xor_elim2.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_not_xor_elim2.case_0
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo_not.construct s e_v5 (by rw [he_v5]; exact empty_args) hinv h64 as ⟨v5, s1, hinv1, h_v5⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4
  pat_same v3 v5 with h_v3 h_v5 using hinv1 else hinv1 hG in EoCases.__eo_prog_not_xor_elim2.case_0
  pat_unapply h_v4 as ⟨v7, v8, x_v7, x_v8, h_v7, h_v8, hn_v7, hn_v8⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_not_xor_elim2.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_not_xor_elim2.case_0
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo_xor.construct s1 e_v12 (by rw [he_v12]; exact empty_args) hinv1 h64 as ⟨v12, s2, hinv2, h_v12⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11
  pat_same v10 v12 with h_v10 h_v12 using hinv2 else hinv2 hG in EoCases.__eo_prog_not_xor_elim2.case_0
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo_or.construct s2 e_v13 (by rw [he_v13]; exact empty_args) hinv2 h64 as ⟨v13, s3, hinv3, h_v13⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo_not.construct s3 e_v14 (by rw [he_v14]; exact empty_args) hinv3 h64 as ⟨v14, s4, hinv4, h_v14⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13
  store_step with Store.apply_rep s4 v14 v11 _ _ hinv4 h64 h_v14 h_v11 (by ns_tac) (by ns_tac) as ⟨v15, s5, hinv5, h_v15⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14
  store_step with Store.apply_rep s5 v13 v15 _ _ hinv5 h64 h_v13 h_v15 (by ns_tac) (by ns_tac) as ⟨v16, s6, hinv6, h_v16⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15
  step as ⟨e_v17, he_v17⟩
  store_step with CtorSpec.eo_or.construct s6 e_v17 (by rw [he_v17]; exact empty_args) hinv6 h64 as ⟨v17, s7, hinv7, h_v17⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16
  store_step with Store.apply_rep s7 v17 v8 _ _ hinv7 h64 h_v17 h_v8 (by ns_tac) (by ns_tac) as ⟨v18, s8, hinv8, h_v18⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17
  store_step with Store.literal_boolean_spec s8 false hinv8 h64 as ⟨v19, s9, hinv9, h_v19⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18
  store_step with Store.apply_rep s9 v18 v19 _ _ hinv9 h64 h_v18 h_v19 (by ns_tac) (by ns_tac) as ⟨v20, s10, hinv10, h_v20⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19
  store_step with Store.apply_rep s10 v16 v20 _ _ hinv10 h64 h_v16 h_v20 (by ns_tac) (by ns_tac) as ⟨v21, s11, hinv11, h_v21⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20
  case_done hinv11 hG with h_v21 in EoCases.__eo_prog_not_xor_elim2.case_0 using hn_v3 hn_v4 hn_v7 hn_v8 hn_v10 hn_v11

/-- logos's `__eo_prog_not_xor_elim2` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fnot_5fxor_5felim2.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_not_xor_elim2 x_a0 =
      (firstSome [EoCases.__eo_prog_not_xor_elim2.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_not_xor_elim2
  unfold EoCases.__eo_prog_not_xor_elim2.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fnot_5fxor_5felim2_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fnot_5fxor_5felim2 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_not_xor_elim2 x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fnot_5fxor_5felim2.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fnot_5fxor_5felim2
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fprog_5fnot_5fxor_5felim2_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using
  body_stuck hinv1 hG using hc0 in EoCases.__eo_prog_not_xor_elim2.case_0

theorem eo__24eo_5fprog_5fnot_5fxor_5felim2_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fnot_5fxor_5felim2.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fnot_5fxor_5felim2
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fnot_5fxor_5felim2 s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_not_xor_elim2 x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fnot_5fxor_5felim2_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fpairwise_5fcong_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fpairwise_5fcong s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_pairwise_cong.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_pairwise_cong.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fpairwise_5fcong
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_prog_pairwise_cong.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a1 as ⟨v4, x_v4, h_v4⟩ else hinv hG in EoCases.__eo_prog_pairwise_cong.case_0
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__3d.construct s e_v5 (by rw [he_v5]; exact empty_args) hinv h64 as ⟨v5, s1, hinv1, h_v5⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4
  store_step with Store.apply_rep s1 v1 v2 _ _ hinv1 h64 h_v1 h_v2 (by ns_tac) (by ns_tac) as ⟨v6, s2, hinv2, h_v6⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5
  store_step with Store.apply_rep s2 v5 v6 _ _ hinv2 h64 h_v5 h_v6 (by ns_tac) (by ns_tac) as ⟨v7, s3, hinv3, h_v7⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24mk_5fnary_5fcong_5frhs s3 v2 v4 _ _ hinv3 h64 (hG.rem hrem) h_v2 h_v4 as ⟨v8, s4, hinv4, h_v8⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with Store.apply_mk_rep s4 v1 v8 _ _ hinv4 h64 h_v1 h_v8 as ⟨v9, s5, hinv5, h_v9⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  store_step with Store.apply_mk_rep s5 v7 v9 _ _ hinv5 h64 h_v7 h_v9 as ⟨v10, s6, hinv6, h_v10⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  case_done hinv6 hG with h_v10 in EoCases.__eo_prog_pairwise_cong.case_0 using hn_a0 hn_v1 hn_v2

/-- logos's `__eo_prog_pairwise_cong` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fpairwise_5fcong.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_pairwise_cong x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_pairwise_cong.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_pairwise_cong
  unfold EoCases.__eo_prog_pairwise_cong.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fpairwise_5fcong_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5fpairwise_5fcong s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_pairwise_cong x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fpairwise_5fcong.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5fpairwise_5fcong
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fpairwise_5fcong_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_pairwise_cong.case_0

theorem eo__24eo_5fprog_5fpairwise_5fcong_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fpairwise_5fcong.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5fpairwise_5fcong
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fpairwise_5fcong s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_pairwise_cong x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fpairwise_5fcong_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fprocess_5fscope_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fprocess_5fscope s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_process_scope.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_process_scope.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fprocess_5fscope
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a1 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_process_scope.case_0
  store_step with ih.eo__24run_5fprocess_5fscope s v1 a0 _ _ hinv h64 hrem h_v1 h_a0 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying h_a0 h_a1 h_v1
  case_done hinv1 hG with h_v2 in EoCases.__eo_prog_process_scope.case_0 using hn_a0

/-- logos's `__eo_prog_process_scope` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fprocess_5fscope.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_process_scope x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_process_scope.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_process_scope
  unfold EoCases.__eo_prog_process_scope.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fprocess_5fscope_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5fprocess_5fscope s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_process_scope x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fprocess_5fscope.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5fprocess_5fscope
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fprocess_5fscope_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_process_scope.case_0

theorem eo__24eo_5fprog_5fprocess_5fscope_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fprocess_5fscope.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5fprocess_5fscope
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fprocess_5fscope s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_process_scope x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fprocess_5fscope_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fre_2ddiff_2delim_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fre_2ddiff_2delim s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_re_diff_elim.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_re_diff_elim.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fre_2ddiff_2delim more_0_eo__24eo_5fprog_5fre_2ddiff_2delim
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_re_2ediff.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a1 _ _ hinv3 h64 h_v2 h_a1 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v0 v3 _ _ hinv4 h64 h_v0 h_v3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo_re_2einter.construct s5 e_v5 (by rw [he_v5]; exact empty_args) hinv5 h64 as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4
  store_step with Store.apply_rep s6 v5 a0 _ _ hinv6 h64 h_v5 h_a0 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo_re_2einter.construct s7 e_v7 (by rw [he_v7]; exact empty_args) hinv7 h64 as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo_re_2ecomp.construct s8 e_v8 (by rw [he_v8]; exact empty_args) hinv8 h64 as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  store_step with Store.apply_rep s9 v8 a1 _ _ hinv9 h64 h_v8 h_a1 (by ns_tac) (by ns_tac) as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
  store_step with Store.apply_rep s10 v7 v9 _ _ hinv10 h64 h_v7 h_v9 (by ns_tac) (by ns_tac) as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  step as ⟨e_v11, he_v11⟩
  store_step with CtorSpec.eo_re_2eall.construct s11 e_v11 (by rw [he_v11]; exact empty_args) hinv11 h64 as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
  store_step with Store.apply_rep s12 v10 v11 _ _ hinv12 h64 h_v10 h_v11 (by ns_tac) (by ns_tac) as ⟨v12, s13, hinv13, h_v12⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11
  store_step with Store.apply_rep s13 v6 v12 _ _ hinv13 h64 h_v6 h_v12 (by ns_tac) (by ns_tac) as ⟨v13, s14, hinv14, h_v13⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
  store_step with Store.apply_rep s14 v4 v13 _ _ hinv14 h64 h_v4 h_v13 (by ns_tac) (by ns_tac) as ⟨v14, s15, hinv15, h_v14⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13
  case_done hinv15 hG with h_v14 in EoCases.__eo_prog_re_diff_elim.case_0 using hn_a0 hn_a1

/-- logos's `__eo_prog_re_diff_elim` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fre_2ddiff_2delim.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_re_diff_elim x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_re_diff_elim.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_re_diff_elim
  unfold EoCases.__eo_prog_re_diff_elim.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fre_2ddiff_2delim_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5fre_2ddiff_2delim s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_re_diff_elim x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fre_2ddiff_2delim.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5fre_2ddiff_2delim
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fre_2ddiff_2delim_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_re_diff_elim.case_0

theorem eo__24eo_5fprog_5fre_2ddiff_2delim_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fre_2ddiff_2delim.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5fre_2ddiff_2delim
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fre_2ddiff_2delim s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_re_diff_elim x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fre_2ddiff_2delim_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fre_2din_2dcomp_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fre_2din_2dcomp s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_re_in_comp.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_re_in_comp.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fre_2din_2dcomp more_0_eo__24eo_5fprog_5fre_2din_2dcomp
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_str_2ein_5fre.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_re_2ecomp.construct s3 e_v3 (by rw [he_v3]; exact empty_args) hinv3 h64 as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v3 a1 _ _ hinv4 h64 h_v3 h_a1 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3
  store_step with Store.apply_rep s5 v2 v4 _ _ hinv5 h64 h_v2 h_v4 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4
  store_step with Store.apply_rep s6 v0 v5 _ _ hinv6 h64 h_v0 h_v5 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo_not.construct s7 e_v7 (by rw [he_v7]; exact empty_args) hinv7 h64 as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo_str_2ein_5fre.construct s8 e_v8 (by rw [he_v8]; exact empty_args) hinv8 h64 as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  store_step with Store.apply_rep s9 v8 a0 _ _ hinv9 h64 h_v8 h_a0 (by ns_tac) (by ns_tac) as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
  store_step with Store.apply_rep s10 v9 a1 _ _ hinv10 h64 h_v9 h_a1 (by ns_tac) (by ns_tac) as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  store_step with Store.apply_rep s11 v7 v10 _ _ hinv11 h64 h_v7 h_v10 (by ns_tac) (by ns_tac) as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
  store_step with Store.apply_rep s12 v6 v11 _ _ hinv12 h64 h_v6 h_v11 (by ns_tac) (by ns_tac) as ⟨v12, s13, hinv13, h_v12⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11
  case_done hinv13 hG with h_v12 in EoCases.__eo_prog_re_in_comp.case_0 using hn_a0 hn_a1

/-- logos's `__eo_prog_re_in_comp` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fre_2din_2dcomp.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_re_in_comp x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_re_in_comp.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_re_in_comp
  unfold EoCases.__eo_prog_re_in_comp.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fre_2din_2dcomp_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5fre_2din_2dcomp s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_re_in_comp x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fre_2din_2dcomp.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5fre_2din_2dcomp
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fre_2din_2dcomp_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_re_in_comp.case_0

theorem eo__24eo_5fprog_5fre_2din_2dcomp_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fre_2din_2dcomp.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5fre_2din_2dcomp
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fre_2din_2dcomp s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_re_in_comp x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fre_2din_2dcomp_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fre_2din_2dcstring_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fre_2din_2dcstring s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_re_in_cstring.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_re_in_cstring.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fre_2din_2dcstring
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_str_2ein_5fre.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_str_2eto_5fre.construct s3 e_v3 (by rw [he_v3]; exact empty_args) hinv3 h64 as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v3 a1 _ _ hinv4 h64 h_v3 h_a1 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3
  store_step with Store.apply_rep s5 v2 v4 _ _ hinv5 h64 h_v2 h_v4 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4
  store_step with Store.apply_rep s6 v0 v5 _ _ hinv6 h64 h_v0 h_v5 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo__3d.construct s7 e_v7 (by rw [he_v7]; exact empty_args) hinv7 h64 as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  store_step with Store.apply_rep s8 v7 a0 _ _ hinv8 h64 h_v7 h_a0 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  store_step with Store.apply_rep s9 v8 a1 _ _ hinv9 h64 h_v8 h_a1 (by ns_tac) (by ns_tac) as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
  store_step with Store.apply_rep s10 v6 v9 _ _ hinv10 h64 h_v6 h_v9 (by ns_tac) (by ns_tac) as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  case_done hinv11 hG with h_v10 in EoCases.__eo_prog_re_in_cstring.case_0 using hn_a0 hn_a1

/-- logos's `__eo_prog_re_in_cstring` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fre_2din_2dcstring.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_re_in_cstring x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_re_in_cstring.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_re_in_cstring
  unfold EoCases.__eo_prog_re_in_cstring.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fre_2din_2dcstring_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5fre_2din_2dcstring s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_re_in_cstring x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fre_2din_2dcstring.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5fre_2din_2dcstring
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fre_2din_2dcstring_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_re_in_cstring.case_0

theorem eo__24eo_5fprog_5fre_2din_2dcstring_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fre_2din_2dcstring.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5fre_2din_2dcstring
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fre_2din_2dcstring s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_re_in_cstring x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fre_2din_2dcstring_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fre_2din_2dempty_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fre_2din_2dempty s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_re_in_empty.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_re_in_empty.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fre_2din_2dempty
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_str_2ein_5fre.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_v0 h_v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_re_2enone.construct s3 e_v3 (by rw [he_v3]; exact empty_args) hinv3 h64 as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v2 v3 _ _ hinv4 h64 h_v2 h_v3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3
  store_step with Store.apply_rep s5 v0 v4 _ _ hinv5 h64 h_v0 h_v4 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4
  store_step with Store.literal_boolean_spec s6 false hinv6 h64 as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with Store.apply_rep s7 v5 v6 _ _ hinv7 h64 h_v5 h_v6 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  case_done hinv8 hG with h_v7 in EoCases.__eo_prog_re_in_empty.case_0 using hn_a0

/-- logos's `__eo_prog_re_in_empty` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fre_2din_2dempty.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_re_in_empty x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_re_in_empty.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_re_in_empty
  unfold EoCases.__eo_prog_re_in_empty.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fre_2din_2dempty_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fre_2din_2dempty s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_re_in_empty x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fre_2din_2dempty.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fre_2din_2dempty
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fre_2din_2dempty_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_re_in_empty.case_0

theorem eo__24eo_5fprog_5fre_2din_2dempty_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fre_2din_2dempty.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fre_2din_2dempty
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fre_2din_2dempty s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_re_in_empty x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fre_2din_2dempty_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fre_2din_2dsigma_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fre_2din_2dsigma s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_re_in_sigma.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_re_in_sigma.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fre_2din_2dsigma more_0_eo__24eo_5fprog_5fre_2din_2dsigma
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_str_2ein_5fre.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_v0 h_v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_re_2eallchar.construct s3 e_v3 (by rw [he_v3]; exact empty_args) hinv3 h64 as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v2 v3 _ _ hinv4 h64 h_v2 h_v3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3
  store_step with Store.apply_rep s5 v0 v4 _ _ hinv5 h64 h_v0 h_v4 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__3d.construct s6 e_v6 (by rw [he_v6]; exact empty_args) hinv6 h64 as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo_str_2elen.construct s7 e_v7 (by rw [he_v7]; exact empty_args) hinv7 h64 as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  store_step with Store.apply_rep s8 v7 a0 _ _ hinv8 h64 h_v7 h_a0 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  store_step with Store.apply_rep s9 v6 v8 _ _ hinv9 h64 h_v6 h_v8 (by ns_tac) (by ns_tac) as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s10 1#u32 (1) (by scalar_tac) hinv10 h64 as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  store_step with Store.apply_rep s11 v9 v10 _ _ hinv11 h64 h_v9 h_v10 (by ns_tac) (by ns_tac) as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
  store_step with Store.apply_rep s12 v5 v11 _ _ hinv12 h64 h_v5 h_v11 (by ns_tac) (by ns_tac) as ⟨v12, s13, hinv13, h_v12⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11
  case_done hinv13 hG with h_v12 in EoCases.__eo_prog_re_in_sigma.case_0 using hn_a0

/-- logos's `__eo_prog_re_in_sigma` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fre_2din_2dsigma.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_re_in_sigma x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_re_in_sigma.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_re_in_sigma
  unfold EoCases.__eo_prog_re_in_sigma.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fre_2din_2dsigma_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fre_2din_2dsigma s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_re_in_sigma x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fre_2din_2dsigma.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fre_2din_2dsigma
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fre_2din_2dsigma_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_re_in_sigma.case_0

theorem eo__24eo_5fprog_5fre_2din_2dsigma_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fre_2din_2dsigma.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fre_2din_2dsigma
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fre_2din_2dsigma s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_re_in_sigma x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fre_2din_2dsigma_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fre_2din_2dsigma_2dstar_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fre_2din_2dsigma_2dstar s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_re_in_sigma_star.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_re_in_sigma_star.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fre_2din_2dsigma_2dstar
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_str_2ein_5fre.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_v0 h_v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_re_2e_2a.construct s3 e_v3 (by rw [he_v3]; exact empty_args) hinv3 h64 as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo_re_2eallchar.construct s4 e_v4 (by rw [he_v4]; exact empty_args) hinv4 h64 as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3
  store_step with Store.apply_rep s5 v3 v4 _ _ hinv5 h64 h_v3 h_v4 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4
  store_step with Store.apply_rep s6 v2 v5 _ _ hinv6 h64 h_v2 h_v5 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with Store.apply_rep s7 v0 v6 _ _ hinv7 h64 h_v0 h_v6 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  store_step with Store.literal_boolean_spec s8 true hinv8 h64 as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  store_step with Store.apply_rep s9 v7 v8 _ _ hinv9 h64 h_v7 h_v8 (by ns_tac) (by ns_tac) as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv10 hG with h_v9 in EoCases.__eo_prog_re_in_sigma_star.case_0 using hn_a0

/-- logos's `__eo_prog_re_in_sigma_star` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fre_2din_2dsigma_2dstar.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_re_in_sigma_star x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_re_in_sigma_star.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_re_in_sigma_star
  unfold EoCases.__eo_prog_re_in_sigma_star.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fre_2din_2dsigma_2dstar_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fre_2din_2dsigma_2dstar s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_re_in_sigma_star x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fre_2din_2dsigma_2dstar.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fre_2din_2dsigma_2dstar
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fre_2din_2dsigma_2dstar_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_re_in_sigma_star.case_0

theorem eo__24eo_5fprog_5fre_2din_2dsigma_2dstar_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fre_2din_2dsigma_2dstar.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fre_2din_2dsigma_2dstar
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fre_2din_2dsigma_2dstar s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_re_in_sigma_star x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fre_2din_2dsigma_2dstar_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fre_2dinter_2dcstring_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fre_2dinter_2dcstring s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_re_inter_cstring.case_0 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_re_inter_cstring.case_0 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fre_2dinter_2dcstring more_0_eo__24eo_5fprog_5fre_2dinter_2dcstring more_1_eo__24eo_5fprog_5fre_2dinter_2dcstring more_2_eo__24eo_5fprog_5fre_2dinter_2dcstring
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a3 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_re_inter_cstring.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_re_inter_cstring.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_re_inter_cstring.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_re_inter_cstring.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_re_inter_cstring.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_re_inter_cstring.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo_str_2ein_5fre.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_re_inter_cstring.case_0
  pat_same v14 a2 with h_v14 h_a2 using hinv2 else hinv2 hG in EoCases.__eo_prog_re_inter_cstring.case_0
  pat_unapply h_v11 as ⟨v17, v18, x_v17, x_v18, h_v17, h_v18, hn_v17, hn_v18⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_re_inter_cstring.case_0
  pat_unapply h_v17 as ⟨v20, v21, x_v20, x_v21, h_v20, h_v21, hn_v20, hn_v21⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_re_inter_cstring.case_0
  step as ⟨e_v22, he_v22⟩
  store_step with CtorSpec.eo_re_2einter.construct s2 e_v22 (by rw [he_v22]; exact empty_args) hinv2 h64 as ⟨v22, s3, hinv3, h_v22⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v20 h_v21
  pat_same v20 v22 with h_v20 h_v22 using hinv3 else hinv3 hG in EoCases.__eo_prog_re_inter_cstring.case_0
  pat_unapply h_v21 as ⟨v24, v25, x_v24, x_v25, h_v24, h_v25, hn_v24, hn_v25⟩ using hinv3 else hinv3 hG in EoCases.__eo_prog_re_inter_cstring.case_0
  step as ⟨e_v26, he_v26⟩
  store_step with CtorSpec.eo_str_2eto_5fre.construct s3 e_v26 (by rw [he_v26]; exact empty_args) hinv3 h64 as ⟨v26, s4, hinv4, h_v26⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25
  pat_same v24 v26 with h_v24 h_v26 using hinv4 else hinv4 hG in EoCases.__eo_prog_re_inter_cstring.case_0
  pat_same v25 a2 with h_v25 h_a2 using hinv4 else hinv4 hG in EoCases.__eo_prog_re_inter_cstring.case_0
  pat_unapply h_v18 as ⟨v28, v29, x_v28, x_v29, h_v28, h_v29, hn_v28, hn_v29⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_re_inter_cstring.case_0
  pat_unapply h_v28 as ⟨v31, v32, x_v31, x_v32, h_v31, h_v32, hn_v31, hn_v32⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_re_inter_cstring.case_0
  step as ⟨e_v33, he_v33⟩
  store_step with CtorSpec.eo_re_2einter.construct s4 e_v33 (by rw [he_v33]; exact empty_args) hinv4 h64 as ⟨v33, s5, hinv5, h_v33⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32
  pat_same v31 v33 with h_v31 h_v33 using hinv5 else hinv5 hG in EoCases.__eo_prog_re_inter_cstring.case_0
  pat_same v32 a0 with h_v32 h_a0 using hinv5 else hinv5 hG in EoCases.__eo_prog_re_inter_cstring.case_0
  pat_same v29 a1 with h_v29 h_a1 using hinv5 else hinv5 hG in EoCases.__eo_prog_re_inter_cstring.case_0
  store_step with Store.literal_boolean_spec s5 true hinv5 h64 as ⟨v34, s6, hinv6, h_v34⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33
  pat_same v4 v34 with h_v4 h_v34 using hinv6 else hinv6 hG in EoCases.__eo_prog_re_inter_cstring.case_0
  step as ⟨e_v35, he_v35⟩
  store_step with CtorSpec.eo__3d.construct s6 e_v35 (by rw [he_v35]; exact empty_args) hinv6 h64 as ⟨v35, s7, hinv7, h_v35⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34
  step as ⟨e_v36, he_v36⟩
  store_step with CtorSpec.eo_re_2einter.construct s7 e_v36 (by rw [he_v36]; exact empty_args) hinv7 h64 as ⟨v36, s8, hinv8, h_v36⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34 h_v35
  step as ⟨e_v37, he_v37⟩
  store_step with CtorSpec.eo_str_2eto_5fre.construct s8 e_v37 (by rw [he_v37]; exact empty_args) hinv8 h64 as ⟨v37, s9, hinv9, h_v37⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36
  store_step with Store.apply_rep s9 v37 a2 _ _ hinv9 h64 h_v37 h_a2 (by ns_tac) (by ns_tac) as ⟨v38, s10, hinv10, h_v38⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37
  store_step with Store.apply_rep s10 v36 v38 _ _ hinv10 h64 h_v36 h_v38 (by ns_tac) (by ns_tac) as ⟨v39, s11, hinv11, h_v39⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38
  step as ⟨e_v40, he_v40⟩
  store_step with CtorSpec.eo_re_2einter.construct s11 e_v40 (by rw [he_v40]; exact empty_args) hinv11 h64 as ⟨v40, s12, hinv12, h_v40⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39
  store_step with Store.apply_rep s12 v40 a0 _ _ hinv12 h64 h_v40 h_a0 (by ns_tac) (by ns_tac) as ⟨v41, s13, hinv13, h_v41⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40
  store_step with Store.apply_rep s13 v41 a1 _ _ hinv13 h64 h_v41 h_a1 (by ns_tac) (by ns_tac) as ⟨v42, s14, hinv14, h_v42⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41
  store_step with Store.apply_rep s14 v39 v42 _ _ hinv14 h64 h_v39 h_v42 (by ns_tac) (by ns_tac) as ⟨v43, s15, hinv15, h_v43⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42
  store_step with Store.apply_rep s15 v35 v43 _ _ hinv15 h64 h_v35 h_v43 (by ns_tac) (by ns_tac) as ⟨v44, s16, hinv16, h_v44⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43
  step as ⟨e_v45, he_v45⟩
  store_step with CtorSpec.eo_str_2eto_5fre.construct s16 e_v45 (by rw [he_v45]; exact empty_args) hinv16 h64 as ⟨v45, s17, hinv17, h_v45⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44
  store_step with Store.apply_rep s17 v45 a2 _ _ hinv17 h64 h_v45 h_a2 (by ns_tac) (by ns_tac) as ⟨v46, s18, hinv18, h_v46⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45
  store_step with Store.apply_rep s18 v44 v46 _ _ hinv18 h64 h_v44 h_v46 (by ns_tac) (by ns_tac) as ⟨v47, s19, hinv19, h_v47⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46
  case_done hinv19 hG with h_v47 in EoCases.__eo_prog_re_inter_cstring.case_0 using hn_a0 hn_a1 hn_a2 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v13 hn_v14 hn_v17 hn_v18 hn_v20 hn_v21 hn_v24 hn_v25 hn_v28 hn_v29 hn_v31 hn_v32

/-- logos's `__eo_prog_re_inter_cstring` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fre_2dinter_2dcstring.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) :
    __eo_prog_re_inter_cstring x_a0 x_a1 x_a2 x_a3 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_re_inter_cstring.case_0 x_a0 x_a1 x_a2 x_a3] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_re_inter_cstring
  unfold EoCases.__eo_prog_re_inter_cstring.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fre_2dinter_2dcstring_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) :
    body_eo__24eo_5fprog_5fre_2dinter_2dcstring s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_re_inter_cstring x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fre_2dinter_2dcstring.rust_eq x_a0 x_a1 x_a2 x_a3 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3)]
  unfold body_eo__24eo_5fprog_5fre_2dinter_2dcstring
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fre_2dinter_2dcstring_spec n ih s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 using hn_a0 hn_a1 hn_a2
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hc0 in EoCases.__eo_prog_re_inter_cstring.case_0

theorem eo__24eo_5fprog_5fre_2dinter_2dcstring_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fre_2dinter_2dcstring.Spec n := by
  intro s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3
  unfold eo__24eo_5fprog_5fre_2dinter_2dcstring
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fre_2dinter_2dcstring s1 a0 a1 a2 a3) (fun s' t => Represents.rep s' t (__eo_prog_re_inter_cstring x_a0 x_a1 x_a2 x_a3))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fre_2dinter_2dcstring_spec m (ih m hm) s1 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fre_2dinter_2dcstring_2dneg_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fre_2dinter_2dcstring_2dneg s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_re_inter_cstring_neg.case_0 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_re_inter_cstring_neg.case_0 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fre_2dinter_2dcstring_2dneg more_0_eo__24eo_5fprog_5fre_2dinter_2dcstring_2dneg more_1_eo__24eo_5fprog_5fre_2dinter_2dcstring_2dneg more_2_eo__24eo_5fprog_5fre_2dinter_2dcstring_2dneg
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a3 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_re_inter_cstring_neg.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_re_inter_cstring_neg.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_re_inter_cstring_neg.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_re_inter_cstring_neg.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_re_inter_cstring_neg.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_re_inter_cstring_neg.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo_str_2ein_5fre.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_re_inter_cstring_neg.case_0
  pat_same v14 a2 with h_v14 h_a2 using hinv2 else hinv2 hG in EoCases.__eo_prog_re_inter_cstring_neg.case_0
  pat_unapply h_v11 as ⟨v17, v18, x_v17, x_v18, h_v17, h_v18, hn_v17, hn_v18⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_re_inter_cstring_neg.case_0
  pat_unapply h_v17 as ⟨v20, v21, x_v20, x_v21, h_v20, h_v21, hn_v20, hn_v21⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_re_inter_cstring_neg.case_0
  step as ⟨e_v22, he_v22⟩
  store_step with CtorSpec.eo_re_2einter.construct s2 e_v22 (by rw [he_v22]; exact empty_args) hinv2 h64 as ⟨v22, s3, hinv3, h_v22⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v20 h_v21
  pat_same v20 v22 with h_v20 h_v22 using hinv3 else hinv3 hG in EoCases.__eo_prog_re_inter_cstring_neg.case_0
  pat_unapply h_v21 as ⟨v24, v25, x_v24, x_v25, h_v24, h_v25, hn_v24, hn_v25⟩ using hinv3 else hinv3 hG in EoCases.__eo_prog_re_inter_cstring_neg.case_0
  step as ⟨e_v26, he_v26⟩
  store_step with CtorSpec.eo_str_2eto_5fre.construct s3 e_v26 (by rw [he_v26]; exact empty_args) hinv3 h64 as ⟨v26, s4, hinv4, h_v26⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25
  pat_same v24 v26 with h_v24 h_v26 using hinv4 else hinv4 hG in EoCases.__eo_prog_re_inter_cstring_neg.case_0
  pat_same v25 a2 with h_v25 h_a2 using hinv4 else hinv4 hG in EoCases.__eo_prog_re_inter_cstring_neg.case_0
  pat_unapply h_v18 as ⟨v28, v29, x_v28, x_v29, h_v28, h_v29, hn_v28, hn_v29⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_re_inter_cstring_neg.case_0
  pat_unapply h_v28 as ⟨v31, v32, x_v31, x_v32, h_v31, h_v32, hn_v31, hn_v32⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_re_inter_cstring_neg.case_0
  step as ⟨e_v33, he_v33⟩
  store_step with CtorSpec.eo_re_2einter.construct s4 e_v33 (by rw [he_v33]; exact empty_args) hinv4 h64 as ⟨v33, s5, hinv5, h_v33⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32
  pat_same v31 v33 with h_v31 h_v33 using hinv5 else hinv5 hG in EoCases.__eo_prog_re_inter_cstring_neg.case_0
  pat_same v32 a0 with h_v32 h_a0 using hinv5 else hinv5 hG in EoCases.__eo_prog_re_inter_cstring_neg.case_0
  pat_same v29 a1 with h_v29 h_a1 using hinv5 else hinv5 hG in EoCases.__eo_prog_re_inter_cstring_neg.case_0
  store_step with Store.literal_boolean_spec s5 false hinv5 h64 as ⟨v34, s6, hinv6, h_v34⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33
  pat_same v4 v34 with h_v4 h_v34 using hinv6 else hinv6 hG in EoCases.__eo_prog_re_inter_cstring_neg.case_0
  step as ⟨e_v35, he_v35⟩
  store_step with CtorSpec.eo__3d.construct s6 e_v35 (by rw [he_v35]; exact empty_args) hinv6 h64 as ⟨v35, s7, hinv7, h_v35⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34
  step as ⟨e_v36, he_v36⟩
  store_step with CtorSpec.eo_re_2einter.construct s7 e_v36 (by rw [he_v36]; exact empty_args) hinv7 h64 as ⟨v36, s8, hinv8, h_v36⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34 h_v35
  step as ⟨e_v37, he_v37⟩
  store_step with CtorSpec.eo_str_2eto_5fre.construct s8 e_v37 (by rw [he_v37]; exact empty_args) hinv8 h64 as ⟨v37, s9, hinv9, h_v37⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36
  store_step with Store.apply_rep s9 v37 a2 _ _ hinv9 h64 h_v37 h_a2 (by ns_tac) (by ns_tac) as ⟨v38, s10, hinv10, h_v38⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37
  store_step with Store.apply_rep s10 v36 v38 _ _ hinv10 h64 h_v36 h_v38 (by ns_tac) (by ns_tac) as ⟨v39, s11, hinv11, h_v39⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38
  step as ⟨e_v40, he_v40⟩
  store_step with CtorSpec.eo_re_2einter.construct s11 e_v40 (by rw [he_v40]; exact empty_args) hinv11 h64 as ⟨v40, s12, hinv12, h_v40⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39
  store_step with Store.apply_rep s12 v40 a0 _ _ hinv12 h64 h_v40 h_a0 (by ns_tac) (by ns_tac) as ⟨v41, s13, hinv13, h_v41⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40
  store_step with Store.apply_rep s13 v41 a1 _ _ hinv13 h64 h_v41 h_a1 (by ns_tac) (by ns_tac) as ⟨v42, s14, hinv14, h_v42⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41
  store_step with Store.apply_rep s14 v39 v42 _ _ hinv14 h64 h_v39 h_v42 (by ns_tac) (by ns_tac) as ⟨v43, s15, hinv15, h_v43⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42
  store_step with Store.apply_rep s15 v35 v43 _ _ hinv15 h64 h_v35 h_v43 (by ns_tac) (by ns_tac) as ⟨v44, s16, hinv16, h_v44⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43
  step as ⟨e_v45, he_v45⟩
  store_step with CtorSpec.eo_re_2enone.construct s16 e_v45 (by rw [he_v45]; exact empty_args) hinv16 h64 as ⟨v45, s17, hinv17, h_v45⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44
  store_step with Store.apply_rep s17 v44 v45 _ _ hinv17 h64 h_v44 h_v45 (by ns_tac) (by ns_tac) as ⟨v46, s18, hinv18, h_v46⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45
  case_done hinv18 hG with h_v46 in EoCases.__eo_prog_re_inter_cstring_neg.case_0 using hn_a0 hn_a1 hn_a2 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v13 hn_v14 hn_v17 hn_v18 hn_v20 hn_v21 hn_v24 hn_v25 hn_v28 hn_v29 hn_v31 hn_v32

/-- logos's `__eo_prog_re_inter_cstring_neg` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fre_2dinter_2dcstring_2dneg.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) :
    __eo_prog_re_inter_cstring_neg x_a0 x_a1 x_a2 x_a3 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_re_inter_cstring_neg.case_0 x_a0 x_a1 x_a2 x_a3] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_re_inter_cstring_neg
  unfold EoCases.__eo_prog_re_inter_cstring_neg.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fre_2dinter_2dcstring_2dneg_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) :
    body_eo__24eo_5fprog_5fre_2dinter_2dcstring_2dneg s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_re_inter_cstring_neg x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fre_2dinter_2dcstring_2dneg.rust_eq x_a0 x_a1 x_a2 x_a3 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3)]
  unfold body_eo__24eo_5fprog_5fre_2dinter_2dcstring_2dneg
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fre_2dinter_2dcstring_2dneg_spec n ih s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 using hn_a0 hn_a1 hn_a2
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hc0 in EoCases.__eo_prog_re_inter_cstring_neg.case_0

theorem eo__24eo_5fprog_5fre_2dinter_2dcstring_2dneg_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fre_2dinter_2dcstring_2dneg.Spec n := by
  intro s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3
  unfold eo__24eo_5fprog_5fre_2dinter_2dcstring_2dneg
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fre_2dinter_2dcstring_2dneg s1 a0 a1 a2 a3) (fun s' t => Represents.rep s' t (__eo_prog_re_inter_cstring_neg x_a0 x_a1 x_a2 x_a3))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fre_2dinter_2dcstring_2dneg_spec m (ih m hm) s1 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fre_2dloop_2dneg_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fre_2dloop_2dneg s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_re_loop_neg.case_0 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_re_loop_neg.case_0 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fre_2dloop_2dneg more_0_eo__24eo_5fprog_5fre_2dloop_2dneg
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a3 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_re_loop_neg.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_re_loop_neg.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_re_loop_neg.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_re_loop_neg.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_re_loop_neg.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_re_loop_neg.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__3e.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_re_loop_neg.case_0
  pat_same v14 a0 with h_v14 h_a0 using hinv2 else hinv2 hG in EoCases.__eo_prog_re_loop_neg.case_0
  pat_same v11 a1 with h_v11 h_a1 using hinv2 else hinv2 hG in EoCases.__eo_prog_re_loop_neg.case_0
  store_step with Store.literal_boolean_spec s2 true hinv2 h64 as ⟨v16, s3, hinv3, h_v16⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15
  pat_same v4 v16 with h_v4 h_v16 using hinv3 else hinv3 hG in EoCases.__eo_prog_re_loop_neg.case_0
  step as ⟨e_v17, he_v17⟩
  store_step with CtorSpec.eo__3d.construct s3 e_v17 (by rw [he_v17]; exact empty_args) hinv3 h64 as ⟨v17, s4, hinv4, h_v17⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16
  step as ⟨e_v18, he_v18⟩
  store_step with CtorSpec.eo_re_2eloop.construct s4 e_v18 (by rw [he_v18]; rfl) h_a0 h_a1 hinv4 h64 as ⟨v18, s5, hinv5, h_v18⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17
  store_step with Store.apply_rep s5 v18 a2 _ _ hinv5 h64 h_v18 h_a2 (by ns_tac) (by ns_tac) as ⟨v19, s6, hinv6, h_v19⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18
  store_step with Store.apply_rep s6 v17 v19 _ _ hinv6 h64 h_v17 h_v19 (by ns_tac) (by ns_tac) as ⟨v20, s7, hinv7, h_v20⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19
  step as ⟨e_v21, he_v21⟩
  store_step with CtorSpec.eo_re_2enone.construct s7 e_v21 (by rw [he_v21]; exact empty_args) hinv7 h64 as ⟨v21, s8, hinv8, h_v21⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20
  store_step with Store.apply_rep s8 v20 v21 _ _ hinv8 h64 h_v20 h_v21 (by ns_tac) (by ns_tac) as ⟨v22, s9, hinv9, h_v22⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21
  case_done hinv9 hG with h_v22 in EoCases.__eo_prog_re_loop_neg.case_0 using hn_a0 hn_a1 hn_a2 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v13 hn_v14

/-- logos's `__eo_prog_re_loop_neg` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fre_2dloop_2dneg.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) :
    __eo_prog_re_loop_neg x_a0 x_a1 x_a2 x_a3 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_re_loop_neg.case_0 x_a0 x_a1 x_a2 x_a3] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_re_loop_neg
  unfold EoCases.__eo_prog_re_loop_neg.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fre_2dloop_2dneg_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) :
    body_eo__24eo_5fprog_5fre_2dloop_2dneg s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_re_loop_neg x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fre_2dloop_2dneg.rust_eq x_a0 x_a1 x_a2 x_a3 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3)]
  unfold body_eo__24eo_5fprog_5fre_2dloop_2dneg
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fre_2dloop_2dneg_spec n ih s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 using hn_a0 hn_a1 hn_a2
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hc0 in EoCases.__eo_prog_re_loop_neg.case_0

theorem eo__24eo_5fprog_5fre_2dloop_2dneg_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fre_2dloop_2dneg.Spec n := by
  intro s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3
  unfold eo__24eo_5fprog_5fre_2dloop_2dneg
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fre_2dloop_2dneg s1 a0 a1 a2 a3) (fun s' t => Represents.rep s' t (__eo_prog_re_loop_neg x_a0 x_a1 x_a2 x_a3))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fre_2dloop_2dneg_spec m (ih m hm) s1 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fre_2dloop_2dstar_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fre_2dloop_2dstar s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_re_loop_star.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_re_loop_star.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fre_2dloop_2dstar more_0_eo__24eo_5fprog_5fre_2dloop_2dstar more_1_eo__24eo_5fprog_5fre_2dloop_2dstar
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a3 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_re_loop_star.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_re_loop_star.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_re_loop_star.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_re_loop_star.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_re_loop_star.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_re_loop_star.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__3e_3d.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_re_loop_star.case_0
  pat_same v14 a1 with h_v14 h_a1 using hinv2 else hinv2 hG in EoCases.__eo_prog_re_loop_star.case_0
  pat_same v11 a0 with h_v11 h_a0 using hinv2 else hinv2 hG in EoCases.__eo_prog_re_loop_star.case_0
  store_step with Store.literal_boolean_spec s2 true hinv2 h64 as ⟨v16, s3, hinv3, h_v16⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15
  pat_same v4 v16 with h_v4 h_v16 using hinv3 else hinv3 hG in EoCases.__eo_prog_re_loop_star.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a4 as ⟨v18, x_v18, h_v18⟩ else hinv3 hG in EoCases.__eo_prog_re_loop_star.case_0
  pat_unapply h_v18 as ⟨v20, v21, x_v20, x_v21, h_v20, h_v21, hn_v20, hn_v21⟩ using hinv3 else hinv3 hG in EoCases.__eo_prog_re_loop_star.case_0
  pat_unapply h_v20 as ⟨v23, v24, x_v23, x_v24, h_v23, h_v24, hn_v23, hn_v24⟩ using hinv3 else hinv3 hG in EoCases.__eo_prog_re_loop_star.case_0
  step as ⟨e_v25, he_v25⟩
  store_step with CtorSpec.eo__3d.construct s3 e_v25 (by rw [he_v25]; exact empty_args) hinv3 h64 as ⟨v25, s4, hinv4, h_v25⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v18 h_v20 h_v21 h_v23 h_v24
  pat_same v23 v25 with h_v23 h_v25 using hinv4 else hinv4 hG in EoCases.__eo_prog_re_loop_star.case_0
  pat_unapply h_v24 as ⟨v27, v28, x_v27, x_v28, h_v27, h_v28, hn_v27, hn_v28⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_re_loop_star.case_0
  pat_unapply h_v27 as ⟨v30, v31, x_v30, x_v31, h_v30, h_v31, hn_v30, hn_v31⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_re_loop_star.case_0
  step as ⟨e_v32, he_v32⟩
  store_step with CtorSpec.eo__3e_3d.construct s4 e_v32 (by rw [he_v32]; exact empty_args) hinv4 h64 as ⟨v32, s5, hinv5, h_v32⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v18 h_v20 h_v21 h_v23 h_v24 h_v25 h_v27 h_v28 h_v30 h_v31
  pat_same v30 v32 with h_v30 h_v32 using hinv5 else hinv5 hG in EoCases.__eo_prog_re_loop_star.case_0
  pat_same v31 a1 with h_v31 h_a1 using hinv5 else hinv5 hG in EoCases.__eo_prog_re_loop_star.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s5 1#u32 (1) (by scalar_tac) hinv5 h64 as ⟨v33, s6, hinv6, h_v33⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v18 h_v20 h_v21 h_v23 h_v24 h_v25 h_v27 h_v28 h_v30 h_v31 h_v32
  pat_same v28 v33 with h_v28 h_v33 using hinv6 else hinv6 hG in EoCases.__eo_prog_re_loop_star.case_0
  store_step with Store.literal_boolean_spec s6 true hinv6 h64 as ⟨v34, s7, hinv7, h_v34⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v18 h_v20 h_v21 h_v23 h_v24 h_v25 h_v27 h_v28 h_v30 h_v31 h_v32 h_v33
  pat_same v21 v34 with h_v21 h_v34 using hinv7 else hinv7 hG in EoCases.__eo_prog_re_loop_star.case_0
  step as ⟨e_v35, he_v35⟩
  store_step with CtorSpec.eo__3d.construct s7 e_v35 (by rw [he_v35]; exact empty_args) hinv7 h64 as ⟨v35, s8, hinv8, h_v35⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v18 h_v20 h_v21 h_v23 h_v24 h_v25 h_v27 h_v28 h_v30 h_v31 h_v32 h_v33 h_v34
  step as ⟨e_v36, he_v36⟩
  store_step with CtorSpec.eo_re_2eloop.construct s8 e_v36 (by rw [he_v36]; rfl) h_a0 h_a1 hinv8 h64 as ⟨v36, s9, hinv9, h_v36⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v18 h_v20 h_v21 h_v23 h_v24 h_v25 h_v27 h_v28 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35
  step as ⟨e_v37, he_v37⟩
  store_step with CtorSpec.eo_re_2e_2a.construct s9 e_v37 (by rw [he_v37]; exact empty_args) hinv9 h64 as ⟨v37, s10, hinv10, h_v37⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v18 h_v20 h_v21 h_v23 h_v24 h_v25 h_v27 h_v28 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36
  store_step with Store.apply_rep s10 v37 a2 _ _ hinv10 h64 h_v37 h_a2 (by ns_tac) (by ns_tac) as ⟨v38, s11, hinv11, h_v38⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v18 h_v20 h_v21 h_v23 h_v24 h_v25 h_v27 h_v28 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37
  store_step with Store.apply_rep s11 v36 v38 _ _ hinv11 h64 h_v36 h_v38 (by ns_tac) (by ns_tac) as ⟨v39, s12, hinv12, h_v39⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v18 h_v20 h_v21 h_v23 h_v24 h_v25 h_v27 h_v28 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38
  store_step with Store.apply_rep s12 v35 v39 _ _ hinv12 h64 h_v35 h_v39 (by ns_tac) (by ns_tac) as ⟨v40, s13, hinv13, h_v40⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v18 h_v20 h_v21 h_v23 h_v24 h_v25 h_v27 h_v28 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39
  step as ⟨e_v41, he_v41⟩
  store_step with CtorSpec.eo_re_2e_2a.construct s13 e_v41 (by rw [he_v41]; exact empty_args) hinv13 h64 as ⟨v41, s14, hinv14, h_v41⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v18 h_v20 h_v21 h_v23 h_v24 h_v25 h_v27 h_v28 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40
  store_step with Store.apply_rep s14 v41 a2 _ _ hinv14 h64 h_v41 h_a2 (by ns_tac) (by ns_tac) as ⟨v42, s15, hinv15, h_v42⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v18 h_v20 h_v21 h_v23 h_v24 h_v25 h_v27 h_v28 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41
  store_step with Store.apply_rep s15 v40 v42 _ _ hinv15 h64 h_v40 h_v42 (by ns_tac) (by ns_tac) as ⟨v43, s16, hinv16, h_v43⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v18 h_v20 h_v21 h_v23 h_v24 h_v25 h_v27 h_v28 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42
  case_done hinv16 hG with h_v43 in EoCases.__eo_prog_re_loop_star.case_0 using hn_a0 hn_a1 hn_a2 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v13 hn_v14 hn_v20 hn_v21 hn_v23 hn_v24 hn_v27 hn_v28 hn_v30 hn_v31

/-- logos's `__eo_prog_re_loop_star` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fre_2dloop_2dstar.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) (hw_a4 : Valid.valid x_a4) :
    __eo_prog_re_loop_star x_a0 x_a1 x_a2 x_a3 x_a4 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_re_loop_star.case_0 x_a0 x_a1 x_a2 x_a3 x_a4] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_re_loop_star
  unfold EoCases.__eo_prog_re_loop_star.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fre_2dloop_2dstar_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) :
    body_eo__24eo_5fprog_5fre_2dloop_2dstar s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_re_loop_star x_a0 x_a1 x_a2 x_a3 x_a4)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fre_2dloop_2dstar.rust_eq x_a0 x_a1 x_a2 x_a3 x_a4 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3) (by valid_tac hinv h_a4)]
  unfold body_eo__24eo_5fprog_5fre_2dloop_2dstar
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fre_2dloop_2dstar_spec n ih s a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 using hn_a0 hn_a1 hn_a2
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hc0 in EoCases.__eo_prog_re_loop_star.case_0

theorem eo__24eo_5fprog_5fre_2dloop_2dstar_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fre_2dloop_2dstar.Spec n := by
  intro s a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4
  unfold eo__24eo_5fprog_5fre_2dloop_2dstar
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fre_2dloop_2dstar s1 a0 a1 a2 a3 a4) (fun s' t => Represents.rep s' t (__eo_prog_re_loop_star x_a0 x_a1 x_a2 x_a3 x_a4))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fre_2dloop_2dstar_spec m (ih m hm) s1 a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn) (by congr_one h_a4 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fre_2dopt_2delim_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fre_2dopt_2delim s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_re_opt_elim.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_re_opt_elim.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fre_2dopt_2delim more_0_eo__24eo_5fprog_5fre_2dopt_2delim
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_re_2eopt.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_v0 h_v1
  store_step with Store.apply_rep s3 v0 v2 _ _ hinv3 h64 h_v0 h_v2 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo_re_2eunion.construct s4 e_v4 (by rw [he_v4]; exact empty_args) hinv4 h64 as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo_str_2eto_5fre.construct s5 e_v5 (by rw [he_v5]; exact empty_args) hinv5 h64 as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s6 _ _ rfl hinv6 h64 as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with Store.apply_rep s7 v5 v6 _ _ hinv7 h64 h_v5 h_v6 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  store_step with Store.apply_rep s8 v4 v7 _ _ hinv8 h64 h_v4 h_v7 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_re_2eunion.construct s9 e_v9 (by rw [he_v9]; exact empty_args) hinv9 h64 as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
  store_step with Store.apply_rep s10 v9 a0 _ _ hinv10 h64 h_v9 h_a0 (by ns_tac) (by ns_tac) as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  step as ⟨e_v11, he_v11⟩
  store_step with CtorSpec.eo_re_2enone.construct s11 e_v11 (by rw [he_v11]; exact empty_args) hinv11 h64 as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
  store_step with Store.apply_rep s12 v10 v11 _ _ hinv12 h64 h_v10 h_v11 (by ns_tac) (by ns_tac) as ⟨v12, s13, hinv13, h_v12⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11
  store_step with Store.apply_rep s13 v8 v12 _ _ hinv13 h64 h_v8 h_v12 (by ns_tac) (by ns_tac) as ⟨v13, s14, hinv14, h_v13⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
  store_step with Store.apply_rep s14 v3 v13 _ _ hinv14 h64 h_v3 h_v13 (by ns_tac) (by ns_tac) as ⟨v14, s15, hinv15, h_v14⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13
  case_done hinv15 hG with h_v14 in EoCases.__eo_prog_re_opt_elim.case_0 using hn_a0

/-- logos's `__eo_prog_re_opt_elim` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fre_2dopt_2delim.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_re_opt_elim x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_re_opt_elim.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_re_opt_elim
  unfold EoCases.__eo_prog_re_opt_elim.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fre_2dopt_2delim_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fre_2dopt_2delim s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_re_opt_elim x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fre_2dopt_2delim.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fre_2dopt_2delim
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fre_2dopt_2delim_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_re_opt_elim.case_0

theorem eo__24eo_5fprog_5fre_2dopt_2delim_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fre_2dopt_2delim.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fre_2dopt_2delim
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fre_2dopt_2delim s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_re_opt_elim x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fre_2dopt_2delim_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fre_2dplus_2delim_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fre_2dplus_2delim s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_re_plus_elim.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_re_plus_elim.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fre_2dplus_2delim more_0_eo__24eo_5fprog_5fre_2dplus_2delim
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_re_2e_2b.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_v0 h_v1
  store_step with Store.apply_rep s3 v0 v2 _ _ hinv3 h64 h_v0 h_v2 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo_re_2e_2b_2b.construct s4 e_v4 (by rw [he_v4]; exact empty_args) hinv4 h64 as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3
  store_step with Store.apply_rep s5 v4 a0 _ _ hinv5 h64 h_v4 h_a0 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_re_2e_2b_2b.construct s6 e_v6 (by rw [he_v6]; exact empty_args) hinv6 h64 as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo_re_2e_2a.construct s7 e_v7 (by rw [he_v7]; exact empty_args) hinv7 h64 as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  store_step with Store.apply_rep s8 v7 a0 _ _ hinv8 h64 h_v7 h_a0 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  store_step with Store.apply_rep s9 v6 v8 _ _ hinv9 h64 h_v6 h_v8 (by ns_tac) (by ns_tac) as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo_str_2eto_5fre.construct s10 e_v10 (by rw [he_v10]; exact empty_args) hinv10 h64 as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s11 _ _ rfl hinv11 h64 as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
  store_step with Store.apply_rep s12 v10 v11 _ _ hinv12 h64 h_v10 h_v11 (by ns_tac) (by ns_tac) as ⟨v12, s13, hinv13, h_v12⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11
  store_step with Store.apply_rep s13 v9 v12 _ _ hinv13 h64 h_v9 h_v12 (by ns_tac) (by ns_tac) as ⟨v13, s14, hinv14, h_v13⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
  store_step with Store.apply_rep s14 v5 v13 _ _ hinv14 h64 h_v5 h_v13 (by ns_tac) (by ns_tac) as ⟨v14, s15, hinv15, h_v14⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13
  store_step with Store.apply_rep s15 v3 v14 _ _ hinv15 h64 h_v3 h_v14 (by ns_tac) (by ns_tac) as ⟨v15, s16, hinv16, h_v15⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14
  case_done hinv16 hG with h_v15 in EoCases.__eo_prog_re_plus_elim.case_0 using hn_a0

/-- logos's `__eo_prog_re_plus_elim` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fre_2dplus_2delim.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_re_plus_elim x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_re_plus_elim.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_re_plus_elim
  unfold EoCases.__eo_prog_re_plus_elim.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fre_2dplus_2delim_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fre_2dplus_2delim s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_re_plus_elim x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fre_2dplus_2delim.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fre_2dplus_2delim
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fre_2dplus_2delim_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_re_plus_elim.case_0

theorem eo__24eo_5fprog_5fre_2dplus_2delim_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fre_2dplus_2delim.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fre_2dplus_2delim
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fre_2dplus_2delim s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_re_plus_elim x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fre_2dplus_2delim_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fre_2drange_2demp_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fre_2drange_2demp s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_re_range_emp.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_re_range_emp.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fre_2drange_2demp more_0_eo__24eo_5fprog_5fre_2drange_2demp more_1_eo__24eo_5fprog_5fre_2drange_2demp more_2_eo__24eo_5fprog_5fre_2drange_2demp
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a2 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_re_range_emp.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_re_range_emp.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_re_range_emp.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_re_range_emp.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_re_range_emp.case_0
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo_str_2elen.construct s1 e_v12 (by rw [he_v12]; exact empty_args) hinv1 h64 as ⟨v12, s2, hinv2, h_v12⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11
  pat_same v10 v12 with h_v10 h_v12 using hinv2 else hinv2 hG in EoCases.__eo_prog_re_range_emp.case_0
  pat_same v11 a0 with h_v11 h_a0 using hinv2 else hinv2 hG in EoCases.__eo_prog_re_range_emp.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s2 1#u32 (1) (by scalar_tac) hinv2 h64 as ⟨v13, s3, hinv3, h_v13⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12
  pat_same v4 v13 with h_v4 h_v13 using hinv3 else hinv3 hG in EoCases.__eo_prog_re_range_emp.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a3 as ⟨v15, x_v15, h_v15⟩ else hinv3 hG in EoCases.__eo_prog_re_range_emp.case_0
  pat_unapply h_v15 as ⟨v17, v18, x_v17, x_v18, h_v17, h_v18, hn_v17, hn_v18⟩ using hinv3 else hinv3 hG in EoCases.__eo_prog_re_range_emp.case_0
  pat_unapply h_v17 as ⟨v20, v21, x_v20, x_v21, h_v20, h_v21, hn_v20, hn_v21⟩ using hinv3 else hinv3 hG in EoCases.__eo_prog_re_range_emp.case_0
  step as ⟨e_v22, he_v22⟩
  store_step with CtorSpec.eo__3d.construct s3 e_v22 (by rw [he_v22]; exact empty_args) hinv3 h64 as ⟨v22, s4, hinv4, h_v22⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v15 h_v17 h_v18 h_v20 h_v21
  pat_same v20 v22 with h_v20 h_v22 using hinv4 else hinv4 hG in EoCases.__eo_prog_re_range_emp.case_0
  pat_unapply h_v21 as ⟨v24, v25, x_v24, x_v25, h_v24, h_v25, hn_v24, hn_v25⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_re_range_emp.case_0
  step as ⟨e_v26, he_v26⟩
  store_step with CtorSpec.eo_str_2elen.construct s4 e_v26 (by rw [he_v26]; exact empty_args) hinv4 h64 as ⟨v26, s5, hinv5, h_v26⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25
  pat_same v24 v26 with h_v24 h_v26 using hinv5 else hinv5 hG in EoCases.__eo_prog_re_range_emp.case_0
  pat_same v25 a1 with h_v25 h_a1 using hinv5 else hinv5 hG in EoCases.__eo_prog_re_range_emp.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s5 1#u32 (1) (by scalar_tac) hinv5 h64 as ⟨v27, s6, hinv6, h_v27⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26
  pat_same v18 v27 with h_v18 h_v27 using hinv6 else hinv6 hG in EoCases.__eo_prog_re_range_emp.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a4 as ⟨v29, x_v29, h_v29⟩ else hinv6 hG in EoCases.__eo_prog_re_range_emp.case_0
  pat_unapply h_v29 as ⟨v31, v32, x_v31, x_v32, h_v31, h_v32, hn_v31, hn_v32⟩ using hinv6 else hinv6 hG in EoCases.__eo_prog_re_range_emp.case_0
  pat_unapply h_v31 as ⟨v34, v35, x_v34, x_v35, h_v34, h_v35, hn_v34, hn_v35⟩ using hinv6 else hinv6 hG in EoCases.__eo_prog_re_range_emp.case_0
  step as ⟨e_v36, he_v36⟩
  store_step with CtorSpec.eo__3d.construct s6 e_v36 (by rw [he_v36]; exact empty_args) hinv6 h64 as ⟨v36, s7, hinv7, h_v36⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v27 h_v29 h_v31 h_v32 h_v34 h_v35
  pat_same v34 v36 with h_v34 h_v36 using hinv7 else hinv7 hG in EoCases.__eo_prog_re_range_emp.case_0
  pat_unapply h_v35 as ⟨v38, v39, x_v38, x_v39, h_v38, h_v39, hn_v38, hn_v39⟩ using hinv7 else hinv7 hG in EoCases.__eo_prog_re_range_emp.case_0
  pat_unapply h_v38 as ⟨v41, v42, x_v41, x_v42, h_v41, h_v42, hn_v41, hn_v42⟩ using hinv7 else hinv7 hG in EoCases.__eo_prog_re_range_emp.case_0
  step as ⟨e_v43, he_v43⟩
  store_step with CtorSpec.eo__3c.construct s7 e_v43 (by rw [he_v43]; exact empty_args) hinv7 h64 as ⟨v43, s8, hinv8, h_v43⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v27 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v41 h_v42
  pat_same v41 v43 with h_v41 h_v43 using hinv8 else hinv8 hG in EoCases.__eo_prog_re_range_emp.case_0
  pat_unapply h_v42 as ⟨v45, v46, x_v45, x_v46, h_v45, h_v46, hn_v45, hn_v46⟩ using hinv8 else hinv8 hG in EoCases.__eo_prog_re_range_emp.case_0
  step as ⟨e_v47, he_v47⟩
  store_step with CtorSpec.eo_str_2eto_5fcode.construct s8 e_v47 (by rw [he_v47]; exact empty_args) hinv8 h64 as ⟨v47, s9, hinv9, h_v47⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v27 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v41 h_v42 h_v43 h_v45 h_v46
  pat_same v45 v47 with h_v45 h_v47 using hinv9 else hinv9 hG in EoCases.__eo_prog_re_range_emp.case_0
  pat_same v46 a1 with h_v46 h_a1 using hinv9 else hinv9 hG in EoCases.__eo_prog_re_range_emp.case_0
  pat_unapply h_v39 as ⟨v49, v50, x_v49, x_v50, h_v49, h_v50, hn_v49, hn_v50⟩ using hinv9 else hinv9 hG in EoCases.__eo_prog_re_range_emp.case_0
  step as ⟨e_v51, he_v51⟩
  store_step with CtorSpec.eo_str_2eto_5fcode.construct s9 e_v51 (by rw [he_v51]; exact empty_args) hinv9 h64 as ⟨v51, s10, hinv10, h_v51⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v27 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v41 h_v42 h_v43 h_v45 h_v46 h_v47 h_v49 h_v50
  pat_same v49 v51 with h_v49 h_v51 using hinv10 else hinv10 hG in EoCases.__eo_prog_re_range_emp.case_0
  pat_same v50 a0 with h_v50 h_a0 using hinv10 else hinv10 hG in EoCases.__eo_prog_re_range_emp.case_0
  store_step with Store.literal_boolean_spec s10 true hinv10 h64 as ⟨v52, s11, hinv11, h_v52⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v27 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v41 h_v42 h_v43 h_v45 h_v46 h_v47 h_v49 h_v50 h_v51
  pat_same v32 v52 with h_v32 h_v52 using hinv11 else hinv11 hG in EoCases.__eo_prog_re_range_emp.case_0
  step as ⟨e_v53, he_v53⟩
  store_step with CtorSpec.eo__3d.construct s11 e_v53 (by rw [he_v53]; exact empty_args) hinv11 h64 as ⟨v53, s12, hinv12, h_v53⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v27 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v41 h_v42 h_v43 h_v45 h_v46 h_v47 h_v49 h_v50 h_v51 h_v52
  step as ⟨e_v54, he_v54⟩
  store_step with CtorSpec.eo_re_2erange.construct s12 e_v54 (by rw [he_v54]; exact empty_args) hinv12 h64 as ⟨v54, s13, hinv13, h_v54⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v27 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v41 h_v42 h_v43 h_v45 h_v46 h_v47 h_v49 h_v50 h_v51 h_v52 h_v53
  store_step with Store.apply_rep s13 v54 a0 _ _ hinv13 h64 h_v54 h_a0 (by ns_tac) (by ns_tac) as ⟨v55, s14, hinv14, h_v55⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v27 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v41 h_v42 h_v43 h_v45 h_v46 h_v47 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54
  store_step with Store.apply_rep s14 v55 a1 _ _ hinv14 h64 h_v55 h_a1 (by ns_tac) (by ns_tac) as ⟨v56, s15, hinv15, h_v56⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v27 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v41 h_v42 h_v43 h_v45 h_v46 h_v47 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55
  store_step with Store.apply_rep s15 v53 v56 _ _ hinv15 h64 h_v53 h_v56 (by ns_tac) (by ns_tac) as ⟨v57, s16, hinv16, h_v57⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v27 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v41 h_v42 h_v43 h_v45 h_v46 h_v47 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56
  step as ⟨e_v58, he_v58⟩
  store_step with CtorSpec.eo_re_2enone.construct s16 e_v58 (by rw [he_v58]; exact empty_args) hinv16 h64 as ⟨v58, s17, hinv17, h_v58⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v27 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v41 h_v42 h_v43 h_v45 h_v46 h_v47 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57
  store_step with Store.apply_rep s17 v57 v58 _ _ hinv17 h64 h_v57 h_v58 (by ns_tac) (by ns_tac) as ⟨v59, s18, hinv18, h_v59⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v27 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v41 h_v42 h_v43 h_v45 h_v46 h_v47 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58
  case_done hinv18 hG with h_v59 in EoCases.__eo_prog_re_range_emp.case_0 using hn_a0 hn_a1 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v17 hn_v18 hn_v20 hn_v21 hn_v24 hn_v25 hn_v31 hn_v32 hn_v34 hn_v35 hn_v38 hn_v39 hn_v41 hn_v42 hn_v45 hn_v46 hn_v49 hn_v50

/-- logos's `__eo_prog_re_range_emp` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fre_2drange_2demp.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) (hw_a4 : Valid.valid x_a4) :
    __eo_prog_re_range_emp x_a0 x_a1 x_a2 x_a3 x_a4 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_re_range_emp.case_0 x_a0 x_a1 x_a2 x_a3 x_a4] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_re_range_emp
  unfold EoCases.__eo_prog_re_range_emp.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fre_2drange_2demp_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) :
    body_eo__24eo_5fprog_5fre_2drange_2demp s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_re_range_emp x_a0 x_a1 x_a2 x_a3 x_a4)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fre_2drange_2demp.rust_eq x_a0 x_a1 x_a2 x_a3 x_a4 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3) (by valid_tac hinv h_a4)]
  unfold body_eo__24eo_5fprog_5fre_2drange_2demp
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fre_2drange_2demp_spec n ih s a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_re_range_emp.case_0

theorem eo__24eo_5fprog_5fre_2drange_2demp_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fre_2drange_2demp.Spec n := by
  intro s a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4
  unfold eo__24eo_5fprog_5fre_2drange_2demp
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fre_2drange_2demp s1 a0 a1 a2 a3 a4) (fun s' t => Represents.rep s' t (__eo_prog_re_range_emp x_a0 x_a1 x_a2 x_a3 x_a4))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fre_2drange_2demp_spec m (ih m hm) s1 a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn) (by congr_one h_a4 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

end pathos_compiled_checker
