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

theorem case_0_eo__24eo_5fprog_5fbv_2dite_2dequal_2dcond_2d1_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fbv_2dite_2dequal_2dcond_2d1 s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_bv_ite_equal_cond_1.case_0 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_bv_ite_equal_cond_1.case_0 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fbv_2dite_2dequal_2dcond_2d1 more_0_eo__24eo_5fprog_5fbv_2dite_2dequal_2dcond_2d1
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_bvite.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_bvite.construct s3 e_v3 (by rw [he_v3]; exact empty_args) hinv3 h64 as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v3 a0 _ _ hinv4 h64 h_v3 h_a0 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3
  store_step with Store.apply_rep s5 v4 a1 _ _ hinv5 h64 h_v4 h_a1 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4
  store_step with Store.apply_rep s6 v5 a2 _ _ hinv6 h64 h_v5 h_a2 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with Store.apply_rep s7 v2 v6 _ _ hinv7 h64 h_v2 h_v6 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  store_step with Store.apply_rep s8 v7 a3 _ _ hinv8 h64 h_v7 h_a3 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  store_step with Store.apply_rep s9 v0 v8 _ _ hinv9 h64 h_v0 h_v8 (by ns_tac) (by ns_tac) as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo_bvite.construct s10 e_v10 (by rw [he_v10]; exact empty_args) hinv10 h64 as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  store_step with Store.apply_rep s11 v10 a0 _ _ hinv11 h64 h_v10 h_a0 (by ns_tac) (by ns_tac) as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
  store_step with Store.apply_rep s12 v11 a1 _ _ hinv12 h64 h_v11 h_a1 (by ns_tac) (by ns_tac) as ⟨v12, s13, hinv13, h_v12⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11
  store_step with Store.apply_rep s13 v12 a3 _ _ hinv13 h64 h_v12 h_a3 (by ns_tac) (by ns_tac) as ⟨v13, s14, hinv14, h_v13⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
  store_step with Store.apply_rep s14 v9 v13 _ _ hinv14 h64 h_v9 h_v13 (by ns_tac) (by ns_tac) as ⟨v14, s15, hinv15, h_v14⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13
  case_done hinv15 hG with h_v14 in EoCases.__eo_prog_bv_ite_equal_cond_1.case_0 using hn_a0 hn_a1 hn_a2 hn_a3

/-- logos's `__eo_prog_bv_ite_equal_cond_1` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fbv_2dite_2dequal_2dcond_2d1.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) :
    __eo_prog_bv_ite_equal_cond_1 x_a0 x_a1 x_a2 x_a3 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_bv_ite_equal_cond_1.case_0 x_a0 x_a1 x_a2 x_a3] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_bv_ite_equal_cond_1
  unfold EoCases.__eo_prog_bv_ite_equal_cond_1.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fbv_2dite_2dequal_2dcond_2d1_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) :
    body_eo__24eo_5fprog_5fbv_2dite_2dequal_2dcond_2d1 s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_ite_equal_cond_1 x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fbv_2dite_2dequal_2dcond_2d1.rust_eq x_a0 x_a1 x_a2 x_a3 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3)]
  unfold body_eo__24eo_5fprog_5fbv_2dite_2dequal_2dcond_2d1
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  stuck_check h_a3 : x_a3 as hn_a3 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fbv_2dite_2dequal_2dcond_2d1_spec n ih s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2 hn_a3
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 using hn_a0 hn_a1 hn_a2 hn_a3
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hn_a3 hc0 in EoCases.__eo_prog_bv_ite_equal_cond_1.case_0

theorem eo__24eo_5fprog_5fbv_2dite_2dequal_2dcond_2d1_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fbv_2dite_2dequal_2dcond_2d1.Spec n := by
  intro s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3
  unfold eo__24eo_5fprog_5fbv_2dite_2dequal_2dcond_2d1
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fbv_2dite_2dequal_2dcond_2d1 s1 a0 a1 a2 a3) (fun s' t => Represents.rep s' t (__eo_prog_bv_ite_equal_cond_1 x_a0 x_a1 x_a2 x_a3))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fbv_2dite_2dequal_2dcond_2d1_spec m (ih m hm) s1 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fbv_2dite_2dequal_2dcond_2d2_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fbv_2dite_2dequal_2dcond_2d2 s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_bv_ite_equal_cond_2.case_0 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_bv_ite_equal_cond_2.case_0 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fbv_2dite_2dequal_2dcond_2d2 more_0_eo__24eo_5fprog_5fbv_2dite_2dequal_2dcond_2d2
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_bvite.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a1 _ _ hinv3 h64 h_v2 h_a1 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo_bvite.construct s4 e_v4 (by rw [he_v4]; exact empty_args) hinv4 h64 as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3
  store_step with Store.apply_rep s5 v4 a0 _ _ hinv5 h64 h_v4 h_a0 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4
  store_step with Store.apply_rep s6 v5 a2 _ _ hinv6 h64 h_v5 h_a2 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with Store.apply_rep s7 v6 a3 _ _ hinv7 h64 h_v6 h_a3 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  store_step with Store.apply_rep s8 v3 v7 _ _ hinv8 h64 h_v3 h_v7 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  store_step with Store.apply_rep s9 v0 v8 _ _ hinv9 h64 h_v0 h_v8 (by ns_tac) (by ns_tac) as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo_bvite.construct s10 e_v10 (by rw [he_v10]; exact empty_args) hinv10 h64 as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  store_step with Store.apply_rep s11 v10 a0 _ _ hinv11 h64 h_v10 h_a0 (by ns_tac) (by ns_tac) as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
  store_step with Store.apply_rep s12 v11 a1 _ _ hinv12 h64 h_v11 h_a1 (by ns_tac) (by ns_tac) as ⟨v12, s13, hinv13, h_v12⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11
  store_step with Store.apply_rep s13 v12 a3 _ _ hinv13 h64 h_v12 h_a3 (by ns_tac) (by ns_tac) as ⟨v13, s14, hinv14, h_v13⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
  store_step with Store.apply_rep s14 v9 v13 _ _ hinv14 h64 h_v9 h_v13 (by ns_tac) (by ns_tac) as ⟨v14, s15, hinv15, h_v14⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13
  case_done hinv15 hG with h_v14 in EoCases.__eo_prog_bv_ite_equal_cond_2.case_0 using hn_a0 hn_a1 hn_a2 hn_a3

/-- logos's `__eo_prog_bv_ite_equal_cond_2` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fbv_2dite_2dequal_2dcond_2d2.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) :
    __eo_prog_bv_ite_equal_cond_2 x_a0 x_a1 x_a2 x_a3 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_bv_ite_equal_cond_2.case_0 x_a0 x_a1 x_a2 x_a3] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_bv_ite_equal_cond_2
  unfold EoCases.__eo_prog_bv_ite_equal_cond_2.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fbv_2dite_2dequal_2dcond_2d2_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) :
    body_eo__24eo_5fprog_5fbv_2dite_2dequal_2dcond_2d2 s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_ite_equal_cond_2 x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fbv_2dite_2dequal_2dcond_2d2.rust_eq x_a0 x_a1 x_a2 x_a3 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3)]
  unfold body_eo__24eo_5fprog_5fbv_2dite_2dequal_2dcond_2d2
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  stuck_check h_a3 : x_a3 as hn_a3 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fbv_2dite_2dequal_2dcond_2d2_spec n ih s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2 hn_a3
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 using hn_a0 hn_a1 hn_a2 hn_a3
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hn_a3 hc0 in EoCases.__eo_prog_bv_ite_equal_cond_2.case_0

theorem eo__24eo_5fprog_5fbv_2dite_2dequal_2dcond_2d2_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fbv_2dite_2dequal_2dcond_2d2.Spec n := by
  intro s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3
  unfold eo__24eo_5fprog_5fbv_2dite_2dequal_2dcond_2d2
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fbv_2dite_2dequal_2dcond_2d2 s1 a0 a1 a2 a3) (fun s' t => Represents.rep s' t (__eo_prog_bv_ite_equal_cond_2 x_a0 x_a1 x_a2 x_a3))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fbv_2dite_2dequal_2dcond_2d2_spec m (ih m hm) s1 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fbv_2dite_2dequal_2dcond_2d3_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) (hn_a4 : x_a4 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fbv_2dite_2dequal_2dcond_2d3 s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_bv_ite_equal_cond_3.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_bv_ite_equal_cond_3.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fbv_2dite_2dequal_2dcond_2d3 more_0_eo__24eo_5fprog_5fbv_2dite_2dequal_2dcond_2d3
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_bvite.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v0
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v0 h_v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_bvite.construct s3 e_v3 (by rw [he_v3]; exact empty_args) hinv3 h64 as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v3 a0 _ _ hinv4 h64 h_v3 h_a0 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v0 h_v1 h_v2 h_v3
  store_step with Store.apply_rep s5 v4 a1 _ _ hinv5 h64 h_v4 h_a1 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v0 h_v1 h_v2 h_v3 h_v4
  store_step with Store.apply_rep s6 v5 a2 _ _ hinv6 h64 h_v5 h_a2 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with Store.apply_rep s7 v2 v6 _ _ hinv7 h64 h_v2 h_v6 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo_bvite.construct s8 e_v8 (by rw [he_v8]; exact empty_args) hinv8 h64 as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  store_step with Store.apply_rep s9 v8 a0 _ _ hinv9 h64 h_v8 h_a0 (by ns_tac) (by ns_tac) as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
  store_step with Store.apply_rep s10 v9 a3 _ _ hinv10 h64 h_v9 h_a3 (by ns_tac) (by ns_tac) as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  store_step with Store.apply_rep s11 v10 a4 _ _ hinv11 h64 h_v10 h_a4 (by ns_tac) (by ns_tac) as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
  store_step with Store.apply_rep s12 v7 v11 _ _ hinv12 h64 h_v7 h_v11 (by ns_tac) (by ns_tac) as ⟨v12, s13, hinv13, h_v12⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11
  store_step with Store.apply_rep s13 v0 v12 _ _ hinv13 h64 h_v0 h_v12 (by ns_tac) (by ns_tac) as ⟨v13, s14, hinv14, h_v13⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo_bvite.construct s14 e_v14 (by rw [he_v14]; exact empty_args) hinv14 h64 as ⟨v14, s15, hinv15, h_v14⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13
  store_step with Store.apply_rep s15 v14 a0 _ _ hinv15 h64 h_v14 h_a0 (by ns_tac) (by ns_tac) as ⟨v15, s16, hinv16, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14
  store_step with Store.apply_rep s16 v15 a1 _ _ hinv16 h64 h_v15 h_a1 (by ns_tac) (by ns_tac) as ⟨v16, s17, hinv17, h_v16⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15
  store_step with Store.apply_rep s17 v16 a4 _ _ hinv17 h64 h_v16 h_a4 (by ns_tac) (by ns_tac) as ⟨v17, s18, hinv18, h_v17⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16
  store_step with Store.apply_rep s18 v13 v17 _ _ hinv18 h64 h_v13 h_v17 (by ns_tac) (by ns_tac) as ⟨v18, s19, hinv19, h_v18⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17
  case_done hinv19 hG with h_v18 in EoCases.__eo_prog_bv_ite_equal_cond_3.case_0 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4

/-- logos's `__eo_prog_bv_ite_equal_cond_3` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fbv_2dite_2dequal_2dcond_2d3.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) (hw_a4 : Valid.valid x_a4) :
    __eo_prog_bv_ite_equal_cond_3 x_a0 x_a1 x_a2 x_a3 x_a4 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else if x_a4 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_bv_ite_equal_cond_3.case_0 x_a0 x_a1 x_a2 x_a3 x_a4] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_bv_ite_equal_cond_3
  unfold EoCases.__eo_prog_bv_ite_equal_cond_3.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fbv_2dite_2dequal_2dcond_2d3_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) :
    body_eo__24eo_5fprog_5fbv_2dite_2dequal_2dcond_2d3 s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_ite_equal_cond_3 x_a0 x_a1 x_a2 x_a3 x_a4)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fbv_2dite_2dequal_2dcond_2d3.rust_eq x_a0 x_a1 x_a2 x_a3 x_a4 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3) (by valid_tac hinv h_a4)]
  unfold body_eo__24eo_5fprog_5fbv_2dite_2dequal_2dcond_2d3
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  stuck_check h_a3 : x_a3 as hn_a3 else hinv hG
  stuck_check h_a4 : x_a4 as hn_a4 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fbv_2dite_2dequal_2dcond_2d3_spec n ih s a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 hn_a0 hn_a1 hn_a2 hn_a3 hn_a4
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hc0 in EoCases.__eo_prog_bv_ite_equal_cond_3.case_0

theorem eo__24eo_5fprog_5fbv_2dite_2dequal_2dcond_2d3_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fbv_2dite_2dequal_2dcond_2d3.Spec n := by
  intro s a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4
  unfold eo__24eo_5fprog_5fbv_2dite_2dequal_2dcond_2d3
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fbv_2dite_2dequal_2dcond_2d3 s1 a0 a1 a2 a3 a4) (fun s' t => Represents.rep s' t (__eo_prog_bv_ite_equal_cond_3 x_a0 x_a1 x_a2 x_a3 x_a4))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fbv_2dite_2dequal_2dcond_2d3_spec m (ih m hm) s1 a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn) (by congr_one h_a4 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fbv_2dite_2dmerge_2delse_2delse_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fbv_2dite_2dmerge_2delse_2delse s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_bv_ite_merge_else_else.case_0 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_bv_ite_merge_else_else.case_0 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fbv_2dite_2dmerge_2delse_2delse more_0_eo__24eo_5fprog_5fbv_2dite_2dmerge_2delse_2delse
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_bvite.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a3 _ _ hinv3 h64 h_v2 h_a3 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo_bvite.construct s4 e_v4 (by rw [he_v4]; exact empty_args) hinv4 h64 as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3
  store_step with Store.apply_rep s5 v4 a1 _ _ hinv5 h64 h_v4 h_a1 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4
  store_step with Store.apply_rep s6 v5 a2 _ _ hinv6 h64 h_v5 h_a2 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with Store.apply_rep s7 v6 a3 _ _ hinv7 h64 h_v6 h_a3 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  store_step with Store.apply_rep s8 v3 v7 _ _ hinv8 h64 h_v3 h_v7 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  store_step with Store.apply_rep s9 v0 v8 _ _ hinv9 h64 h_v0 h_v8 (by ns_tac) (by ns_tac) as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo_bvite.construct s10 e_v10 (by rw [he_v10]; exact empty_args) hinv10 h64 as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  step as ⟨e_v11, he_v11⟩
  store_step with CtorSpec.eo_bvand.construct s11 e_v11 (by rw [he_v11]; exact empty_args) hinv11 h64 as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo_bvnot.construct s12 e_v12 (by rw [he_v12]; exact empty_args) hinv12 h64 as ⟨v12, s13, hinv13, h_v12⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11
  store_step with Store.apply_rep s13 v12 a0 _ _ hinv13 h64 h_v12 h_a0 (by ns_tac) (by ns_tac) as ⟨v13, s14, hinv14, h_v13⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
  store_step with Store.apply_rep s14 v11 v13 _ _ hinv14 h64 h_v11 h_v13 (by ns_tac) (by ns_tac) as ⟨v14, s15, hinv15, h_v14⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo_bvand.construct s15 e_v15 (by rw [he_v15]; exact empty_args) hinv15 h64 as ⟨v15, s16, hinv16, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14
  store_step with Store.apply_rep s16 v15 a1 _ _ hinv16 h64 h_v15 h_a1 (by ns_tac) (by ns_tac) as ⟨v16, s17, hinv17, h_v16⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s17 1#u32 1#u32 (1) (1) rfl rfl (by unfold Tree.okBv; norm_num) hinv17 h64 as ⟨v17, s18, hinv18, h_v17⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16
  store_step with Store.apply_rep s18 v16 v17 _ _ hinv18 h64 h_v16 h_v17 (by ns_tac) (by ns_tac) as ⟨v18, s19, hinv19, h_v18⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17
  store_step with Store.apply_rep s19 v14 v18 _ _ hinv19 h64 h_v14 h_v18 (by ns_tac) (by ns_tac) as ⟨v19, s20, hinv20, h_v19⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18
  store_step with Store.apply_rep s20 v10 v19 _ _ hinv20 h64 h_v10 h_v19 (by ns_tac) (by ns_tac) as ⟨v20, s21, hinv21, h_v20⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19
  store_step with Store.apply_rep s21 v20 a2 _ _ hinv21 h64 h_v20 h_a2 (by ns_tac) (by ns_tac) as ⟨v21, s22, hinv22, h_v21⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20
  store_step with Store.apply_rep s22 v21 a3 _ _ hinv22 h64 h_v21 h_a3 (by ns_tac) (by ns_tac) as ⟨v22, s23, hinv23, h_v22⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21
  store_step with Store.apply_rep s23 v9 v22 _ _ hinv23 h64 h_v9 h_v22 (by ns_tac) (by ns_tac) as ⟨v23, s24, hinv24, h_v23⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22
  case_done hinv24 hG with h_v23 in EoCases.__eo_prog_bv_ite_merge_else_else.case_0 using hn_a0 hn_a1 hn_a2 hn_a3

/-- logos's `__eo_prog_bv_ite_merge_else_else` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fbv_2dite_2dmerge_2delse_2delse.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) :
    __eo_prog_bv_ite_merge_else_else x_a0 x_a1 x_a2 x_a3 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_bv_ite_merge_else_else.case_0 x_a0 x_a1 x_a2 x_a3] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_bv_ite_merge_else_else
  unfold EoCases.__eo_prog_bv_ite_merge_else_else.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fbv_2dite_2dmerge_2delse_2delse_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) :
    body_eo__24eo_5fprog_5fbv_2dite_2dmerge_2delse_2delse s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_ite_merge_else_else x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fbv_2dite_2dmerge_2delse_2delse.rust_eq x_a0 x_a1 x_a2 x_a3 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3)]
  unfold body_eo__24eo_5fprog_5fbv_2dite_2dmerge_2delse_2delse
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  stuck_check h_a3 : x_a3 as hn_a3 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fbv_2dite_2dmerge_2delse_2delse_spec n ih s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2 hn_a3
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 using hn_a0 hn_a1 hn_a2 hn_a3
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hn_a3 hc0 in EoCases.__eo_prog_bv_ite_merge_else_else.case_0

theorem eo__24eo_5fprog_5fbv_2dite_2dmerge_2delse_2delse_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fbv_2dite_2dmerge_2delse_2delse.Spec n := by
  intro s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3
  unfold eo__24eo_5fprog_5fbv_2dite_2dmerge_2delse_2delse
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fbv_2dite_2dmerge_2delse_2delse s1 a0 a1 a2 a3) (fun s' t => Represents.rep s' t (__eo_prog_bv_ite_merge_else_else x_a0 x_a1 x_a2 x_a3))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fbv_2dite_2dmerge_2delse_2delse_spec m (ih m hm) s1 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fbv_2dite_2dmerge_2delse_2dif_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fbv_2dite_2dmerge_2delse_2dif s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_bv_ite_merge_else_if.case_0 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_bv_ite_merge_else_if.case_0 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fbv_2dite_2dmerge_2delse_2dif more_0_eo__24eo_5fprog_5fbv_2dite_2dmerge_2delse_2dif
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_bvite.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_bvite.construct s3 e_v3 (by rw [he_v3]; exact empty_args) hinv3 h64 as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v3 a1 _ _ hinv4 h64 h_v3 h_a1 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3
  store_step with Store.apply_rep s5 v4 a2 _ _ hinv5 h64 h_v4 h_a2 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4
  store_step with Store.apply_rep s6 v5 a3 _ _ hinv6 h64 h_v5 h_a3 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with Store.apply_rep s7 v2 v6 _ _ hinv7 h64 h_v2 h_v6 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  store_step with Store.apply_rep s8 v7 a3 _ _ hinv8 h64 h_v7 h_a3 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  store_step with Store.apply_rep s9 v0 v8 _ _ hinv9 h64 h_v0 h_v8 (by ns_tac) (by ns_tac) as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo_bvite.construct s10 e_v10 (by rw [he_v10]; exact empty_args) hinv10 h64 as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  step as ⟨e_v11, he_v11⟩
  store_step with CtorSpec.eo_bvand.construct s11 e_v11 (by rw [he_v11]; exact empty_args) hinv11 h64 as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
  store_step with Store.apply_rep s12 v11 a0 _ _ hinv12 h64 h_v11 h_a0 (by ns_tac) (by ns_tac) as ⟨v12, s13, hinv13, h_v12⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo_bvand.construct s13 e_v13 (by rw [he_v13]; exact empty_args) hinv13 h64 as ⟨v13, s14, hinv14, h_v13⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
  store_step with Store.apply_rep s14 v13 a1 _ _ hinv14 h64 h_v13 h_a1 (by ns_tac) (by ns_tac) as ⟨v14, s15, hinv15, h_v14⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s15 1#u32 1#u32 (1) (1) rfl rfl (by unfold Tree.okBv; norm_num) hinv15 h64 as ⟨v15, s16, hinv16, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14
  store_step with Store.apply_rep s16 v14 v15 _ _ hinv16 h64 h_v14 h_v15 (by ns_tac) (by ns_tac) as ⟨v16, s17, hinv17, h_v16⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15
  store_step with Store.apply_rep s17 v12 v16 _ _ hinv17 h64 h_v12 h_v16 (by ns_tac) (by ns_tac) as ⟨v17, s18, hinv18, h_v17⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16
  store_step with Store.apply_rep s18 v10 v17 _ _ hinv18 h64 h_v10 h_v17 (by ns_tac) (by ns_tac) as ⟨v18, s19, hinv19, h_v18⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17
  store_step with Store.apply_rep s19 v18 a2 _ _ hinv19 h64 h_v18 h_a2 (by ns_tac) (by ns_tac) as ⟨v19, s20, hinv20, h_v19⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18
  store_step with Store.apply_rep s20 v19 a3 _ _ hinv20 h64 h_v19 h_a3 (by ns_tac) (by ns_tac) as ⟨v20, s21, hinv21, h_v20⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19
  store_step with Store.apply_rep s21 v9 v20 _ _ hinv21 h64 h_v9 h_v20 (by ns_tac) (by ns_tac) as ⟨v21, s22, hinv22, h_v21⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20
  case_done hinv22 hG with h_v21 in EoCases.__eo_prog_bv_ite_merge_else_if.case_0 using hn_a0 hn_a1 hn_a2 hn_a3

/-- logos's `__eo_prog_bv_ite_merge_else_if` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fbv_2dite_2dmerge_2delse_2dif.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) :
    __eo_prog_bv_ite_merge_else_if x_a0 x_a1 x_a2 x_a3 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_bv_ite_merge_else_if.case_0 x_a0 x_a1 x_a2 x_a3] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_bv_ite_merge_else_if
  unfold EoCases.__eo_prog_bv_ite_merge_else_if.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fbv_2dite_2dmerge_2delse_2dif_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) :
    body_eo__24eo_5fprog_5fbv_2dite_2dmerge_2delse_2dif s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_ite_merge_else_if x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fbv_2dite_2dmerge_2delse_2dif.rust_eq x_a0 x_a1 x_a2 x_a3 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3)]
  unfold body_eo__24eo_5fprog_5fbv_2dite_2dmerge_2delse_2dif
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  stuck_check h_a3 : x_a3 as hn_a3 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fbv_2dite_2dmerge_2delse_2dif_spec n ih s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2 hn_a3
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 using hn_a0 hn_a1 hn_a2 hn_a3
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hn_a3 hc0 in EoCases.__eo_prog_bv_ite_merge_else_if.case_0

theorem eo__24eo_5fprog_5fbv_2dite_2dmerge_2delse_2dif_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fbv_2dite_2dmerge_2delse_2dif.Spec n := by
  intro s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3
  unfold eo__24eo_5fprog_5fbv_2dite_2dmerge_2delse_2dif
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fbv_2dite_2dmerge_2delse_2dif s1 a0 a1 a2 a3) (fun s' t => Represents.rep s' t (__eo_prog_bv_ite_merge_else_if x_a0 x_a1 x_a2 x_a3))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fbv_2dite_2dmerge_2delse_2dif_spec m (ih m hm) s1 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fbv_2dite_2dmerge_2dthen_2delse_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fbv_2dite_2dmerge_2dthen_2delse s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_bv_ite_merge_then_else.case_0 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_bv_ite_merge_then_else.case_0 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fbv_2dite_2dmerge_2dthen_2delse more_0_eo__24eo_5fprog_5fbv_2dite_2dmerge_2dthen_2delse more_1_eo__24eo_5fprog_5fbv_2dite_2dmerge_2dthen_2delse
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_bvite.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a2 _ _ hinv3 h64 h_v2 h_a2 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo_bvite.construct s4 e_v4 (by rw [he_v4]; exact empty_args) hinv4 h64 as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3
  store_step with Store.apply_rep s5 v4 a1 _ _ hinv5 h64 h_v4 h_a1 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4
  store_step with Store.apply_rep s6 v5 a2 _ _ hinv6 h64 h_v5 h_a2 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with Store.apply_rep s7 v6 a3 _ _ hinv7 h64 h_v6 h_a3 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  store_step with Store.apply_rep s8 v3 v7 _ _ hinv8 h64 h_v3 h_v7 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  store_step with Store.apply_rep s9 v0 v8 _ _ hinv9 h64 h_v0 h_v8 (by ns_tac) (by ns_tac) as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo_bvite.construct s10 e_v10 (by rw [he_v10]; exact empty_args) hinv10 h64 as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  step as ⟨e_v11, he_v11⟩
  store_step with CtorSpec.eo_bvand.construct s11 e_v11 (by rw [he_v11]; exact empty_args) hinv11 h64 as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo_bvnot.construct s12 e_v12 (by rw [he_v12]; exact empty_args) hinv12 h64 as ⟨v12, s13, hinv13, h_v12⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11
  store_step with Store.apply_rep s13 v12 a0 _ _ hinv13 h64 h_v12 h_a0 (by ns_tac) (by ns_tac) as ⟨v13, s14, hinv14, h_v13⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
  store_step with Store.apply_rep s14 v11 v13 _ _ hinv14 h64 h_v11 h_v13 (by ns_tac) (by ns_tac) as ⟨v14, s15, hinv15, h_v14⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo_bvand.construct s15 e_v15 (by rw [he_v15]; exact empty_args) hinv15 h64 as ⟨v15, s16, hinv16, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14
  step as ⟨e_v16, he_v16⟩
  store_step with CtorSpec.eo_bvnot.construct s16 e_v16 (by rw [he_v16]; exact empty_args) hinv16 h64 as ⟨v16, s17, hinv17, h_v16⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15
  store_step with Store.apply_rep s17 v16 a1 _ _ hinv17 h64 h_v16 h_a1 (by ns_tac) (by ns_tac) as ⟨v17, s18, hinv18, h_v17⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16
  store_step with Store.apply_rep s18 v15 v17 _ _ hinv18 h64 h_v15 h_v17 (by ns_tac) (by ns_tac) as ⟨v18, s19, hinv19, h_v18⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s19 1#u32 1#u32 (1) (1) rfl rfl (by unfold Tree.okBv; norm_num) hinv19 h64 as ⟨v19, s20, hinv20, h_v19⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18
  store_step with Store.apply_rep s20 v18 v19 _ _ hinv20 h64 h_v18 h_v19 (by ns_tac) (by ns_tac) as ⟨v20, s21, hinv21, h_v20⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19
  store_step with Store.apply_rep s21 v14 v20 _ _ hinv21 h64 h_v14 h_v20 (by ns_tac) (by ns_tac) as ⟨v21, s22, hinv22, h_v21⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20
  store_step with Store.apply_rep s22 v10 v21 _ _ hinv22 h64 h_v10 h_v21 (by ns_tac) (by ns_tac) as ⟨v22, s23, hinv23, h_v22⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21
  store_step with Store.apply_rep s23 v22 a3 _ _ hinv23 h64 h_v22 h_a3 (by ns_tac) (by ns_tac) as ⟨v23, s24, hinv24, h_v23⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22
  store_step with Store.apply_rep s24 v23 a2 _ _ hinv24 h64 h_v23 h_a2 (by ns_tac) (by ns_tac) as ⟨v24, s25, hinv25, h_v24⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23
  store_step with Store.apply_rep s25 v9 v24 _ _ hinv25 h64 h_v9 h_v24 (by ns_tac) (by ns_tac) as ⟨v25, s26, hinv26, h_v25⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24
  case_done hinv26 hG with h_v25 in EoCases.__eo_prog_bv_ite_merge_then_else.case_0 using hn_a0 hn_a1 hn_a2 hn_a3

/-- logos's `__eo_prog_bv_ite_merge_then_else` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fbv_2dite_2dmerge_2dthen_2delse.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) :
    __eo_prog_bv_ite_merge_then_else x_a0 x_a1 x_a2 x_a3 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_bv_ite_merge_then_else.case_0 x_a0 x_a1 x_a2 x_a3] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_bv_ite_merge_then_else
  unfold EoCases.__eo_prog_bv_ite_merge_then_else.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fbv_2dite_2dmerge_2dthen_2delse_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) :
    body_eo__24eo_5fprog_5fbv_2dite_2dmerge_2dthen_2delse s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_ite_merge_then_else x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fbv_2dite_2dmerge_2dthen_2delse.rust_eq x_a0 x_a1 x_a2 x_a3 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3)]
  unfold body_eo__24eo_5fprog_5fbv_2dite_2dmerge_2dthen_2delse
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  stuck_check h_a3 : x_a3 as hn_a3 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fbv_2dite_2dmerge_2dthen_2delse_spec n ih s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2 hn_a3
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 using hn_a0 hn_a1 hn_a2 hn_a3
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hn_a3 hc0 in EoCases.__eo_prog_bv_ite_merge_then_else.case_0

theorem eo__24eo_5fprog_5fbv_2dite_2dmerge_2dthen_2delse_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fbv_2dite_2dmerge_2dthen_2delse.Spec n := by
  intro s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3
  unfold eo__24eo_5fprog_5fbv_2dite_2dmerge_2dthen_2delse
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fbv_2dite_2dmerge_2dthen_2delse s1 a0 a1 a2 a3) (fun s' t => Represents.rep s' t (__eo_prog_bv_ite_merge_then_else x_a0 x_a1 x_a2 x_a3))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fbv_2dite_2dmerge_2dthen_2delse_spec m (ih m hm) s1 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fbv_2dite_2dmerge_2dthen_2dif_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fbv_2dite_2dmerge_2dthen_2dif s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_bv_ite_merge_then_if.case_0 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_bv_ite_merge_then_if.case_0 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fbv_2dite_2dmerge_2dthen_2dif more_0_eo__24eo_5fprog_5fbv_2dite_2dmerge_2dthen_2dif
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_bvite.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_bvite.construct s3 e_v3 (by rw [he_v3]; exact empty_args) hinv3 h64 as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v3 a1 _ _ hinv4 h64 h_v3 h_a1 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3
  store_step with Store.apply_rep s5 v4 a2 _ _ hinv5 h64 h_v4 h_a2 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4
  store_step with Store.apply_rep s6 v5 a3 _ _ hinv6 h64 h_v5 h_a3 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with Store.apply_rep s7 v2 v6 _ _ hinv7 h64 h_v2 h_v6 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  store_step with Store.apply_rep s8 v7 a2 _ _ hinv8 h64 h_v7 h_a2 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  store_step with Store.apply_rep s9 v0 v8 _ _ hinv9 h64 h_v0 h_v8 (by ns_tac) (by ns_tac) as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo_bvite.construct s10 e_v10 (by rw [he_v10]; exact empty_args) hinv10 h64 as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  step as ⟨e_v11, he_v11⟩
  store_step with CtorSpec.eo_bvand.construct s11 e_v11 (by rw [he_v11]; exact empty_args) hinv11 h64 as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
  store_step with Store.apply_rep s12 v11 a0 _ _ hinv12 h64 h_v11 h_a0 (by ns_tac) (by ns_tac) as ⟨v12, s13, hinv13, h_v12⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo_bvand.construct s13 e_v13 (by rw [he_v13]; exact empty_args) hinv13 h64 as ⟨v13, s14, hinv14, h_v13⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo_bvnot.construct s14 e_v14 (by rw [he_v14]; exact empty_args) hinv14 h64 as ⟨v14, s15, hinv15, h_v14⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13
  store_step with Store.apply_rep s15 v14 a1 _ _ hinv15 h64 h_v14 h_a1 (by ns_tac) (by ns_tac) as ⟨v15, s16, hinv16, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14
  store_step with Store.apply_rep s16 v13 v15 _ _ hinv16 h64 h_v13 h_v15 (by ns_tac) (by ns_tac) as ⟨v16, s17, hinv17, h_v16⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s17 1#u32 1#u32 (1) (1) rfl rfl (by unfold Tree.okBv; norm_num) hinv17 h64 as ⟨v17, s18, hinv18, h_v17⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16
  store_step with Store.apply_rep s18 v16 v17 _ _ hinv18 h64 h_v16 h_v17 (by ns_tac) (by ns_tac) as ⟨v18, s19, hinv19, h_v18⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17
  store_step with Store.apply_rep s19 v12 v18 _ _ hinv19 h64 h_v12 h_v18 (by ns_tac) (by ns_tac) as ⟨v19, s20, hinv20, h_v19⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18
  store_step with Store.apply_rep s20 v10 v19 _ _ hinv20 h64 h_v10 h_v19 (by ns_tac) (by ns_tac) as ⟨v20, s21, hinv21, h_v20⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19
  store_step with Store.apply_rep s21 v20 a3 _ _ hinv21 h64 h_v20 h_a3 (by ns_tac) (by ns_tac) as ⟨v21, s22, hinv22, h_v21⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20
  store_step with Store.apply_rep s22 v21 a2 _ _ hinv22 h64 h_v21 h_a2 (by ns_tac) (by ns_tac) as ⟨v22, s23, hinv23, h_v22⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21
  store_step with Store.apply_rep s23 v9 v22 _ _ hinv23 h64 h_v9 h_v22 (by ns_tac) (by ns_tac) as ⟨v23, s24, hinv24, h_v23⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22
  case_done hinv24 hG with h_v23 in EoCases.__eo_prog_bv_ite_merge_then_if.case_0 using hn_a0 hn_a1 hn_a2 hn_a3

/-- logos's `__eo_prog_bv_ite_merge_then_if` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fbv_2dite_2dmerge_2dthen_2dif.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) :
    __eo_prog_bv_ite_merge_then_if x_a0 x_a1 x_a2 x_a3 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_bv_ite_merge_then_if.case_0 x_a0 x_a1 x_a2 x_a3] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_bv_ite_merge_then_if
  unfold EoCases.__eo_prog_bv_ite_merge_then_if.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fbv_2dite_2dmerge_2dthen_2dif_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) :
    body_eo__24eo_5fprog_5fbv_2dite_2dmerge_2dthen_2dif s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_ite_merge_then_if x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fbv_2dite_2dmerge_2dthen_2dif.rust_eq x_a0 x_a1 x_a2 x_a3 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3)]
  unfold body_eo__24eo_5fprog_5fbv_2dite_2dmerge_2dthen_2dif
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  stuck_check h_a3 : x_a3 as hn_a3 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fbv_2dite_2dmerge_2dthen_2dif_spec n ih s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2 hn_a3
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 using hn_a0 hn_a1 hn_a2 hn_a3
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hn_a3 hc0 in EoCases.__eo_prog_bv_ite_merge_then_if.case_0

theorem eo__24eo_5fprog_5fbv_2dite_2dmerge_2dthen_2dif_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fbv_2dite_2dmerge_2dthen_2dif.Spec n := by
  intro s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3
  unfold eo__24eo_5fprog_5fbv_2dite_2dmerge_2dthen_2dif
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fbv_2dite_2dmerge_2dthen_2dif s1 a0 a1 a2 a3) (fun s' t => Represents.rep s' t (__eo_prog_bv_ite_merge_then_if x_a0 x_a1 x_a2 x_a3))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fbv_2dite_2dmerge_2dthen_2dif_spec m (ih m hm) s1 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fbv_2dite_2dwidth_2done_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fbv_2dite_2dwidth_2done s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_bv_ite_width_one.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_bv_ite_width_one.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fbv_2dite_2dwidth_2done more_0_eo__24eo_5fprog_5fbv_2dite_2dwidth_2done
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_ite.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__3d.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a0 _ _ hinv3 h64 h_v2 h_a0 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s4 1#u32 (1) (by scalar_tac) hinv4 h64 as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s5 e_v5 (by rw [he_v5]; rfl) h_v4 hinv5 h64 as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s6 1#u32 (1) (by scalar_tac) hinv6 h64 as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with Store.apply_rep s7 v5 v6 _ _ hinv7 h64 h_v5 h_v6 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  store_step with Store.apply_rep s8 v3 v7 _ _ hinv8 h64 h_v3 h_v7 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  store_step with Store.apply_rep s9 v1 v8 _ _ hinv9 h64 h_v1 h_v8 (by ns_tac) (by ns_tac) as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s10 1#u32 (1) (by scalar_tac) hinv10 h64 as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  step as ⟨e_v11, he_v11⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s11 e_v11 (by rw [he_v11]; rfl) h_v10 hinv11 h64 as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s12 1#u32 (1) (by scalar_tac) hinv12 h64 as ⟨v12, s13, hinv13, h_v12⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11
  store_step with Store.apply_rep s13 v11 v12 _ _ hinv13 h64 h_v11 h_v12 (by ns_tac) (by ns_tac) as ⟨v13, s14, hinv14, h_v13⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
  store_step with Store.apply_rep s14 v9 v13 _ _ hinv14 h64 h_v9 h_v13 (by ns_tac) (by ns_tac) as ⟨v14, s15, hinv15, h_v14⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s15 1#u32 (1) (by scalar_tac) hinv15 h64 as ⟨v15, s16, hinv16, h_v15⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14
  step as ⟨e_v16, he_v16⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s16 e_v16 (by rw [he_v16]; rfl) h_v15 hinv16 h64 as ⟨v16, s17, hinv17, h_v16⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s17 0#u32 (0) (by scalar_tac) hinv17 h64 as ⟨v17, s18, hinv18, h_v17⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16
  store_step with Store.apply_rep s18 v16 v17 _ _ hinv18 h64 h_v16 h_v17 (by ns_tac) (by ns_tac) as ⟨v18, s19, hinv19, h_v18⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17
  store_step with Store.apply_rep s19 v14 v18 _ _ hinv19 h64 h_v14 h_v18 (by ns_tac) (by ns_tac) as ⟨v19, s20, hinv20, h_v19⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18
  store_step with Store.apply_rep s20 v0 v19 _ _ hinv20 h64 h_v0 h_v19 (by ns_tac) (by ns_tac) as ⟨v20, s21, hinv21, h_v20⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19
  store_step with Store.apply_rep s21 v20 a0 _ _ hinv21 h64 h_v20 h_a0 (by ns_tac) (by ns_tac) as ⟨v21, s22, hinv22, h_v21⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20
  case_done hinv22 hG with h_v21 in EoCases.__eo_prog_bv_ite_width_one.case_0 using hn_a0

/-- logos's `__eo_prog_bv_ite_width_one` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fbv_2dite_2dwidth_2done.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_bv_ite_width_one x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_bv_ite_width_one.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_bv_ite_width_one
  unfold EoCases.__eo_prog_bv_ite_width_one.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fbv_2dite_2dwidth_2done_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fbv_2dite_2dwidth_2done s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_ite_width_one x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fbv_2dite_2dwidth_2done.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fbv_2dite_2dwidth_2done
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fbv_2dite_2dwidth_2done_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_bv_ite_width_one.case_0

theorem eo__24eo_5fprog_5fbv_2dite_2dwidth_2done_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fbv_2dite_2dwidth_2done.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fbv_2dite_2dwidth_2done
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fbv_2dite_2dwidth_2done s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_bv_ite_width_one x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fbv_2dite_2dwidth_2done_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fbv_2dite_2dwidth_2done_2dnot_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fbv_2dite_2dwidth_2done_2dnot s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_bv_ite_width_one_not.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_bv_ite_width_one_not.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fbv_2dite_2dwidth_2done_2dnot more_0_eo__24eo_5fprog_5fbv_2dite_2dwidth_2done_2dnot
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_ite.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__3d.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a0 _ _ hinv3 h64 h_v2 h_a0 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s4 1#u32 (1) (by scalar_tac) hinv4 h64 as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s5 e_v5 (by rw [he_v5]; rfl) h_v4 hinv5 h64 as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s6 0#u32 (0) (by scalar_tac) hinv6 h64 as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with Store.apply_rep s7 v5 v6 _ _ hinv7 h64 h_v5 h_v6 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  store_step with Store.apply_rep s8 v3 v7 _ _ hinv8 h64 h_v3 h_v7 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  store_step with Store.apply_rep s9 v1 v8 _ _ hinv9 h64 h_v1 h_v8 (by ns_tac) (by ns_tac) as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s10 1#u32 (1) (by scalar_tac) hinv10 h64 as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  step as ⟨e_v11, he_v11⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s11 e_v11 (by rw [he_v11]; rfl) h_v10 hinv11 h64 as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s12 1#u32 (1) (by scalar_tac) hinv12 h64 as ⟨v12, s13, hinv13, h_v12⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11
  store_step with Store.apply_rep s13 v11 v12 _ _ hinv13 h64 h_v11 h_v12 (by ns_tac) (by ns_tac) as ⟨v13, s14, hinv14, h_v13⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
  store_step with Store.apply_rep s14 v9 v13 _ _ hinv14 h64 h_v9 h_v13 (by ns_tac) (by ns_tac) as ⟨v14, s15, hinv15, h_v14⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s15 1#u32 (1) (by scalar_tac) hinv15 h64 as ⟨v15, s16, hinv16, h_v15⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14
  step as ⟨e_v16, he_v16⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s16 e_v16 (by rw [he_v16]; rfl) h_v15 hinv16 h64 as ⟨v16, s17, hinv17, h_v16⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s17 0#u32 (0) (by scalar_tac) hinv17 h64 as ⟨v17, s18, hinv18, h_v17⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16
  store_step with Store.apply_rep s18 v16 v17 _ _ hinv18 h64 h_v16 h_v17 (by ns_tac) (by ns_tac) as ⟨v18, s19, hinv19, h_v18⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17
  store_step with Store.apply_rep s19 v14 v18 _ _ hinv19 h64 h_v14 h_v18 (by ns_tac) (by ns_tac) as ⟨v19, s20, hinv20, h_v19⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18
  store_step with Store.apply_rep s20 v0 v19 _ _ hinv20 h64 h_v0 h_v19 (by ns_tac) (by ns_tac) as ⟨v20, s21, hinv21, h_v20⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19
  step as ⟨e_v21, he_v21⟩
  store_step with CtorSpec.eo_bvnot.construct s21 e_v21 (by rw [he_v21]; exact empty_args) hinv21 h64 as ⟨v21, s22, hinv22, h_v21⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20
  store_step with Store.apply_rep s22 v21 a0 _ _ hinv22 h64 h_v21 h_a0 (by ns_tac) (by ns_tac) as ⟨v22, s23, hinv23, h_v22⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21
  store_step with Store.apply_rep s23 v20 v22 _ _ hinv23 h64 h_v20 h_v22 (by ns_tac) (by ns_tac) as ⟨v23, s24, hinv24, h_v23⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22
  case_done hinv24 hG with h_v23 in EoCases.__eo_prog_bv_ite_width_one_not.case_0 using hn_a0

/-- logos's `__eo_prog_bv_ite_width_one_not` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fbv_2dite_2dwidth_2done_2dnot.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_bv_ite_width_one_not x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_bv_ite_width_one_not.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_bv_ite_width_one_not
  unfold EoCases.__eo_prog_bv_ite_width_one_not.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fbv_2dite_2dwidth_2done_2dnot_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fbv_2dite_2dwidth_2done_2dnot s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_ite_width_one_not x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fbv_2dite_2dwidth_2done_2dnot.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fbv_2dite_2dwidth_2done_2dnot
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fbv_2dite_2dwidth_2done_2dnot_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_bv_ite_width_one_not.case_0

theorem eo__24eo_5fprog_5fbv_2dite_2dwidth_2done_2dnot_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fbv_2dite_2dwidth_2done_2dnot.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fbv_2dite_2dwidth_2done_2dnot
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fbv_2dite_2dwidth_2done_2dnot s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_bv_ite_width_one_not x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fbv_2dite_2dwidth_2done_2dnot_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d0_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d0 s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_bv_lshr_by_const_0.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_bv_lshr_by_const_0.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d0
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_bvlshr.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s3 e_v3 (by rw [he_v3]; rfl) h_a1 hinv3 h64 as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s4 0#u32 (0) (by scalar_tac) hinv4 h64 as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3
  store_step with Store.apply_rep s5 v3 v4 _ _ hinv5 h64 h_v3 h_v4 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4
  store_step with Store.apply_rep s6 v2 v5 _ _ hinv6 h64 h_v2 h_v5 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with Store.apply_rep s7 v0 v6 _ _ hinv7 h64 h_v0 h_v6 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  store_step with Store.apply_rep s8 v7 a0 _ _ hinv8 h64 h_v7 h_a0 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  case_done hinv9 hG with h_v8 in EoCases.__eo_prog_bv_lshr_by_const_0.case_0 using hn_a0 hn_a1

/-- logos's `__eo_prog_bv_lshr_by_const_0` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d0.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_bv_lshr_by_const_0 x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_bv_lshr_by_const_0.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_bv_lshr_by_const_0
  unfold EoCases.__eo_prog_bv_lshr_by_const_0.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d0_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d0 s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_lshr_by_const_0 x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d0.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d0
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d0_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_bv_lshr_by_const_0.case_0

theorem eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d0_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d0.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d0
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d0 s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_bv_lshr_by_const_0 x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d0_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d1_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d1 s a0 a1 a2 a3 a4 a5 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_bv_lshr_by_const_1.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_bv_lshr_by_const_1.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d1 more_0_eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d1 more_1_eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d1 more_2_eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d1 more_3_eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d1
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a4 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_bv_lshr_by_const_1.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_lshr_by_const_1.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_lshr_by_const_1.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_lshr_by_const_1.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_lshr_by_const_1.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_lshr_by_const_1.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__3c.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_lshr_by_const_1.case_0
  pat_same v14 a1 with h_v14 h_a1 using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_lshr_by_const_1.case_0
  pat_unapply h_v11 as ⟨v17, v18, x_v17, x_v18, h_v17, h_v18, hn_v17, hn_v18⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_lshr_by_const_1.case_0
  step as ⟨e_v19, he_v19⟩
  store_step with CtorSpec.eo__40bvsize.construct s2 e_v19 (by rw [he_v19]; exact empty_args) hinv2 h64 as ⟨v19, s3, hinv3, h_v19⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18
  pat_same v17 v19 with h_v17 h_v19 using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_lshr_by_const_1.case_0
  pat_same v18 a0 with h_v18 h_a0 using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_lshr_by_const_1.case_0
  store_step with Store.literal_boolean_spec s3 true hinv3 h64 as ⟨v20, s4, hinv4, h_v20⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19
  pat_same v4 v20 with h_v4 h_v20 using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_lshr_by_const_1.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a5 as ⟨v22, x_v22, h_v22⟩ else hinv4 hG in EoCases.__eo_prog_bv_lshr_by_const_1.case_0
  pat_unapply h_v22 as ⟨v24, v25, x_v24, x_v25, h_v24, h_v25, hn_v24, hn_v25⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_lshr_by_const_1.case_0
  pat_unapply h_v24 as ⟨v27, v28, x_v27, x_v28, h_v27, h_v28, hn_v27, hn_v28⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_lshr_by_const_1.case_0
  step as ⟨e_v29, he_v29⟩
  store_step with CtorSpec.eo__3d.construct s4 e_v29 (by rw [he_v29]; exact empty_args) hinv4 h64 as ⟨v29, s5, hinv5, h_v29⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28
  pat_same v27 v29 with h_v27 h_v29 using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_lshr_by_const_1.case_0
  pat_same v28 a3 with h_v28 h_a3 using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_lshr_by_const_1.case_0
  pat_unapply h_v25 as ⟨v31, v32, x_v31, x_v32, h_v31, h_v32, hn_v31, hn_v32⟩ using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_lshr_by_const_1.case_0
  pat_unapply h_v31 as ⟨v34, v35, x_v34, x_v35, h_v34, h_v35, hn_v34, hn_v35⟩ using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_lshr_by_const_1.case_0
  step as ⟨e_v36, he_v36⟩
  store_step with CtorSpec.eo__2d.construct s5 e_v36 (by rw [he_v36]; exact empty_args) hinv5 h64 as ⟨v36, s6, hinv6, h_v36⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35
  pat_same v34 v36 with h_v34 h_v36 using hinv6 else hinv6 hG in EoCases.__eo_prog_bv_lshr_by_const_1.case_0
  pat_unapply h_v35 as ⟨v38, v39, x_v38, x_v39, h_v38, h_v39, hn_v38, hn_v39⟩ using hinv6 else hinv6 hG in EoCases.__eo_prog_bv_lshr_by_const_1.case_0
  step as ⟨e_v40, he_v40⟩
  store_step with CtorSpec.eo__40bvsize.construct s6 e_v40 (by rw [he_v40]; exact empty_args) hinv6 h64 as ⟨v40, s7, hinv7, h_v40⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39
  pat_same v38 v40 with h_v38 h_v40 using hinv7 else hinv7 hG in EoCases.__eo_prog_bv_lshr_by_const_1.case_0
  pat_same v39 a0 with h_v39 h_a0 using hinv7 else hinv7 hG in EoCases.__eo_prog_bv_lshr_by_const_1.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s7 1#u32 (1) (by scalar_tac) hinv7 h64 as ⟨v41, s8, hinv8, h_v41⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40
  pat_same v32 v41 with h_v32 h_v41 using hinv8 else hinv8 hG in EoCases.__eo_prog_bv_lshr_by_const_1.case_0
  step as ⟨e_v42, he_v42⟩
  store_step with CtorSpec.eo__3d.construct s8 e_v42 (by rw [he_v42]; exact empty_args) hinv8 h64 as ⟨v42, s9, hinv9, h_v42⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v41
  step as ⟨e_v43, he_v43⟩
  store_step with CtorSpec.eo_bvlshr.construct s9 e_v43 (by rw [he_v43]; exact empty_args) hinv9 h64 as ⟨v43, s10, hinv10, h_v43⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v41 h_v42
  store_step with Store.apply_rep s10 v43 a0 _ _ hinv10 h64 h_v43 h_a0 (by ns_tac) (by ns_tac) as ⟨v44, s11, hinv11, h_v44⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43
  step as ⟨e_v45, he_v45⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s11 e_v45 (by rw [he_v45]; rfl) h_a2 hinv11 h64 as ⟨v45, s12, hinv12, h_v45⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44
  store_step with Store.apply_rep s12 v45 a1 _ _ hinv12 h64 h_v45 h_a1 (by ns_tac) (by ns_tac) as ⟨v46, s13, hinv13, h_v46⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45
  store_step with Store.apply_rep s13 v44 v46 _ _ hinv13 h64 h_v44 h_v46 (by ns_tac) (by ns_tac) as ⟨v47, s14, hinv14, h_v47⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46
  store_step with Store.apply_rep s14 v42 v47 _ _ hinv14 h64 h_v42 h_v47 (by ns_tac) (by ns_tac) as ⟨v48, s15, hinv15, h_v48⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47
  step as ⟨e_v49, he_v49⟩
  store_step with CtorSpec.eo_concat.construct s15 e_v49 (by rw [he_v49]; exact empty_args) hinv15 h64 as ⟨v49, s16, hinv16, h_v49⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48
  step as ⟨e_v50, he_v50⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s16 e_v50 (by rw [he_v50]; rfl) h_a1 hinv16 h64 as ⟨v50, s17, hinv17, h_v50⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s17 0#u32 (0) (by scalar_tac) hinv17 h64 as ⟨v51, s18, hinv18, h_v51⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50
  store_step with Store.apply_rep s18 v50 v51 _ _ hinv18 h64 h_v50 h_v51 (by ns_tac) (by ns_tac) as ⟨v52, s19, hinv19, h_v52⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51
  store_step with Store.apply_rep s19 v49 v52 _ _ hinv19 h64 h_v49 h_v52 (by ns_tac) (by ns_tac) as ⟨v53, s20, hinv20, h_v53⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52
  step as ⟨e_v54, he_v54⟩
  store_step with CtorSpec.eo_concat.construct s20 e_v54 (by rw [he_v54]; exact empty_args) hinv20 h64 as ⟨v54, s21, hinv21, h_v54⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53
  step as ⟨e_v55, he_v55⟩
  store_step with CtorSpec.eo_extract.construct s21 e_v55 (by rw [he_v55]; rfl) h_a3 h_a1 hinv21 h64 as ⟨v55, s22, hinv22, h_v55⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54
  store_step with Store.apply_rep s22 v55 a0 _ _ hinv22 h64 h_v55 h_a0 (by ns_tac) (by ns_tac) as ⟨v56, s23, hinv23, h_v56⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55
  store_step with Store.apply_rep s23 v54 v56 _ _ hinv23 h64 h_v54 h_v56 (by ns_tac) (by ns_tac) as ⟨v57, s24, hinv24, h_v57⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s24 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv24 h64 as ⟨v58, s25, hinv25, h_v58⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57
  store_step with Store.apply_rep s25 v57 v58 _ _ hinv25 h64 h_v57 h_v58 (by ns_tac) (by ns_tac) as ⟨v59, s26, hinv26, h_v59⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58
  store_step with Store.apply_rep s26 v53 v59 _ _ hinv26 h64 h_v53 h_v59 (by ns_tac) (by ns_tac) as ⟨v60, s27, hinv27, h_v60⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59
  store_step with Store.apply_rep s27 v48 v60 _ _ hinv27 h64 h_v48 h_v60 (by ns_tac) (by ns_tac) as ⟨v61, s28, hinv28, h_v61⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60
  case_done hinv28 hG with h_v61 in EoCases.__eo_prog_bv_lshr_by_const_1.case_0 using hn_a0 hn_a1 hn_a2 hn_a3 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v13 hn_v14 hn_v17 hn_v18 hn_v24 hn_v25 hn_v27 hn_v28 hn_v31 hn_v32 hn_v34 hn_v35 hn_v38 hn_v39

/-- logos's `__eo_prog_bv_lshr_by_const_1` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d1.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) (hw_a4 : Valid.valid x_a4) (hw_a5 : Valid.valid x_a5) :
    __eo_prog_bv_lshr_by_const_1 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_bv_lshr_by_const_1.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_bv_lshr_by_const_1
  unfold EoCases.__eo_prog_bv_lshr_by_const_1.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d1_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) :
    body_eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d1 s a0 a1 a2 a3 a4 a5 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_lshr_by_const_1 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d1.rust_eq x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3) (by valid_tac hinv h_a4) (by valid_tac hinv h_a5)]
  unfold body_eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d1
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  stuck_check h_a3 : x_a3 as hn_a3 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d1_spec n ih s a0 a1 a2 a3 a4 a5 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 hn_a0 hn_a1 hn_a2 hn_a3
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 using hn_a0 hn_a1 hn_a2 hn_a3
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hn_a3 hc0 in EoCases.__eo_prog_bv_lshr_by_const_1.case_0

theorem eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d1_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d1.Spec n := by
  intro s a0 a1 a2 a3 a4 a5 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5
  unfold eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d1
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d1 s1 a0 a1 a2 a3 a4 a5) (fun s' t => Represents.rep s' t (__eo_prog_bv_lshr_by_const_1 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d1_spec m (ih m hm) s1 a0 a1 a2 a3 a4 a5 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn) (by congr_one h_a4 hn) (by congr_one h_a5 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d2_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d2 s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_bv_lshr_by_const_2.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_bv_lshr_by_const_2.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d2 more_0_eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d2 more_1_eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d2 more_2_eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d2
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a3 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_bv_lshr_by_const_2.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_lshr_by_const_2.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_lshr_by_const_2.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_lshr_by_const_2.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_lshr_by_const_2.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_lshr_by_const_2.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__3e_3d.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_lshr_by_const_2.case_0
  pat_same v14 a1 with h_v14 h_a1 using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_lshr_by_const_2.case_0
  pat_unapply h_v11 as ⟨v17, v18, x_v17, x_v18, h_v17, h_v18, hn_v17, hn_v18⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_lshr_by_const_2.case_0
  step as ⟨e_v19, he_v19⟩
  store_step with CtorSpec.eo__40bvsize.construct s2 e_v19 (by rw [he_v19]; exact empty_args) hinv2 h64 as ⟨v19, s3, hinv3, h_v19⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18
  pat_same v17 v19 with h_v17 h_v19 using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_lshr_by_const_2.case_0
  pat_same v18 a0 with h_v18 h_a0 using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_lshr_by_const_2.case_0
  store_step with Store.literal_boolean_spec s3 true hinv3 h64 as ⟨v20, s4, hinv4, h_v20⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19
  pat_same v4 v20 with h_v4 h_v20 using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_lshr_by_const_2.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a4 as ⟨v22, x_v22, h_v22⟩ else hinv4 hG in EoCases.__eo_prog_bv_lshr_by_const_2.case_0
  pat_unapply h_v22 as ⟨v24, v25, x_v24, x_v25, h_v24, h_v25, hn_v24, hn_v25⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_lshr_by_const_2.case_0
  pat_unapply h_v24 as ⟨v27, v28, x_v27, x_v28, h_v27, h_v28, hn_v27, hn_v28⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_lshr_by_const_2.case_0
  step as ⟨e_v29, he_v29⟩
  store_step with CtorSpec.eo__3d.construct s4 e_v29 (by rw [he_v29]; exact empty_args) hinv4 h64 as ⟨v29, s5, hinv5, h_v29⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28
  pat_same v27 v29 with h_v27 h_v29 using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_lshr_by_const_2.case_0
  pat_unapply h_v28 as ⟨v31, v32, x_v31, x_v32, h_v31, h_v32, hn_v31, hn_v32⟩ using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_lshr_by_const_2.case_0
  pat_unapply h_v31 as ⟨v34, v35, x_v34, x_v35, h_v34, h_v35, hn_v34, hn_v35⟩ using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_lshr_by_const_2.case_0
  step as ⟨e_v36, he_v36⟩
  store_step with CtorSpec.eo__3c.construct s5 e_v36 (by rw [he_v36]; exact empty_args) hinv5 h64 as ⟨v36, s6, hinv6, h_v36⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35
  pat_same v34 v36 with h_v34 h_v36 using hinv6 else hinv6 hG in EoCases.__eo_prog_bv_lshr_by_const_2.case_0
  pat_same v35 a1 with h_v35 h_a1 using hinv6 else hinv6 hG in EoCases.__eo_prog_bv_lshr_by_const_2.case_0
  pat_unapply h_v32 as ⟨v38, v39, x_v38, x_v39, h_v38, h_v39, hn_v38, hn_v39⟩ using hinv6 else hinv6 hG in EoCases.__eo_prog_bv_lshr_by_const_2.case_0
  step as ⟨e_v40, he_v40⟩
  store_step with CtorSpec.eo_int_2epow2.construct s6 e_v40 (by rw [he_v40]; exact empty_args) hinv6 h64 as ⟨v40, s7, hinv7, h_v40⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39
  pat_same v38 v40 with h_v38 h_v40 using hinv7 else hinv7 hG in EoCases.__eo_prog_bv_lshr_by_const_2.case_0
  pat_unapply h_v39 as ⟨v42, v43, x_v42, x_v43, h_v42, h_v43, hn_v42, hn_v43⟩ using hinv7 else hinv7 hG in EoCases.__eo_prog_bv_lshr_by_const_2.case_0
  step as ⟨e_v44, he_v44⟩
  store_step with CtorSpec.eo__40bvsize.construct s7 e_v44 (by rw [he_v44]; exact empty_args) hinv7 h64 as ⟨v44, s8, hinv8, h_v44⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43
  pat_same v42 v44 with h_v42 h_v44 using hinv8 else hinv8 hG in EoCases.__eo_prog_bv_lshr_by_const_2.case_0
  pat_same v43 a0 with h_v43 h_a0 using hinv8 else hinv8 hG in EoCases.__eo_prog_bv_lshr_by_const_2.case_0
  store_step with Store.literal_boolean_spec s8 true hinv8 h64 as ⟨v45, s9, hinv9, h_v45⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v44
  pat_same v25 v45 with h_v25 h_v45 using hinv9 else hinv9 hG in EoCases.__eo_prog_bv_lshr_by_const_2.case_0
  step as ⟨e_v46, he_v46⟩
  store_step with CtorSpec.eo__3d.construct s9 e_v46 (by rw [he_v46]; exact empty_args) hinv9 h64 as ⟨v46, s10, hinv10, h_v46⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v44 h_v45
  step as ⟨e_v47, he_v47⟩
  store_step with CtorSpec.eo_bvlshr.construct s10 e_v47 (by rw [he_v47]; exact empty_args) hinv10 h64 as ⟨v47, s11, hinv11, h_v47⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v44 h_v45 h_v46
  store_step with Store.apply_rep s11 v47 a0 _ _ hinv11 h64 h_v47 h_a0 (by ns_tac) (by ns_tac) as ⟨v48, s12, hinv12, h_v48⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47
  step as ⟨e_v49, he_v49⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s12 e_v49 (by rw [he_v49]; rfl) h_a2 hinv12 h64 as ⟨v49, s13, hinv13, h_v49⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48
  store_step with Store.apply_rep s13 v49 a1 _ _ hinv13 h64 h_v49 h_a1 (by ns_tac) (by ns_tac) as ⟨v50, s14, hinv14, h_v50⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49
  store_step with Store.apply_rep s14 v48 v50 _ _ hinv14 h64 h_v48 h_v50 (by ns_tac) (by ns_tac) as ⟨v51, s15, hinv15, h_v51⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50
  store_step with Store.apply_rep s15 v46 v51 _ _ hinv15 h64 h_v46 h_v51 (by ns_tac) (by ns_tac) as ⟨v52, s16, hinv16, h_v52⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51
  step as ⟨e_v53, he_v53⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s16 e_v53 (by rw [he_v53]; rfl) h_a2 hinv16 h64 as ⟨v53, s17, hinv17, h_v53⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s17 0#u32 (0) (by scalar_tac) hinv17 h64 as ⟨v54, s18, hinv18, h_v54⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53
  store_step with Store.apply_rep s18 v53 v54 _ _ hinv18 h64 h_v53 h_v54 (by ns_tac) (by ns_tac) as ⟨v55, s19, hinv19, h_v55⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54
  store_step with Store.apply_rep s19 v52 v55 _ _ hinv19 h64 h_v52 h_v55 (by ns_tac) (by ns_tac) as ⟨v56, s20, hinv20, h_v56⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55
  case_done hinv20 hG with h_v56 in EoCases.__eo_prog_bv_lshr_by_const_2.case_0 using hn_a0 hn_a1 hn_a2 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v13 hn_v14 hn_v17 hn_v18 hn_v24 hn_v25 hn_v27 hn_v28 hn_v31 hn_v32 hn_v34 hn_v35 hn_v38 hn_v39 hn_v42 hn_v43

/-- logos's `__eo_prog_bv_lshr_by_const_2` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d2.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) (hw_a4 : Valid.valid x_a4) :
    __eo_prog_bv_lshr_by_const_2 x_a0 x_a1 x_a2 x_a3 x_a4 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_bv_lshr_by_const_2.case_0 x_a0 x_a1 x_a2 x_a3 x_a4] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_bv_lshr_by_const_2
  unfold EoCases.__eo_prog_bv_lshr_by_const_2.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d2_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) :
    body_eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d2 s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_lshr_by_const_2 x_a0 x_a1 x_a2 x_a3 x_a4)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d2.rust_eq x_a0 x_a1 x_a2 x_a3 x_a4 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3) (by valid_tac hinv h_a4)]
  unfold body_eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d2
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d2_spec n ih s a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 using hn_a0 hn_a1 hn_a2
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hc0 in EoCases.__eo_prog_bv_lshr_by_const_2.case_0

theorem eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d2_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d2.Spec n := by
  intro s a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4
  unfold eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d2
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d2 s1 a0 a1 a2 a3 a4) (fun s' t => Represents.rep s' t (__eo_prog_bv_lshr_by_const_2 x_a0 x_a1 x_a2 x_a3 x_a4))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d2_spec m (ih m hm) s1 a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn) (by congr_one h_a4 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fbv_2dlshr_2dzero_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fbv_2dlshr_2dzero s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_bv_lshr_zero.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_bv_lshr_zero.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fbv_2dlshr_2dzero
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_bvlshr.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s2 e_v2 (by rw [he_v2]; rfl) h_a1 hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s3 0#u32 (0) (by scalar_tac) hinv3 h64 as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v2 v3 _ _ hinv4 h64 h_v2 h_v3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3
  store_step with Store.apply_rep s5 v1 v4 _ _ hinv5 h64 h_v1 h_v4 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4
  store_step with Store.apply_rep s6 v5 a0 _ _ hinv6 h64 h_v5 h_a0 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with Store.apply_rep s7 v0 v6 _ _ hinv7 h64 h_v0 h_v6 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s8 e_v8 (by rw [he_v8]; rfl) h_a1 hinv8 h64 as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s9 0#u32 (0) (by scalar_tac) hinv9 h64 as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
  store_step with Store.apply_rep s10 v8 v9 _ _ hinv10 h64 h_v8 h_v9 (by ns_tac) (by ns_tac) as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  store_step with Store.apply_rep s11 v7 v10 _ _ hinv11 h64 h_v7 h_v10 (by ns_tac) (by ns_tac) as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
  case_done hinv12 hG with h_v11 in EoCases.__eo_prog_bv_lshr_zero.case_0 using hn_a0 hn_a1

/-- logos's `__eo_prog_bv_lshr_zero` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fbv_2dlshr_2dzero.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_bv_lshr_zero x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_bv_lshr_zero.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_bv_lshr_zero
  unfold EoCases.__eo_prog_bv_lshr_zero.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fbv_2dlshr_2dzero_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5fbv_2dlshr_2dzero s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_lshr_zero x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fbv_2dlshr_2dzero.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5fbv_2dlshr_2dzero
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fbv_2dlshr_2dzero_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_bv_lshr_zero.case_0

theorem eo__24eo_5fprog_5fbv_2dlshr_2dzero_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fbv_2dlshr_2dzero.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5fbv_2dlshr_2dzero
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fbv_2dlshr_2dzero s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_bv_lshr_zero x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fbv_2dlshr_2dzero_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fbv_2dlt_2dself_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fbv_2dlt_2dself s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_bv_lt_self.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_bv_lt_self.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fbv_2dlt_2dself
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_bvslt.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a0 _ _ hinv3 h64 h_v2 h_a0 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v0 v3 _ _ hinv4 h64 h_v0 h_v3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3
  store_step with Store.literal_boolean_spec s5 false hinv5 h64 as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4
  store_step with Store.apply_rep s6 v4 v5 _ _ hinv6 h64 h_v4 h_v5 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5
  case_done hinv7 hG with h_v6 in EoCases.__eo_prog_bv_lt_self.case_0 using hn_a0

/-- logos's `__eo_prog_bv_lt_self` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fbv_2dlt_2dself.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_bv_lt_self x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_bv_lt_self.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_bv_lt_self
  unfold EoCases.__eo_prog_bv_lt_self.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fbv_2dlt_2dself_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fbv_2dlt_2dself s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_lt_self x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fbv_2dlt_2dself.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fbv_2dlt_2dself
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fbv_2dlt_2dself_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_bv_lt_self.case_0

theorem eo__24eo_5fprog_5fbv_2dlt_2dself_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fbv_2dlt_2dself.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fbv_2dlt_2dself
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fbv_2dlt_2dself s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_bv_lt_self x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fbv_2dlt_2dself_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fbv_2dmerge_2dsign_2dextend_2d1_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fbv_2dmerge_2dsign_2dextend_2d1 s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_bv_merge_sign_extend_1.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_bv_merge_sign_extend_1.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fbv_2dmerge_2dsign_2dextend_2d1 more_0_eo__24eo_5fprog_5fbv_2dmerge_2dsign_2dextend_2d1 more_1_eo__24eo_5fprog_5fbv_2dmerge_2dsign_2dextend_2d1
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a4 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_bv_merge_sign_extend_1.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_merge_sign_extend_1.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_merge_sign_extend_1.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_merge_sign_extend_1.case_0
  pat_same v7 a3 with h_v7 h_a3 using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_merge_sign_extend_1.case_0
  pat_unapply h_v4 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_merge_sign_extend_1.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_merge_sign_extend_1.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__2b.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_merge_sign_extend_1.case_0
  pat_same v14 a1 with h_v14 h_a1 using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_merge_sign_extend_1.case_0
  pat_unapply h_v11 as ⟨v17, v18, x_v17, x_v18, h_v17, h_v18, hn_v17, hn_v18⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_merge_sign_extend_1.case_0
  pat_unapply h_v17 as ⟨v20, v21, x_v20, x_v21, h_v20, h_v21, hn_v20, hn_v21⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_merge_sign_extend_1.case_0
  step as ⟨e_v22, he_v22⟩
  store_step with CtorSpec.eo__2b.construct s2 e_v22 (by rw [he_v22]; exact empty_args) hinv2 h64 as ⟨v22, s3, hinv3, h_v22⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v20 h_v21
  pat_same v20 v22 with h_v20 h_v22 using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_merge_sign_extend_1.case_0
  pat_same v21 a2 with h_v21 h_a2 using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_merge_sign_extend_1.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s3 0#u32 (0) (by scalar_tac) hinv3 h64 as ⟨v23, s4, hinv4, h_v23⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22
  pat_same v18 v23 with h_v18 h_v23 using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_merge_sign_extend_1.case_0
  step as ⟨e_v24, he_v24⟩
  store_step with CtorSpec.eo__3d.construct s4 e_v24 (by rw [he_v24]; exact empty_args) hinv4 h64 as ⟨v24, s5, hinv5, h_v24⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23
  step as ⟨e_v25, he_v25⟩
  store_step with CtorSpec.eo_sign_5fextend.construct s5 e_v25 (by rw [he_v25]; rfl) h_a1 hinv5 h64 as ⟨v25, s6, hinv6, h_v25⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23 h_v24
  step as ⟨e_v26, he_v26⟩
  store_step with CtorSpec.eo_sign_5fextend.construct s6 e_v26 (by rw [he_v26]; rfl) h_a2 hinv6 h64 as ⟨v26, s7, hinv7, h_v26⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25
  store_step with Store.apply_rep s7 v26 a0 _ _ hinv7 h64 h_v26 h_a0 (by ns_tac) (by ns_tac) as ⟨v27, s8, hinv8, h_v27⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26
  store_step with Store.apply_rep s8 v25 v27 _ _ hinv8 h64 h_v25 h_v27 (by ns_tac) (by ns_tac) as ⟨v28, s9, hinv9, h_v28⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27
  store_step with Store.apply_rep s9 v24 v28 _ _ hinv9 h64 h_v24 h_v28 (by ns_tac) (by ns_tac) as ⟨v29, s10, hinv10, h_v29⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28
  step as ⟨e_v30, he_v30⟩
  store_step with CtorSpec.eo_sign_5fextend.construct s10 e_v30 (by rw [he_v30]; rfl) h_a3 hinv10 h64 as ⟨v30, s11, hinv11, h_v30⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29
  store_step with Store.apply_rep s11 v30 a0 _ _ hinv11 h64 h_v30 h_a0 (by ns_tac) (by ns_tac) as ⟨v31, s12, hinv12, h_v31⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30
  store_step with Store.apply_rep s12 v29 v31 _ _ hinv12 h64 h_v29 h_v31 (by ns_tac) (by ns_tac) as ⟨v32, s13, hinv13, h_v32⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31
  case_done hinv13 hG with h_v32 in EoCases.__eo_prog_bv_merge_sign_extend_1.case_0 using hn_a0 hn_a1 hn_a2 hn_a3 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v13 hn_v14 hn_v17 hn_v18 hn_v20 hn_v21

/-- logos's `__eo_prog_bv_merge_sign_extend_1` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fbv_2dmerge_2dsign_2dextend_2d1.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) (hw_a4 : Valid.valid x_a4) :
    __eo_prog_bv_merge_sign_extend_1 x_a0 x_a1 x_a2 x_a3 x_a4 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_bv_merge_sign_extend_1.case_0 x_a0 x_a1 x_a2 x_a3 x_a4] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_bv_merge_sign_extend_1
  unfold EoCases.__eo_prog_bv_merge_sign_extend_1.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fbv_2dmerge_2dsign_2dextend_2d1_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) :
    body_eo__24eo_5fprog_5fbv_2dmerge_2dsign_2dextend_2d1 s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_merge_sign_extend_1 x_a0 x_a1 x_a2 x_a3 x_a4)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fbv_2dmerge_2dsign_2dextend_2d1.rust_eq x_a0 x_a1 x_a2 x_a3 x_a4 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3) (by valid_tac hinv h_a4)]
  unfold body_eo__24eo_5fprog_5fbv_2dmerge_2dsign_2dextend_2d1
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  stuck_check h_a3 : x_a3 as hn_a3 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fbv_2dmerge_2dsign_2dextend_2d1_spec n ih s a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 hn_a0 hn_a1 hn_a2 hn_a3
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 using hn_a0 hn_a1 hn_a2 hn_a3
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hn_a3 hc0 in EoCases.__eo_prog_bv_merge_sign_extend_1.case_0

theorem eo__24eo_5fprog_5fbv_2dmerge_2dsign_2dextend_2d1_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fbv_2dmerge_2dsign_2dextend_2d1.Spec n := by
  intro s a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4
  unfold eo__24eo_5fprog_5fbv_2dmerge_2dsign_2dextend_2d1
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fbv_2dmerge_2dsign_2dextend_2d1 s1 a0 a1 a2 a3 a4) (fun s' t => Represents.rep s' t (__eo_prog_bv_merge_sign_extend_1 x_a0 x_a1 x_a2 x_a3 x_a4))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fbv_2dmerge_2dsign_2dextend_2d1_spec m (ih m hm) s1 a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn) (by congr_one h_a4 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fbv_2dmerge_2dsign_2dextend_2d2_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fbv_2dmerge_2dsign_2dextend_2d2 s a0 a1 a2 a3 a4 a5 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_bv_merge_sign_extend_2.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_bv_merge_sign_extend_2.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fbv_2dmerge_2dsign_2dextend_2d2 more_0_eo__24eo_5fprog_5fbv_2dmerge_2dsign_2dextend_2d2 more_1_eo__24eo_5fprog_5fbv_2dmerge_2dsign_2dextend_2d2 more_2_eo__24eo_5fprog_5fbv_2dmerge_2dsign_2dextend_2d2
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a4 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_bv_merge_sign_extend_2.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_merge_sign_extend_2.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_merge_sign_extend_2.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_merge_sign_extend_2.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_merge_sign_extend_2.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_merge_sign_extend_2.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__3e.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_merge_sign_extend_2.case_0
  pat_same v14 a2 with h_v14 h_a2 using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_merge_sign_extend_2.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s2 0#u32 (0) (by scalar_tac) hinv2 h64 as ⟨v16, s3, hinv3, h_v16⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15
  pat_same v11 v16 with h_v11 h_v16 using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_merge_sign_extend_2.case_0
  store_step with Store.literal_boolean_spec s3 true hinv3 h64 as ⟨v17, s4, hinv4, h_v17⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16
  pat_same v4 v17 with h_v4 h_v17 using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_merge_sign_extend_2.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a5 as ⟨v19, x_v19, h_v19⟩ else hinv4 hG in EoCases.__eo_prog_bv_merge_sign_extend_2.case_0
  pat_unapply h_v19 as ⟨v21, v22, x_v21, x_v22, h_v21, h_v22, hn_v21, hn_v22⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_merge_sign_extend_2.case_0
  pat_unapply h_v21 as ⟨v24, v25, x_v24, x_v25, h_v24, h_v25, hn_v24, hn_v25⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_merge_sign_extend_2.case_0
  step as ⟨e_v26, he_v26⟩
  store_step with CtorSpec.eo__3d.construct s4 e_v26 (by rw [he_v26]; exact empty_args) hinv4 h64 as ⟨v26, s5, hinv5, h_v26⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v19 h_v21 h_v22 h_v24 h_v25
  pat_same v24 v26 with h_v24 h_v26 using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_merge_sign_extend_2.case_0
  pat_same v25 a3 with h_v25 h_a3 using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_merge_sign_extend_2.case_0
  pat_unapply h_v22 as ⟨v28, v29, x_v28, x_v29, h_v28, h_v29, hn_v28, hn_v29⟩ using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_merge_sign_extend_2.case_0
  pat_unapply h_v28 as ⟨v31, v32, x_v31, x_v32, h_v31, h_v32, hn_v31, hn_v32⟩ using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_merge_sign_extend_2.case_0
  step as ⟨e_v33, he_v33⟩
  store_step with CtorSpec.eo__2b.construct s5 e_v33 (by rw [he_v33]; exact empty_args) hinv5 h64 as ⟨v33, s6, hinv6, h_v33⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v19 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32
  pat_same v31 v33 with h_v31 h_v33 using hinv6 else hinv6 hG in EoCases.__eo_prog_bv_merge_sign_extend_2.case_0
  pat_same v32 a1 with h_v32 h_a1 using hinv6 else hinv6 hG in EoCases.__eo_prog_bv_merge_sign_extend_2.case_0
  pat_unapply h_v29 as ⟨v35, v36, x_v35, x_v36, h_v35, h_v36, hn_v35, hn_v36⟩ using hinv6 else hinv6 hG in EoCases.__eo_prog_bv_merge_sign_extend_2.case_0
  pat_unapply h_v35 as ⟨v38, v39, x_v38, x_v39, h_v38, h_v39, hn_v38, hn_v39⟩ using hinv6 else hinv6 hG in EoCases.__eo_prog_bv_merge_sign_extend_2.case_0
  step as ⟨e_v40, he_v40⟩
  store_step with CtorSpec.eo__2b.construct s6 e_v40 (by rw [he_v40]; exact empty_args) hinv6 h64 as ⟨v40, s7, hinv7, h_v40⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v19 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v38 h_v39
  pat_same v38 v40 with h_v38 h_v40 using hinv7 else hinv7 hG in EoCases.__eo_prog_bv_merge_sign_extend_2.case_0
  pat_same v39 a2 with h_v39 h_a2 using hinv7 else hinv7 hG in EoCases.__eo_prog_bv_merge_sign_extend_2.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s7 0#u32 (0) (by scalar_tac) hinv7 h64 as ⟨v41, s8, hinv8, h_v41⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v19 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v38 h_v39 h_v40
  pat_same v36 v41 with h_v36 h_v41 using hinv8 else hinv8 hG in EoCases.__eo_prog_bv_merge_sign_extend_2.case_0
  step as ⟨e_v42, he_v42⟩
  store_step with CtorSpec.eo__3d.construct s8 e_v42 (by rw [he_v42]; exact empty_args) hinv8 h64 as ⟨v42, s9, hinv9, h_v42⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v19 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v38 h_v39 h_v40 h_v41
  step as ⟨e_v43, he_v43⟩
  store_step with CtorSpec.eo_sign_5fextend.construct s9 e_v43 (by rw [he_v43]; rfl) h_a1 hinv9 h64 as ⟨v43, s10, hinv10, h_v43⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v19 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v38 h_v39 h_v40 h_v41 h_v42
  step as ⟨e_v44, he_v44⟩
  store_step with CtorSpec.eo_zero_5fextend.construct s10 e_v44 (by rw [he_v44]; rfl) h_a2 hinv10 h64 as ⟨v44, s11, hinv11, h_v44⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v19 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43
  store_step with Store.apply_rep s11 v44 a0 _ _ hinv11 h64 h_v44 h_a0 (by ns_tac) (by ns_tac) as ⟨v45, s12, hinv12, h_v45⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v19 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44
  store_step with Store.apply_rep s12 v43 v45 _ _ hinv12 h64 h_v43 h_v45 (by ns_tac) (by ns_tac) as ⟨v46, s13, hinv13, h_v46⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v19 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45
  store_step with Store.apply_rep s13 v42 v46 _ _ hinv13 h64 h_v42 h_v46 (by ns_tac) (by ns_tac) as ⟨v47, s14, hinv14, h_v47⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v19 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46
  step as ⟨e_v48, he_v48⟩
  store_step with CtorSpec.eo_zero_5fextend.construct s14 e_v48 (by rw [he_v48]; rfl) h_a3 hinv14 h64 as ⟨v48, s15, hinv15, h_v48⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v19 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47
  store_step with Store.apply_rep s15 v48 a0 _ _ hinv15 h64 h_v48 h_a0 (by ns_tac) (by ns_tac) as ⟨v49, s16, hinv16, h_v49⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v19 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48
  store_step with Store.apply_rep s16 v47 v49 _ _ hinv16 h64 h_v47 h_v49 (by ns_tac) (by ns_tac) as ⟨v50, s17, hinv17, h_v50⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v19 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49
  case_done hinv17 hG with h_v50 in EoCases.__eo_prog_bv_merge_sign_extend_2.case_0 using hn_a0 hn_a1 hn_a2 hn_a3 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v13 hn_v14 hn_v21 hn_v22 hn_v24 hn_v25 hn_v28 hn_v29 hn_v31 hn_v32 hn_v35 hn_v36 hn_v38 hn_v39

/-- logos's `__eo_prog_bv_merge_sign_extend_2` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fbv_2dmerge_2dsign_2dextend_2d2.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) (hw_a4 : Valid.valid x_a4) (hw_a5 : Valid.valid x_a5) :
    __eo_prog_bv_merge_sign_extend_2 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_bv_merge_sign_extend_2.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_bv_merge_sign_extend_2
  unfold EoCases.__eo_prog_bv_merge_sign_extend_2.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fbv_2dmerge_2dsign_2dextend_2d2_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) :
    body_eo__24eo_5fprog_5fbv_2dmerge_2dsign_2dextend_2d2 s a0 a1 a2 a3 a4 a5 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_merge_sign_extend_2 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fbv_2dmerge_2dsign_2dextend_2d2.rust_eq x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3) (by valid_tac hinv h_a4) (by valid_tac hinv h_a5)]
  unfold body_eo__24eo_5fprog_5fbv_2dmerge_2dsign_2dextend_2d2
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  stuck_check h_a3 : x_a3 as hn_a3 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fbv_2dmerge_2dsign_2dextend_2d2_spec n ih s a0 a1 a2 a3 a4 a5 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 hn_a0 hn_a1 hn_a2 hn_a3
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 using hn_a0 hn_a1 hn_a2 hn_a3
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hn_a3 hc0 in EoCases.__eo_prog_bv_merge_sign_extend_2.case_0

theorem eo__24eo_5fprog_5fbv_2dmerge_2dsign_2dextend_2d2_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fbv_2dmerge_2dsign_2dextend_2d2.Spec n := by
  intro s a0 a1 a2 a3 a4 a5 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5
  unfold eo__24eo_5fprog_5fbv_2dmerge_2dsign_2dextend_2d2
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fbv_2dmerge_2dsign_2dextend_2d2 s1 a0 a1 a2 a3 a4 a5) (fun s' t => Represents.rep s' t (__eo_prog_bv_merge_sign_extend_2 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fbv_2dmerge_2dsign_2dextend_2d2_spec m (ih m hm) s1 a0 a1 a2 a3 a4 a5 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn) (by congr_one h_a4 hn) (by congr_one h_a5 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fbv_2dnego_2deliminate_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fbv_2dnego_2deliminate s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_bv_nego_eliminate.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_bv_nego_eliminate.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fbv_2dnego_2deliminate more_0_eo__24eo_5fprog_5fbv_2dnego_2deliminate more_1_eo__24eo_5fprog_5fbv_2dnego_2deliminate more_2_eo__24eo_5fprog_5fbv_2dnego_2deliminate
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a2 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_bv_nego_eliminate.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_nego_eliminate.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_nego_eliminate.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_nego_eliminate.case_0
  pat_same v7 a1 with h_v7 h_a1 using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_nego_eliminate.case_0
  pat_unapply h_v4 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_nego_eliminate.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_nego_eliminate.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__2d.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_nego_eliminate.case_0
  pat_unapply h_v14 as ⟨v17, v18, x_v17, x_v18, h_v17, h_v18, hn_v17, hn_v18⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_nego_eliminate.case_0
  step as ⟨e_v19, he_v19⟩
  store_step with CtorSpec.eo__40bvsize.construct s2 e_v19 (by rw [he_v19]; exact empty_args) hinv2 h64 as ⟨v19, s3, hinv3, h_v19⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18
  pat_same v17 v19 with h_v17 h_v19 using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_nego_eliminate.case_0
  pat_same v18 a0 with h_v18 h_a0 using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_nego_eliminate.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s3 1#u32 (1) (by scalar_tac) hinv3 h64 as ⟨v20, s4, hinv4, h_v20⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19
  pat_same v11 v20 with h_v11 h_v20 using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_nego_eliminate.case_0
  step as ⟨e_v21, he_v21⟩
  store_step with CtorSpec.eo__3d.construct s4 e_v21 (by rw [he_v21]; exact empty_args) hinv4 h64 as ⟨v21, s5, hinv5, h_v21⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20
  step as ⟨e_v22, he_v22⟩
  store_step with CtorSpec.eo_bvnego.construct s5 e_v22 (by rw [he_v22]; exact empty_args) hinv5 h64 as ⟨v22, s6, hinv6, h_v22⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21
  store_step with Store.apply_rep s6 v22 a0 _ _ hinv6 h64 h_v22 h_a0 (by ns_tac) (by ns_tac) as ⟨v23, s7, hinv7, h_v23⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22
  store_step with Store.apply_rep s7 v21 v23 _ _ hinv7 h64 h_v21 h_v23 (by ns_tac) (by ns_tac) as ⟨v24, s8, hinv8, h_v24⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23
  step as ⟨e_v25, he_v25⟩
  store_step with CtorSpec.eo__3d.construct s8 e_v25 (by rw [he_v25]; exact empty_args) hinv8 h64 as ⟨v25, s9, hinv9, h_v25⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24
  store_step with Store.apply_rep s9 v25 a0 _ _ hinv9 h64 h_v25 h_a0 (by ns_tac) (by ns_tac) as ⟨v26, s10, hinv10, h_v26⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25
  step as ⟨e_v27, he_v27⟩
  store_step with CtorSpec.eo_concat.construct s10 e_v27 (by rw [he_v27]; exact empty_args) hinv10 h64 as ⟨v27, s11, hinv11, h_v27⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s11 1#u32 (1) (by scalar_tac) hinv11 h64 as ⟨v28, s12, hinv12, h_v28⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27
  step as ⟨e_v29, he_v29⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s12 e_v29 (by rw [he_v29]; rfl) h_v28 hinv12 h64 as ⟨v29, s13, hinv13, h_v29⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s13 1#u32 (1) (by scalar_tac) hinv13 h64 as ⟨v30, s14, hinv14, h_v30⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29
  store_step with Store.apply_rep s14 v29 v30 _ _ hinv14 h64 h_v29 h_v30 (by ns_tac) (by ns_tac) as ⟨v31, s15, hinv15, h_v31⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30
  store_step with Store.apply_rep s15 v27 v31 _ _ hinv15 h64 h_v27 h_v31 (by ns_tac) (by ns_tac) as ⟨v32, s16, hinv16, h_v32⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31
  step as ⟨e_v33, he_v33⟩
  store_step with CtorSpec.eo_concat.construct s16 e_v33 (by rw [he_v33]; exact empty_args) hinv16 h64 as ⟨v33, s17, hinv17, h_v33⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32
  step as ⟨e_v34, he_v34⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s17 e_v34 (by rw [he_v34]; rfl) h_a1 hinv17 h64 as ⟨v34, s18, hinv18, h_v34⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s18 0#u32 (0) (by scalar_tac) hinv18 h64 as ⟨v35, s19, hinv19, h_v35⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34
  store_step with Store.apply_rep s19 v34 v35 _ _ hinv19 h64 h_v34 h_v35 (by ns_tac) (by ns_tac) as ⟨v36, s20, hinv20, h_v36⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35
  store_step with Store.apply_rep s20 v33 v36 _ _ hinv20 h64 h_v33 h_v36 (by ns_tac) (by ns_tac) as ⟨v37, s21, hinv21, h_v37⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s21 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv21 h64 as ⟨v38, s22, hinv22, h_v38⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37
  store_step with Store.apply_rep s22 v37 v38 _ _ hinv22 h64 h_v37 h_v38 (by ns_tac) (by ns_tac) as ⟨v39, s23, hinv23, h_v39⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38
  store_step with Store.apply_rep s23 v32 v39 _ _ hinv23 h64 h_v32 h_v39 (by ns_tac) (by ns_tac) as ⟨v40, s24, hinv24, h_v40⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39
  store_step with Store.apply_rep s24 v26 v40 _ _ hinv24 h64 h_v26 h_v40 (by ns_tac) (by ns_tac) as ⟨v41, s25, hinv25, h_v41⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40
  store_step with Store.apply_rep s25 v24 v41 _ _ hinv25 h64 h_v24 h_v41 (by ns_tac) (by ns_tac) as ⟨v42, s26, hinv26, h_v42⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41
  case_done hinv26 hG with h_v42 in EoCases.__eo_prog_bv_nego_eliminate.case_0 using hn_a0 hn_a1 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v13 hn_v14 hn_v17 hn_v18

/-- logos's `__eo_prog_bv_nego_eliminate` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fbv_2dnego_2deliminate.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __eo_prog_bv_nego_eliminate x_a0 x_a1 x_a2 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_bv_nego_eliminate.case_0 x_a0 x_a1 x_a2] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_bv_nego_eliminate
  unfold EoCases.__eo_prog_bv_nego_eliminate.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fbv_2dnego_2deliminate_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24eo_5fprog_5fbv_2dnego_2deliminate s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_nego_eliminate x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fbv_2dnego_2deliminate.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24eo_5fprog_5fbv_2dnego_2deliminate
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fbv_2dnego_2deliminate_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_bv_nego_eliminate.case_0

theorem eo__24eo_5fprog_5fbv_2dnego_2deliminate_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fbv_2dnego_2deliminate.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24eo_5fprog_5fbv_2dnego_2deliminate
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fbv_2dnego_2deliminate s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__eo_prog_bv_nego_eliminate x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fbv_2dnego_2deliminate_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fbv_2dnot_2didemp_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fbv_2dnot_2didemp s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_bv_not_idemp.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_bv_not_idemp.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fbv_2dnot_2didemp
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_bvnot.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo_bvnot.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a0 _ _ hinv3 h64 h_v2 h_a0 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v1 v3 _ _ hinv4 h64 h_v1 h_v3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3
  store_step with Store.apply_rep s5 v0 v4 _ _ hinv5 h64 h_v0 h_v4 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4
  store_step with Store.apply_rep s6 v5 a0 _ _ hinv6 h64 h_v5 h_a0 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5
  case_done hinv7 hG with h_v6 in EoCases.__eo_prog_bv_not_idemp.case_0 using hn_a0

/-- logos's `__eo_prog_bv_not_idemp` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fbv_2dnot_2didemp.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_bv_not_idemp x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_bv_not_idemp.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_bv_not_idemp
  unfold EoCases.__eo_prog_bv_not_idemp.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fbv_2dnot_2didemp_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fbv_2dnot_2didemp s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_not_idemp x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fbv_2dnot_2didemp.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fbv_2dnot_2didemp
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fbv_2dnot_2didemp_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_bv_not_idemp.case_0

theorem eo__24eo_5fprog_5fbv_2dnot_2didemp_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fbv_2dnot_2didemp.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fbv_2dnot_2didemp
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fbv_2dnot_2didemp s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_bv_not_idemp x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fbv_2dnot_2didemp_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fbv_2dnot_2dneq_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fbv_2dnot_2dneq s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_bv_not_neq.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_bv_not_neq.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fbv_2dnot_2dneq more_0_eo__24eo_5fprog_5fbv_2dnot_2dneq more_1_eo__24eo_5fprog_5fbv_2dnot_2dneq
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a1 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_bv_not_neq.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_not_neq.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_not_neq.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_v1 h_v3 h_v4 h_v6 h_v7
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_not_neq.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_not_neq.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_not_neq.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__3e.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_a1 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_not_neq.case_0
  pat_unapply h_v14 as ⟨v17, v18, x_v17, x_v18, h_v17, h_v18, hn_v17, hn_v18⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_not_neq.case_0
  step as ⟨e_v19, he_v19⟩
  store_step with CtorSpec.eo__40bvsize.construct s2 e_v19 (by rw [he_v19]; exact empty_args) hinv2 h64 as ⟨v19, s3, hinv3, h_v19⟩ growing hG carrying h_a0 h_a1 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18
  pat_same v17 v19 with h_v17 h_v19 using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_not_neq.case_0
  pat_same v18 a0 with h_v18 h_a0 using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_not_neq.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s3 0#u32 (0) (by scalar_tac) hinv3 h64 as ⟨v20, s4, hinv4, h_v20⟩ growing hG carrying h_a0 h_a1 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19
  pat_same v11 v20 with h_v11 h_v20 using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_not_neq.case_0
  store_step with Store.literal_boolean_spec s4 true hinv4 h64 as ⟨v21, s5, hinv5, h_v21⟩ growing hG carrying h_a0 h_a1 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20
  pat_same v4 v21 with h_v4 h_v21 using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_not_neq.case_0
  step as ⟨e_v22, he_v22⟩
  store_step with CtorSpec.eo__3d.construct s5 e_v22 (by rw [he_v22]; exact empty_args) hinv5 h64 as ⟨v22, s6, hinv6, h_v22⟩ growing hG carrying h_a0 h_a1 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21
  step as ⟨e_v23, he_v23⟩
  store_step with CtorSpec.eo__3d.construct s6 e_v23 (by rw [he_v23]; exact empty_args) hinv6 h64 as ⟨v23, s7, hinv7, h_v23⟩ growing hG carrying h_a0 h_a1 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22
  store_step with Store.apply_rep s7 v23 a0 _ _ hinv7 h64 h_v23 h_a0 (by ns_tac) (by ns_tac) as ⟨v24, s8, hinv8, h_v24⟩ growing hG carrying h_a0 h_a1 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23
  step as ⟨e_v25, he_v25⟩
  store_step with CtorSpec.eo_bvnot.construct s8 e_v25 (by rw [he_v25]; exact empty_args) hinv8 h64 as ⟨v25, s9, hinv9, h_v25⟩ growing hG carrying h_a0 h_a1 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24
  store_step with Store.apply_rep s9 v25 a0 _ _ hinv9 h64 h_v25 h_a0 (by ns_tac) (by ns_tac) as ⟨v26, s10, hinv10, h_v26⟩ growing hG carrying h_a0 h_a1 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25
  store_step with Store.apply_rep s10 v24 v26 _ _ hinv10 h64 h_v24 h_v26 (by ns_tac) (by ns_tac) as ⟨v27, s11, hinv11, h_v27⟩ growing hG carrying h_a0 h_a1 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26
  store_step with Store.apply_rep s11 v22 v27 _ _ hinv11 h64 h_v22 h_v27 (by ns_tac) (by ns_tac) as ⟨v28, s12, hinv12, h_v28⟩ growing hG carrying h_a0 h_a1 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27
  store_step with Store.literal_boolean_spec s12 false hinv12 h64 as ⟨v29, s13, hinv13, h_v29⟩ growing hG carrying h_a0 h_a1 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28
  store_step with Store.apply_rep s13 v28 v29 _ _ hinv13 h64 h_v28 h_v29 (by ns_tac) (by ns_tac) as ⟨v30, s14, hinv14, h_v30⟩ growing hG carrying h_a0 h_a1 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29
  case_done hinv14 hG with h_v30 in EoCases.__eo_prog_bv_not_neq.case_0 using hn_a0 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v13 hn_v14 hn_v17 hn_v18

/-- logos's `__eo_prog_bv_not_neq` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fbv_2dnot_2dneq.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_bv_not_neq x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_bv_not_neq.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_bv_not_neq
  unfold EoCases.__eo_prog_bv_not_neq.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fbv_2dnot_2dneq_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5fbv_2dnot_2dneq s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_not_neq x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fbv_2dnot_2dneq.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5fbv_2dnot_2dneq
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fbv_2dnot_2dneq_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_bv_not_neq.case_0

theorem eo__24eo_5fprog_5fbv_2dnot_2dneq_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fbv_2dnot_2dneq.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5fbv_2dnot_2dneq
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fbv_2dnot_2dneq s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_bv_not_neq x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fbv_2dnot_2dneq_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fbv_2dnot_2dult_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fbv_2dnot_2dult s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_bv_not_ult.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_bv_not_ult.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fbv_2dnot_2dult
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_not.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo_bvult.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a0 _ _ hinv3 h64 h_v2 h_a0 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v3 a1 _ _ hinv4 h64 h_v3 h_a1 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3
  store_step with Store.apply_rep s5 v1 v4 _ _ hinv5 h64 h_v1 h_v4 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4
  store_step with Store.apply_rep s6 v0 v5 _ _ hinv6 h64 h_v0 h_v5 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo_bvule.construct s7 e_v7 (by rw [he_v7]; exact empty_args) hinv7 h64 as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  store_step with Store.apply_rep s8 v7 a1 _ _ hinv8 h64 h_v7 h_a1 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  store_step with Store.apply_rep s9 v8 a0 _ _ hinv9 h64 h_v8 h_a0 (by ns_tac) (by ns_tac) as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
  store_step with Store.apply_rep s10 v6 v9 _ _ hinv10 h64 h_v6 h_v9 (by ns_tac) (by ns_tac) as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  case_done hinv11 hG with h_v10 in EoCases.__eo_prog_bv_not_ult.case_0 using hn_a0 hn_a1

/-- logos's `__eo_prog_bv_not_ult` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fbv_2dnot_2dult.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_bv_not_ult x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_bv_not_ult.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_bv_not_ult
  unfold EoCases.__eo_prog_bv_not_ult.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fbv_2dnot_2dult_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5fbv_2dnot_2dult s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_not_ult x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fbv_2dnot_2dult.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5fbv_2dnot_2dult
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fbv_2dnot_2dult_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_bv_not_ult.case_0

theorem eo__24eo_5fprog_5fbv_2dnot_2dult_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fbv_2dnot_2dult.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5fbv_2dnot_2dult
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fbv_2dnot_2dult s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_bv_not_ult x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fbv_2dnot_2dult_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fbv_2dnot_2dxor_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fbv_2dnot_2dxor s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_bv_not_xor.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_bv_not_xor.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fbv_2dnot_2dxor more_0_eo__24eo_5fprog_5fbv_2dnot_2dxor
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_bvnot.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo_bvxor.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a0 _ _ hinv3 h64 h_v2 h_a0 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo_bvxor.construct s4 e_v4 (by rw [he_v4]; exact empty_args) hinv4 h64 as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3
  store_step with Store.apply_rep s5 v4 a1 _ _ hinv5 h64 h_v4 h_a1 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4
  store_step with Store.apply_rep s6 v5 a2 _ _ hinv6 h64 h_v5 h_a2 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with Store.apply_rep s7 v3 v6 _ _ hinv7 h64 h_v3 h_v6 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  store_step with Store.apply_rep s8 v1 v7 _ _ hinv8 h64 h_v1 h_v7 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  store_step with Store.apply_rep s9 v0 v8 _ _ hinv9 h64 h_v0 h_v8 (by ns_tac) (by ns_tac) as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo_bvxor.construct s10 e_v10 (by rw [he_v10]; exact empty_args) hinv10 h64 as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  step as ⟨e_v11, he_v11⟩
  store_step with CtorSpec.eo_bvnot.construct s11 e_v11 (by rw [he_v11]; exact empty_args) hinv11 h64 as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
  store_step with Store.apply_rep s12 v11 a0 _ _ hinv12 h64 h_v11 h_a0 (by ns_tac) (by ns_tac) as ⟨v12, s13, hinv13, h_v12⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11
  store_step with Store.apply_rep s13 v10 v12 _ _ hinv13 h64 h_v10 h_v12 (by ns_tac) (by ns_tac) as ⟨v13, s14, hinv14, h_v13⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo_bvxor.construct s14 e_v14 (by rw [he_v14]; exact empty_args) hinv14 h64 as ⟨v14, s15, hinv15, h_v14⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13
  store_step with Store.apply_rep s15 v14 a1 _ _ hinv15 h64 h_v14 h_a1 (by ns_tac) (by ns_tac) as ⟨v15, s16, hinv16, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14
  store_step with Store.apply_rep s16 v15 a2 _ _ hinv16 h64 h_v15 h_a2 (by ns_tac) (by ns_tac) as ⟨v16, s17, hinv17, h_v16⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15
  store_step with Store.apply_rep s17 v13 v16 _ _ hinv17 h64 h_v13 h_v16 (by ns_tac) (by ns_tac) as ⟨v17, s18, hinv18, h_v17⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16
  store_step with Store.apply_rep s18 v9 v17 _ _ hinv18 h64 h_v9 h_v17 (by ns_tac) (by ns_tac) as ⟨v18, s19, hinv19, h_v18⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17
  case_done hinv19 hG with h_v18 in EoCases.__eo_prog_bv_not_xor.case_0 using hn_a0 hn_a1 hn_a2

/-- logos's `__eo_prog_bv_not_xor` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fbv_2dnot_2dxor.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __eo_prog_bv_not_xor x_a0 x_a1 x_a2 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_bv_not_xor.case_0 x_a0 x_a1 x_a2] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_bv_not_xor
  unfold EoCases.__eo_prog_bv_not_xor.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fbv_2dnot_2dxor_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24eo_5fprog_5fbv_2dnot_2dxor s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_not_xor x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fbv_2dnot_2dxor.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24eo_5fprog_5fbv_2dnot_2dxor
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fbv_2dnot_2dxor_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1 hn_a2
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hc0 in EoCases.__eo_prog_bv_not_xor.case_0

theorem eo__24eo_5fprog_5fbv_2dnot_2dxor_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fbv_2dnot_2dxor.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24eo_5fprog_5fbv_2dnot_2dxor
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fbv_2dnot_2dxor s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__eo_prog_bv_not_xor x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fbv_2dnot_2dxor_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fbv_2dredand_2deliminate_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fbv_2dredand_2deliminate s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_bv_redand_eliminate.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_bv_redand_eliminate.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fbv_2dredand_2deliminate more_0_eo__24eo_5fprog_5fbv_2dredand_2deliminate
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a2 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_bv_redand_eliminate.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_redand_eliminate.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_redand_eliminate.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_redand_eliminate.case_0
  pat_same v7 a1 with h_v7 h_a1 using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_redand_eliminate.case_0
  pat_unapply h_v4 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_redand_eliminate.case_0
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo__40bvsize.construct s1 e_v12 (by rw [he_v12]; exact empty_args) hinv1 h64 as ⟨v12, s2, hinv2, h_v12⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11
  pat_same v10 v12 with h_v10 h_v12 using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_redand_eliminate.case_0
  pat_same v11 a0 with h_v11 h_a0 using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_redand_eliminate.case_0
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo__3d.construct s2 e_v13 (by rw [he_v13]; exact empty_args) hinv2 h64 as ⟨v13, s3, hinv3, h_v13⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo_bvredand.construct s3 e_v14 (by rw [he_v14]; exact empty_args) hinv3 h64 as ⟨v14, s4, hinv4, h_v14⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13
  store_step with Store.apply_rep s4 v14 a0 _ _ hinv4 h64 h_v14 h_a0 (by ns_tac) (by ns_tac) as ⟨v15, s5, hinv5, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14
  store_step with Store.apply_rep s5 v13 v15 _ _ hinv5 h64 h_v13 h_v15 (by ns_tac) (by ns_tac) as ⟨v16, s6, hinv6, h_v16⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15
  step as ⟨e_v17, he_v17⟩
  store_step with CtorSpec.eo_bvcomp.construct s6 e_v17 (by rw [he_v17]; exact empty_args) hinv6 h64 as ⟨v17, s7, hinv7, h_v17⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16
  store_step with Store.apply_rep s7 v17 a0 _ _ hinv7 h64 h_v17 h_a0 (by ns_tac) (by ns_tac) as ⟨v18, s8, hinv8, h_v18⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17
  step as ⟨e_v19, he_v19⟩
  store_step with CtorSpec.eo_bvnot.construct s8 e_v19 (by rw [he_v19]; exact empty_args) hinv8 h64 as ⟨v19, s9, hinv9, h_v19⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18
  step as ⟨e_v20, he_v20⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s9 e_v20 (by rw [he_v20]; rfl) h_a1 hinv9 h64 as ⟨v20, s10, hinv10, h_v20⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s10 0#u32 (0) (by scalar_tac) hinv10 h64 as ⟨v21, s11, hinv11, h_v21⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20
  store_step with Store.apply_rep s11 v20 v21 _ _ hinv11 h64 h_v20 h_v21 (by ns_tac) (by ns_tac) as ⟨v22, s12, hinv12, h_v22⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21
  store_step with Store.apply_rep s12 v19 v22 _ _ hinv12 h64 h_v19 h_v22 (by ns_tac) (by ns_tac) as ⟨v23, s13, hinv13, h_v23⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22
  store_step with Store.apply_rep s13 v18 v23 _ _ hinv13 h64 h_v18 h_v23 (by ns_tac) (by ns_tac) as ⟨v24, s14, hinv14, h_v24⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23
  store_step with Store.apply_rep s14 v16 v24 _ _ hinv14 h64 h_v16 h_v24 (by ns_tac) (by ns_tac) as ⟨v25, s15, hinv15, h_v25⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24
  case_done hinv15 hG with h_v25 in EoCases.__eo_prog_bv_redand_eliminate.case_0 using hn_a0 hn_a1 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11

/-- logos's `__eo_prog_bv_redand_eliminate` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fbv_2dredand_2deliminate.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __eo_prog_bv_redand_eliminate x_a0 x_a1 x_a2 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_bv_redand_eliminate.case_0 x_a0 x_a1 x_a2] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_bv_redand_eliminate
  unfold EoCases.__eo_prog_bv_redand_eliminate.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fbv_2dredand_2deliminate_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24eo_5fprog_5fbv_2dredand_2deliminate s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_redand_eliminate x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fbv_2dredand_2deliminate.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24eo_5fprog_5fbv_2dredand_2deliminate
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fbv_2dredand_2deliminate_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_bv_redand_eliminate.case_0

theorem eo__24eo_5fprog_5fbv_2dredand_2deliminate_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fbv_2dredand_2deliminate.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24eo_5fprog_5fbv_2dredand_2deliminate
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fbv_2dredand_2deliminate s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__eo_prog_bv_redand_eliminate x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fbv_2dredand_2deliminate_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fbv_2dredor_2deliminate_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fbv_2dredor_2deliminate s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_bv_redor_eliminate.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_bv_redor_eliminate.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fbv_2dredor_2deliminate more_0_eo__24eo_5fprog_5fbv_2dredor_2deliminate
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a2 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_bv_redor_eliminate.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_redor_eliminate.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_redor_eliminate.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_redor_eliminate.case_0
  pat_same v7 a1 with h_v7 h_a1 using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_redor_eliminate.case_0
  pat_unapply h_v4 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_redor_eliminate.case_0
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo__40bvsize.construct s1 e_v12 (by rw [he_v12]; exact empty_args) hinv1 h64 as ⟨v12, s2, hinv2, h_v12⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11
  pat_same v10 v12 with h_v10 h_v12 using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_redor_eliminate.case_0
  pat_same v11 a0 with h_v11 h_a0 using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_redor_eliminate.case_0
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo__3d.construct s2 e_v13 (by rw [he_v13]; exact empty_args) hinv2 h64 as ⟨v13, s3, hinv3, h_v13⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo_bvredor.construct s3 e_v14 (by rw [he_v14]; exact empty_args) hinv3 h64 as ⟨v14, s4, hinv4, h_v14⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13
  store_step with Store.apply_rep s4 v14 a0 _ _ hinv4 h64 h_v14 h_a0 (by ns_tac) (by ns_tac) as ⟨v15, s5, hinv5, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14
  store_step with Store.apply_rep s5 v13 v15 _ _ hinv5 h64 h_v13 h_v15 (by ns_tac) (by ns_tac) as ⟨v16, s6, hinv6, h_v16⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15
  step as ⟨e_v17, he_v17⟩
  store_step with CtorSpec.eo_bvnot.construct s6 e_v17 (by rw [he_v17]; exact empty_args) hinv6 h64 as ⟨v17, s7, hinv7, h_v17⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16
  step as ⟨e_v18, he_v18⟩
  store_step with CtorSpec.eo_bvcomp.construct s7 e_v18 (by rw [he_v18]; exact empty_args) hinv7 h64 as ⟨v18, s8, hinv8, h_v18⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17
  store_step with Store.apply_rep s8 v18 a0 _ _ hinv8 h64 h_v18 h_a0 (by ns_tac) (by ns_tac) as ⟨v19, s9, hinv9, h_v19⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18
  step as ⟨e_v20, he_v20⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s9 e_v20 (by rw [he_v20]; rfl) h_a1 hinv9 h64 as ⟨v20, s10, hinv10, h_v20⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s10 0#u32 (0) (by scalar_tac) hinv10 h64 as ⟨v21, s11, hinv11, h_v21⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20
  store_step with Store.apply_rep s11 v20 v21 _ _ hinv11 h64 h_v20 h_v21 (by ns_tac) (by ns_tac) as ⟨v22, s12, hinv12, h_v22⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21
  store_step with Store.apply_rep s12 v19 v22 _ _ hinv12 h64 h_v19 h_v22 (by ns_tac) (by ns_tac) as ⟨v23, s13, hinv13, h_v23⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22
  store_step with Store.apply_rep s13 v17 v23 _ _ hinv13 h64 h_v17 h_v23 (by ns_tac) (by ns_tac) as ⟨v24, s14, hinv14, h_v24⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23
  store_step with Store.apply_rep s14 v16 v24 _ _ hinv14 h64 h_v16 h_v24 (by ns_tac) (by ns_tac) as ⟨v25, s15, hinv15, h_v25⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24
  case_done hinv15 hG with h_v25 in EoCases.__eo_prog_bv_redor_eliminate.case_0 using hn_a0 hn_a1 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11

/-- logos's `__eo_prog_bv_redor_eliminate` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fbv_2dredor_2deliminate.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __eo_prog_bv_redor_eliminate x_a0 x_a1 x_a2 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_bv_redor_eliminate.case_0 x_a0 x_a1 x_a2] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_bv_redor_eliminate
  unfold EoCases.__eo_prog_bv_redor_eliminate.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fbv_2dredor_2deliminate_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24eo_5fprog_5fbv_2dredor_2deliminate s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_redor_eliminate x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fbv_2dredor_2deliminate.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24eo_5fprog_5fbv_2dredor_2deliminate
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fbv_2dredor_2deliminate_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_bv_redor_eliminate.case_0

theorem eo__24eo_5fprog_5fbv_2dredor_2deliminate_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fbv_2dredor_2deliminate.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24eo_5fprog_5fbv_2dredor_2deliminate
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fbv_2dredor_2deliminate s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__eo_prog_bv_redor_eliminate x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fbv_2dredor_2deliminate_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fbv_2drotate_2dleft_2deliminate_2d2_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fbv_2drotate_2dleft_2deliminate_2d2 s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_bv_rotate_left_eliminate_2.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_bv_rotate_left_eliminate_2.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fbv_2drotate_2dleft_2deliminate_2d2 more_0_eo__24eo_5fprog_5fbv_2drotate_2dleft_2deliminate_2d2
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a2 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_bv_rotate_left_eliminate_2.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_rotate_left_eliminate_2.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_rotate_left_eliminate_2.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_rotate_left_eliminate_2.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_rotate_left_eliminate_2.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_rotate_left_eliminate_2.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo_mod.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_rotate_left_eliminate_2.case_0
  pat_same v14 a1 with h_v14 h_a1 using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_rotate_left_eliminate_2.case_0
  pat_unapply h_v11 as ⟨v17, v18, x_v17, x_v18, h_v17, h_v18, hn_v17, hn_v18⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_rotate_left_eliminate_2.case_0
  step as ⟨e_v19, he_v19⟩
  store_step with CtorSpec.eo__40bvsize.construct s2 e_v19 (by rw [he_v19]; exact empty_args) hinv2 h64 as ⟨v19, s3, hinv3, h_v19⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18
  pat_same v17 v19 with h_v17 h_v19 using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_rotate_left_eliminate_2.case_0
  pat_same v18 a0 with h_v18 h_a0 using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_rotate_left_eliminate_2.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s3 0#u32 (0) (by scalar_tac) hinv3 h64 as ⟨v20, s4, hinv4, h_v20⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19
  pat_same v4 v20 with h_v4 h_v20 using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_rotate_left_eliminate_2.case_0
  step as ⟨e_v21, he_v21⟩
  store_step with CtorSpec.eo__3d.construct s4 e_v21 (by rw [he_v21]; exact empty_args) hinv4 h64 as ⟨v21, s5, hinv5, h_v21⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20
  step as ⟨e_v22, he_v22⟩
  store_step with CtorSpec.eo_rotate_5fleft.construct s5 e_v22 (by rw [he_v22]; rfl) h_a1 hinv5 h64 as ⟨v22, s6, hinv6, h_v22⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21
  store_step with Store.apply_rep s6 v22 a0 _ _ hinv6 h64 h_v22 h_a0 (by ns_tac) (by ns_tac) as ⟨v23, s7, hinv7, h_v23⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22
  store_step with Store.apply_rep s7 v21 v23 _ _ hinv7 h64 h_v21 h_v23 (by ns_tac) (by ns_tac) as ⟨v24, s8, hinv8, h_v24⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23
  store_step with Store.apply_rep s8 v24 a0 _ _ hinv8 h64 h_v24 h_a0 (by ns_tac) (by ns_tac) as ⟨v25, s9, hinv9, h_v25⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24
  case_done hinv9 hG with h_v25 in EoCases.__eo_prog_bv_rotate_left_eliminate_2.case_0 using hn_a0 hn_a1 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v13 hn_v14 hn_v17 hn_v18

/-- logos's `__eo_prog_bv_rotate_left_eliminate_2` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fbv_2drotate_2dleft_2deliminate_2d2.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __eo_prog_bv_rotate_left_eliminate_2 x_a0 x_a1 x_a2 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_bv_rotate_left_eliminate_2.case_0 x_a0 x_a1 x_a2] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_bv_rotate_left_eliminate_2
  unfold EoCases.__eo_prog_bv_rotate_left_eliminate_2.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fbv_2drotate_2dleft_2deliminate_2d2_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24eo_5fprog_5fbv_2drotate_2dleft_2deliminate_2d2 s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_rotate_left_eliminate_2 x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fbv_2drotate_2dleft_2deliminate_2d2.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24eo_5fprog_5fbv_2drotate_2dleft_2deliminate_2d2
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fbv_2drotate_2dleft_2deliminate_2d2_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_bv_rotate_left_eliminate_2.case_0

theorem eo__24eo_5fprog_5fbv_2drotate_2dleft_2deliminate_2d2_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fbv_2drotate_2dleft_2deliminate_2d2.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24eo_5fprog_5fbv_2drotate_2dleft_2deliminate_2d2
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fbv_2drotate_2dleft_2deliminate_2d2 s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__eo_prog_bv_rotate_left_eliminate_2 x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fbv_2drotate_2dleft_2deliminate_2d2_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fbv_2drotate_2dright_2deliminate_2d2_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fbv_2drotate_2dright_2deliminate_2d2 s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_bv_rotate_right_eliminate_2.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_bv_rotate_right_eliminate_2.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fbv_2drotate_2dright_2deliminate_2d2 more_0_eo__24eo_5fprog_5fbv_2drotate_2dright_2deliminate_2d2
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a2 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_bv_rotate_right_eliminate_2.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_rotate_right_eliminate_2.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_rotate_right_eliminate_2.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_rotate_right_eliminate_2.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_rotate_right_eliminate_2.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_rotate_right_eliminate_2.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo_mod.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_rotate_right_eliminate_2.case_0
  pat_same v14 a1 with h_v14 h_a1 using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_rotate_right_eliminate_2.case_0
  pat_unapply h_v11 as ⟨v17, v18, x_v17, x_v18, h_v17, h_v18, hn_v17, hn_v18⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_rotate_right_eliminate_2.case_0
  step as ⟨e_v19, he_v19⟩
  store_step with CtorSpec.eo__40bvsize.construct s2 e_v19 (by rw [he_v19]; exact empty_args) hinv2 h64 as ⟨v19, s3, hinv3, h_v19⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18
  pat_same v17 v19 with h_v17 h_v19 using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_rotate_right_eliminate_2.case_0
  pat_same v18 a0 with h_v18 h_a0 using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_rotate_right_eliminate_2.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s3 0#u32 (0) (by scalar_tac) hinv3 h64 as ⟨v20, s4, hinv4, h_v20⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19
  pat_same v4 v20 with h_v4 h_v20 using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_rotate_right_eliminate_2.case_0
  step as ⟨e_v21, he_v21⟩
  store_step with CtorSpec.eo__3d.construct s4 e_v21 (by rw [he_v21]; exact empty_args) hinv4 h64 as ⟨v21, s5, hinv5, h_v21⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20
  step as ⟨e_v22, he_v22⟩
  store_step with CtorSpec.eo_rotate_5fright.construct s5 e_v22 (by rw [he_v22]; rfl) h_a1 hinv5 h64 as ⟨v22, s6, hinv6, h_v22⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21
  store_step with Store.apply_rep s6 v22 a0 _ _ hinv6 h64 h_v22 h_a0 (by ns_tac) (by ns_tac) as ⟨v23, s7, hinv7, h_v23⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22
  store_step with Store.apply_rep s7 v21 v23 _ _ hinv7 h64 h_v21 h_v23 (by ns_tac) (by ns_tac) as ⟨v24, s8, hinv8, h_v24⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23
  store_step with Store.apply_rep s8 v24 a0 _ _ hinv8 h64 h_v24 h_a0 (by ns_tac) (by ns_tac) as ⟨v25, s9, hinv9, h_v25⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24
  case_done hinv9 hG with h_v25 in EoCases.__eo_prog_bv_rotate_right_eliminate_2.case_0 using hn_a0 hn_a1 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v13 hn_v14 hn_v17 hn_v18

/-- logos's `__eo_prog_bv_rotate_right_eliminate_2` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fbv_2drotate_2dright_2deliminate_2d2.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __eo_prog_bv_rotate_right_eliminate_2 x_a0 x_a1 x_a2 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_bv_rotate_right_eliminate_2.case_0 x_a0 x_a1 x_a2] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_bv_rotate_right_eliminate_2
  unfold EoCases.__eo_prog_bv_rotate_right_eliminate_2.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fbv_2drotate_2dright_2deliminate_2d2_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24eo_5fprog_5fbv_2drotate_2dright_2deliminate_2d2 s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_rotate_right_eliminate_2 x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fbv_2drotate_2dright_2deliminate_2d2.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24eo_5fprog_5fbv_2drotate_2dright_2deliminate_2d2
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fbv_2drotate_2dright_2deliminate_2d2_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_bv_rotate_right_eliminate_2.case_0

theorem eo__24eo_5fprog_5fbv_2drotate_2dright_2deliminate_2d2_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fbv_2drotate_2dright_2deliminate_2d2.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24eo_5fprog_5fbv_2drotate_2dright_2deliminate_2d2
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fbv_2drotate_2dright_2deliminate_2d2 s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__eo_prog_bv_rotate_right_eliminate_2 x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fbv_2drotate_2dright_2deliminate_2d2_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fbv_2dsdivo_2deliminate_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fbv_2dsdivo_2deliminate s a0 a1 a2 a3 a4 a5 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_bv_sdivo_eliminate.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_bv_sdivo_eliminate.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fbv_2dsdivo_2deliminate more_0_eo__24eo_5fprog_5fbv_2dsdivo_2deliminate more_1_eo__24eo_5fprog_5fbv_2dsdivo_2deliminate more_2_eo__24eo_5fprog_5fbv_2dsdivo_2deliminate more_3_eo__24eo_5fprog_5fbv_2dsdivo_2deliminate more_4_eo__24eo_5fprog_5fbv_2dsdivo_2deliminate
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a4 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_bv_sdivo_eliminate.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_sdivo_eliminate.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_sdivo_eliminate.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_sdivo_eliminate.case_0
  pat_same v7 a3 with h_v7 h_a3 using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_sdivo_eliminate.case_0
  pat_unapply h_v4 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_sdivo_eliminate.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_sdivo_eliminate.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__2d.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_sdivo_eliminate.case_0
  pat_unapply h_v14 as ⟨v17, v18, x_v17, x_v18, h_v17, h_v18, hn_v17, hn_v18⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_sdivo_eliminate.case_0
  step as ⟨e_v19, he_v19⟩
  store_step with CtorSpec.eo__40bvsize.construct s2 e_v19 (by rw [he_v19]; exact empty_args) hinv2 h64 as ⟨v19, s3, hinv3, h_v19⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18
  pat_same v17 v19 with h_v17 h_v19 using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_sdivo_eliminate.case_0
  pat_same v18 a0 with h_v18 h_a0 using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_sdivo_eliminate.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s3 1#u32 (1) (by scalar_tac) hinv3 h64 as ⟨v20, s4, hinv4, h_v20⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19
  pat_same v11 v20 with h_v11 h_v20 using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_sdivo_eliminate.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a5 as ⟨v22, x_v22, h_v22⟩ else hinv4 hG in EoCases.__eo_prog_bv_sdivo_eliminate.case_0
  pat_unapply h_v22 as ⟨v24, v25, x_v24, x_v25, h_v24, h_v25, hn_v24, hn_v25⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_sdivo_eliminate.case_0
  pat_unapply h_v24 as ⟨v27, v28, x_v27, x_v28, h_v27, h_v28, hn_v27, hn_v28⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_sdivo_eliminate.case_0
  step as ⟨e_v29, he_v29⟩
  store_step with CtorSpec.eo__3d.construct s4 e_v29 (by rw [he_v29]; exact empty_args) hinv4 h64 as ⟨v29, s5, hinv5, h_v29⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28
  pat_same v27 v29 with h_v27 h_v29 using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_sdivo_eliminate.case_0
  pat_same v28 a2 with h_v28 h_a2 using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_sdivo_eliminate.case_0
  pat_unapply h_v25 as ⟨v31, v32, x_v31, x_v32, h_v31, h_v32, hn_v31, hn_v32⟩ using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_sdivo_eliminate.case_0
  step as ⟨e_v33, he_v33⟩
  store_step with CtorSpec.eo__40bvsize.construct s5 e_v33 (by rw [he_v33]; exact empty_args) hinv5 h64 as ⟨v33, s6, hinv6, h_v33⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32
  pat_same v31 v33 with h_v31 h_v33 using hinv6 else hinv6 hG in EoCases.__eo_prog_bv_sdivo_eliminate.case_0
  pat_same v32 a1 with h_v32 h_a1 using hinv6 else hinv6 hG in EoCases.__eo_prog_bv_sdivo_eliminate.case_0
  step as ⟨e_v34, he_v34⟩
  store_step with CtorSpec.eo__3d.construct s6 e_v34 (by rw [he_v34]; exact empty_args) hinv6 h64 as ⟨v34, s7, hinv7, h_v34⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v33
  step as ⟨e_v35, he_v35⟩
  store_step with CtorSpec.eo_bvsdivo.construct s7 e_v35 (by rw [he_v35]; exact empty_args) hinv7 h64 as ⟨v35, s8, hinv8, h_v35⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34
  store_step with Store.apply_rep s8 v35 a0 _ _ hinv8 h64 h_v35 h_a0 (by ns_tac) (by ns_tac) as ⟨v36, s9, hinv9, h_v36⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34 h_v35
  store_step with Store.apply_rep s9 v36 a1 _ _ hinv9 h64 h_v36 h_a1 (by ns_tac) (by ns_tac) as ⟨v37, s10, hinv10, h_v37⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36
  store_step with Store.apply_rep s10 v34 v37 _ _ hinv10 h64 h_v34 h_v37 (by ns_tac) (by ns_tac) as ⟨v38, s11, hinv11, h_v38⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37
  step as ⟨e_v39, he_v39⟩
  store_step with CtorSpec.eo_and.construct s11 e_v39 (by rw [he_v39]; exact empty_args) hinv11 h64 as ⟨v39, s12, hinv12, h_v39⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38
  step as ⟨e_v40, he_v40⟩
  store_step with CtorSpec.eo__3d.construct s12 e_v40 (by rw [he_v40]; exact empty_args) hinv12 h64 as ⟨v40, s13, hinv13, h_v40⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39
  store_step with Store.apply_rep s13 v40 a0 _ _ hinv13 h64 h_v40 h_a0 (by ns_tac) (by ns_tac) as ⟨v41, s14, hinv14, h_v41⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40
  step as ⟨e_v42, he_v42⟩
  store_step with CtorSpec.eo_concat.construct s14 e_v42 (by rw [he_v42]; exact empty_args) hinv14 h64 as ⟨v42, s15, hinv15, h_v42⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s15 1#u32 (1) (by scalar_tac) hinv15 h64 as ⟨v43, s16, hinv16, h_v43⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42
  step as ⟨e_v44, he_v44⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s16 e_v44 (by rw [he_v44]; rfl) h_v43 hinv16 h64 as ⟨v44, s17, hinv17, h_v44⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s17 1#u32 (1) (by scalar_tac) hinv17 h64 as ⟨v45, s18, hinv18, h_v45⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44
  store_step with Store.apply_rep s18 v44 v45 _ _ hinv18 h64 h_v44 h_v45 (by ns_tac) (by ns_tac) as ⟨v46, s19, hinv19, h_v46⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45
  store_step with Store.apply_rep s19 v42 v46 _ _ hinv19 h64 h_v42 h_v46 (by ns_tac) (by ns_tac) as ⟨v47, s20, hinv20, h_v47⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46
  step as ⟨e_v48, he_v48⟩
  store_step with CtorSpec.eo_concat.construct s20 e_v48 (by rw [he_v48]; exact empty_args) hinv20 h64 as ⟨v48, s21, hinv21, h_v48⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47
  step as ⟨e_v49, he_v49⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s21 e_v49 (by rw [he_v49]; rfl) h_a3 hinv21 h64 as ⟨v49, s22, hinv22, h_v49⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s22 0#u32 (0) (by scalar_tac) hinv22 h64 as ⟨v50, s23, hinv23, h_v50⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49
  store_step with Store.apply_rep s23 v49 v50 _ _ hinv23 h64 h_v49 h_v50 (by ns_tac) (by ns_tac) as ⟨v51, s24, hinv24, h_v51⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50
  store_step with Store.apply_rep s24 v48 v51 _ _ hinv24 h64 h_v48 h_v51 (by ns_tac) (by ns_tac) as ⟨v52, s25, hinv25, h_v52⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s25 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv25 h64 as ⟨v53, s26, hinv26, h_v53⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52
  store_step with Store.apply_rep s26 v52 v53 _ _ hinv26 h64 h_v52 h_v53 (by ns_tac) (by ns_tac) as ⟨v54, s27, hinv27, h_v54⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53
  store_step with Store.apply_rep s27 v47 v54 _ _ hinv27 h64 h_v47 h_v54 (by ns_tac) (by ns_tac) as ⟨v55, s28, hinv28, h_v55⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54
  store_step with Store.apply_rep s28 v41 v55 _ _ hinv28 h64 h_v41 h_v55 (by ns_tac) (by ns_tac) as ⟨v56, s29, hinv29, h_v56⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55
  store_step with Store.apply_rep s29 v39 v56 _ _ hinv29 h64 h_v39 h_v56 (by ns_tac) (by ns_tac) as ⟨v57, s30, hinv30, h_v57⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56
  step as ⟨e_v58, he_v58⟩
  store_step with CtorSpec.eo_and.construct s30 e_v58 (by rw [he_v58]; exact empty_args) hinv30 h64 as ⟨v58, s31, hinv31, h_v58⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57
  step as ⟨e_v59, he_v59⟩
  store_step with CtorSpec.eo__3d.construct s31 e_v59 (by rw [he_v59]; exact empty_args) hinv31 h64 as ⟨v59, s32, hinv32, h_v59⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58
  store_step with Store.apply_rep s32 v59 a1 _ _ hinv32 h64 h_v59 h_a1 (by ns_tac) (by ns_tac) as ⟨v60, s33, hinv33, h_v60⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59
  step as ⟨e_v61, he_v61⟩
  store_step with CtorSpec.eo_bvnot.construct s33 e_v61 (by rw [he_v61]; exact empty_args) hinv33 h64 as ⟨v61, s34, hinv34, h_v61⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60
  step as ⟨e_v62, he_v62⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s34 e_v62 (by rw [he_v62]; rfl) h_a2 hinv34 h64 as ⟨v62, s35, hinv35, h_v62⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s35 0#u32 (0) (by scalar_tac) hinv35 h64 as ⟨v63, s36, hinv36, h_v63⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62
  store_step with Store.apply_rep s36 v62 v63 _ _ hinv36 h64 h_v62 h_v63 (by ns_tac) (by ns_tac) as ⟨v64, s37, hinv37, h_v64⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63
  store_step with Store.apply_rep s37 v61 v64 _ _ hinv37 h64 h_v61 h_v64 (by ns_tac) (by ns_tac) as ⟨v65, s38, hinv38, h_v65⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64
  store_step with Store.apply_rep s38 v60 v65 _ _ hinv38 h64 h_v60 h_v65 (by ns_tac) (by ns_tac) as ⟨v66, s39, hinv39, h_v66⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65
  store_step with Store.apply_rep s39 v58 v66 _ _ hinv39 h64 h_v58 h_v66 (by ns_tac) (by ns_tac) as ⟨v67, s40, hinv40, h_v67⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66
  store_step with Store.literal_boolean_spec s40 true hinv40 h64 as ⟨v68, s41, hinv41, h_v68⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67
  store_step with Store.apply_rep s41 v67 v68 _ _ hinv41 h64 h_v67 h_v68 (by ns_tac) (by ns_tac) as ⟨v69, s42, hinv42, h_v69⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68
  store_step with Store.apply_rep s42 v57 v69 _ _ hinv42 h64 h_v57 h_v69 (by ns_tac) (by ns_tac) as ⟨v70, s43, hinv43, h_v70⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69
  store_step with Store.apply_rep s43 v38 v70 _ _ hinv43 h64 h_v38 h_v70 (by ns_tac) (by ns_tac) as ⟨v71, s44, hinv44, h_v71⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70
  case_done hinv44 hG with h_v71 in EoCases.__eo_prog_bv_sdivo_eliminate.case_0 using hn_a0 hn_a1 hn_a2 hn_a3 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v13 hn_v14 hn_v17 hn_v18 hn_v24 hn_v25 hn_v27 hn_v28 hn_v31 hn_v32

/-- logos's `__eo_prog_bv_sdivo_eliminate` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fbv_2dsdivo_2deliminate.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) (hw_a4 : Valid.valid x_a4) (hw_a5 : Valid.valid x_a5) :
    __eo_prog_bv_sdivo_eliminate x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_bv_sdivo_eliminate.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_bv_sdivo_eliminate
  unfold EoCases.__eo_prog_bv_sdivo_eliminate.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fbv_2dsdivo_2deliminate_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) :
    body_eo__24eo_5fprog_5fbv_2dsdivo_2deliminate s a0 a1 a2 a3 a4 a5 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_sdivo_eliminate x_a0 x_a1 x_a2 x_a3 x_a4 x_a5)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fbv_2dsdivo_2deliminate.rust_eq x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3) (by valid_tac hinv h_a4) (by valid_tac hinv h_a5)]
  unfold body_eo__24eo_5fprog_5fbv_2dsdivo_2deliminate
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  stuck_check h_a3 : x_a3 as hn_a3 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fbv_2dsdivo_2deliminate_spec n ih s a0 a1 a2 a3 a4 a5 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 hn_a0 hn_a1 hn_a2 hn_a3
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 using hn_a0 hn_a1 hn_a2 hn_a3
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hn_a3 hc0 in EoCases.__eo_prog_bv_sdivo_eliminate.case_0

theorem eo__24eo_5fprog_5fbv_2dsdivo_2deliminate_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fbv_2dsdivo_2deliminate.Spec n := by
  intro s a0 a1 a2 a3 a4 a5 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5
  unfold eo__24eo_5fprog_5fbv_2dsdivo_2deliminate
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fbv_2dsdivo_2deliminate s1 a0 a1 a2 a3 a4 a5) (fun s' t => Represents.rep s' t (__eo_prog_bv_sdivo_eliminate x_a0 x_a1 x_a2 x_a3 x_a4 x_a5))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fbv_2dsdivo_2deliminate_spec m (ih m hm) s1 a0 a1 a2 a3 a4 a5 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn) (by congr_one h_a4 hn) (by congr_one h_a5 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fbv_2dsge_2deliminate_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fbv_2dsge_2deliminate s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_bv_sge_eliminate.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_bv_sge_eliminate.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fbv_2dsge_2deliminate
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_bvsge.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a1 _ _ hinv3 h64 h_v2 h_a1 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v0 v3 _ _ hinv4 h64 h_v0 h_v3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo_bvsle.construct s5 e_v5 (by rw [he_v5]; exact empty_args) hinv5 h64 as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4
  store_step with Store.apply_rep s6 v5 a1 _ _ hinv6 h64 h_v5 h_a1 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with Store.apply_rep s7 v6 a0 _ _ hinv7 h64 h_v6 h_a0 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  store_step with Store.apply_rep s8 v4 v7 _ _ hinv8 h64 h_v4 h_v7 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  case_done hinv9 hG with h_v8 in EoCases.__eo_prog_bv_sge_eliminate.case_0 using hn_a0 hn_a1

/-- logos's `__eo_prog_bv_sge_eliminate` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fbv_2dsge_2deliminate.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_bv_sge_eliminate x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_bv_sge_eliminate.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_bv_sge_eliminate
  unfold EoCases.__eo_prog_bv_sge_eliminate.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fbv_2dsge_2deliminate_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5fbv_2dsge_2deliminate s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_sge_eliminate x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fbv_2dsge_2deliminate.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5fbv_2dsge_2deliminate
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fbv_2dsge_2deliminate_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_bv_sge_eliminate.case_0

theorem eo__24eo_5fprog_5fbv_2dsge_2deliminate_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fbv_2dsge_2deliminate.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5fbv_2dsge_2deliminate
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fbv_2dsge_2deliminate s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_bv_sge_eliminate x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fbv_2dsge_2deliminate_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fbv_2dsgt_2deliminate_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fbv_2dsgt_2deliminate s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_bv_sgt_eliminate.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_bv_sgt_eliminate.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fbv_2dsgt_2deliminate
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_bvsgt.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a1 _ _ hinv3 h64 h_v2 h_a1 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v0 v3 _ _ hinv4 h64 h_v0 h_v3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo_bvslt.construct s5 e_v5 (by rw [he_v5]; exact empty_args) hinv5 h64 as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4
  store_step with Store.apply_rep s6 v5 a1 _ _ hinv6 h64 h_v5 h_a1 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with Store.apply_rep s7 v6 a0 _ _ hinv7 h64 h_v6 h_a0 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  store_step with Store.apply_rep s8 v4 v7 _ _ hinv8 h64 h_v4 h_v7 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  case_done hinv9 hG with h_v8 in EoCases.__eo_prog_bv_sgt_eliminate.case_0 using hn_a0 hn_a1

/-- logos's `__eo_prog_bv_sgt_eliminate` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fbv_2dsgt_2deliminate.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_bv_sgt_eliminate x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_bv_sgt_eliminate.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_bv_sgt_eliminate
  unfold EoCases.__eo_prog_bv_sgt_eliminate.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fbv_2dsgt_2deliminate_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5fbv_2dsgt_2deliminate s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_sgt_eliminate x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fbv_2dsgt_2deliminate.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5fbv_2dsgt_2deliminate
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fbv_2dsgt_2deliminate_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_bv_sgt_eliminate.case_0

theorem eo__24eo_5fprog_5fbv_2dsgt_2deliminate_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fbv_2dsgt_2deliminate.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5fbv_2dsgt_2deliminate
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fbv_2dsgt_2deliminate s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_bv_sgt_eliminate x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fbv_2dsgt_2deliminate_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d0_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d0 s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_bv_shl_by_const_0.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_bv_shl_by_const_0.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d0
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_bvshl.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s3 e_v3 (by rw [he_v3]; rfl) h_a1 hinv3 h64 as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s4 0#u32 (0) (by scalar_tac) hinv4 h64 as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3
  store_step with Store.apply_rep s5 v3 v4 _ _ hinv5 h64 h_v3 h_v4 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4
  store_step with Store.apply_rep s6 v2 v5 _ _ hinv6 h64 h_v2 h_v5 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with Store.apply_rep s7 v0 v6 _ _ hinv7 h64 h_v0 h_v6 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  store_step with Store.apply_rep s8 v7 a0 _ _ hinv8 h64 h_v7 h_a0 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  case_done hinv9 hG with h_v8 in EoCases.__eo_prog_bv_shl_by_const_0.case_0 using hn_a0 hn_a1

/-- logos's `__eo_prog_bv_shl_by_const_0` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d0.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_bv_shl_by_const_0 x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_bv_shl_by_const_0.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_bv_shl_by_const_0
  unfold EoCases.__eo_prog_bv_shl_by_const_0.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d0_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d0 s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_shl_by_const_0 x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d0.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d0
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d0_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_bv_shl_by_const_0.case_0

theorem eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d0_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d0.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d0
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d0 s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_bv_shl_by_const_0 x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d0_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d1_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d1 s a0 a1 a2 a3 a4 a5 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_bv_shl_by_const_1.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_bv_shl_by_const_1.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d1 more_0_eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d1 more_1_eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d1 more_2_eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d1 more_3_eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d1 more_4_eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d1
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a4 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_bv_shl_by_const_1.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_shl_by_const_1.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_shl_by_const_1.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_shl_by_const_1.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_shl_by_const_1.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_shl_by_const_1.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__3c.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_shl_by_const_1.case_0
  pat_same v14 a1 with h_v14 h_a1 using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_shl_by_const_1.case_0
  pat_unapply h_v11 as ⟨v17, v18, x_v17, x_v18, h_v17, h_v18, hn_v17, hn_v18⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_shl_by_const_1.case_0
  step as ⟨e_v19, he_v19⟩
  store_step with CtorSpec.eo__40bvsize.construct s2 e_v19 (by rw [he_v19]; exact empty_args) hinv2 h64 as ⟨v19, s3, hinv3, h_v19⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18
  pat_same v17 v19 with h_v17 h_v19 using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_shl_by_const_1.case_0
  pat_same v18 a0 with h_v18 h_a0 using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_shl_by_const_1.case_0
  store_step with Store.literal_boolean_spec s3 true hinv3 h64 as ⟨v20, s4, hinv4, h_v20⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19
  pat_same v4 v20 with h_v4 h_v20 using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_shl_by_const_1.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a5 as ⟨v22, x_v22, h_v22⟩ else hinv4 hG in EoCases.__eo_prog_bv_shl_by_const_1.case_0
  pat_unapply h_v22 as ⟨v24, v25, x_v24, x_v25, h_v24, h_v25, hn_v24, hn_v25⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_shl_by_const_1.case_0
  pat_unapply h_v24 as ⟨v27, v28, x_v27, x_v28, h_v27, h_v28, hn_v27, hn_v28⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_shl_by_const_1.case_0
  step as ⟨e_v29, he_v29⟩
  store_step with CtorSpec.eo__3d.construct s4 e_v29 (by rw [he_v29]; exact empty_args) hinv4 h64 as ⟨v29, s5, hinv5, h_v29⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28
  pat_same v27 v29 with h_v27 h_v29 using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_shl_by_const_1.case_0
  pat_same v28 a3 with h_v28 h_a3 using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_shl_by_const_1.case_0
  pat_unapply h_v25 as ⟨v31, v32, x_v31, x_v32, h_v31, h_v32, hn_v31, hn_v32⟩ using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_shl_by_const_1.case_0
  pat_unapply h_v31 as ⟨v34, v35, x_v34, x_v35, h_v34, h_v35, hn_v34, hn_v35⟩ using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_shl_by_const_1.case_0
  step as ⟨e_v36, he_v36⟩
  store_step with CtorSpec.eo__2d.construct s5 e_v36 (by rw [he_v36]; exact empty_args) hinv5 h64 as ⟨v36, s6, hinv6, h_v36⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35
  pat_same v34 v36 with h_v34 h_v36 using hinv6 else hinv6 hG in EoCases.__eo_prog_bv_shl_by_const_1.case_0
  pat_unapply h_v35 as ⟨v38, v39, x_v38, x_v39, h_v38, h_v39, hn_v38, hn_v39⟩ using hinv6 else hinv6 hG in EoCases.__eo_prog_bv_shl_by_const_1.case_0
  step as ⟨e_v40, he_v40⟩
  store_step with CtorSpec.eo__40bvsize.construct s6 e_v40 (by rw [he_v40]; exact empty_args) hinv6 h64 as ⟨v40, s7, hinv7, h_v40⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39
  pat_same v38 v40 with h_v38 h_v40 using hinv7 else hinv7 hG in EoCases.__eo_prog_bv_shl_by_const_1.case_0
  pat_same v39 a0 with h_v39 h_a0 using hinv7 else hinv7 hG in EoCases.__eo_prog_bv_shl_by_const_1.case_0
  pat_unapply h_v32 as ⟨v42, v43, x_v42, x_v43, h_v42, h_v43, hn_v42, hn_v43⟩ using hinv7 else hinv7 hG in EoCases.__eo_prog_bv_shl_by_const_1.case_0
  pat_unapply h_v42 as ⟨v45, v46, x_v45, x_v46, h_v45, h_v46, hn_v45, hn_v46⟩ using hinv7 else hinv7 hG in EoCases.__eo_prog_bv_shl_by_const_1.case_0
  step as ⟨e_v47, he_v47⟩
  store_step with CtorSpec.eo__2b.construct s7 e_v47 (by rw [he_v47]; exact empty_args) hinv7 h64 as ⟨v47, s8, hinv8, h_v47⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v45 h_v46
  pat_same v45 v47 with h_v45 h_v47 using hinv8 else hinv8 hG in EoCases.__eo_prog_bv_shl_by_const_1.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s8 1#u32 (1) (by scalar_tac) hinv8 h64 as ⟨v48, s9, hinv9, h_v48⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v45 h_v46 h_v47
  pat_same v46 v48 with h_v46 h_v48 using hinv9 else hinv9 hG in EoCases.__eo_prog_bv_shl_by_const_1.case_0
  pat_unapply h_v43 as ⟨v50, v51, x_v50, x_v51, h_v50, h_v51, hn_v50, hn_v51⟩ using hinv9 else hinv9 hG in EoCases.__eo_prog_bv_shl_by_const_1.case_0
  pat_unapply h_v50 as ⟨v53, v54, x_v53, x_v54, h_v53, h_v54, hn_v53, hn_v54⟩ using hinv9 else hinv9 hG in EoCases.__eo_prog_bv_shl_by_const_1.case_0
  step as ⟨e_v55, he_v55⟩
  store_step with CtorSpec.eo__2b.construct s9 e_v55 (by rw [he_v55]; exact empty_args) hinv9 h64 as ⟨v55, s10, hinv10, h_v55⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v45 h_v46 h_v47 h_v48 h_v50 h_v51 h_v53 h_v54
  pat_same v53 v55 with h_v53 h_v55 using hinv10 else hinv10 hG in EoCases.__eo_prog_bv_shl_by_const_1.case_0
  pat_same v54 a1 with h_v54 h_a1 using hinv10 else hinv10 hG in EoCases.__eo_prog_bv_shl_by_const_1.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s10 0#u32 (0) (by scalar_tac) hinv10 h64 as ⟨v56, s11, hinv11, h_v56⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v45 h_v46 h_v47 h_v48 h_v50 h_v51 h_v53 h_v54 h_v55
  pat_same v51 v56 with h_v51 h_v56 using hinv11 else hinv11 hG in EoCases.__eo_prog_bv_shl_by_const_1.case_0
  step as ⟨e_v57, he_v57⟩
  store_step with CtorSpec.eo__3d.construct s11 e_v57 (by rw [he_v57]; exact empty_args) hinv11 h64 as ⟨v57, s12, hinv12, h_v57⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v45 h_v46 h_v47 h_v48 h_v50 h_v51 h_v53 h_v54 h_v55 h_v56
  step as ⟨e_v58, he_v58⟩
  store_step with CtorSpec.eo_bvshl.construct s12 e_v58 (by rw [he_v58]; exact empty_args) hinv12 h64 as ⟨v58, s13, hinv13, h_v58⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v45 h_v46 h_v47 h_v48 h_v50 h_v51 h_v53 h_v54 h_v55 h_v56 h_v57
  store_step with Store.apply_rep s13 v58 a0 _ _ hinv13 h64 h_v58 h_a0 (by ns_tac) (by ns_tac) as ⟨v59, s14, hinv14, h_v59⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v45 h_v46 h_v47 h_v48 h_v50 h_v51 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58
  step as ⟨e_v60, he_v60⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s14 e_v60 (by rw [he_v60]; rfl) h_a2 hinv14 h64 as ⟨v60, s15, hinv15, h_v60⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v45 h_v46 h_v47 h_v48 h_v50 h_v51 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59
  store_step with Store.apply_rep s15 v60 a1 _ _ hinv15 h64 h_v60 h_a1 (by ns_tac) (by ns_tac) as ⟨v61, s16, hinv16, h_v61⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v45 h_v46 h_v47 h_v48 h_v50 h_v51 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60
  store_step with Store.apply_rep s16 v59 v61 _ _ hinv16 h64 h_v59 h_v61 (by ns_tac) (by ns_tac) as ⟨v62, s17, hinv17, h_v62⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v45 h_v46 h_v47 h_v48 h_v50 h_v51 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61
  store_step with Store.apply_rep s17 v57 v62 _ _ hinv17 h64 h_v57 h_v62 (by ns_tac) (by ns_tac) as ⟨v63, s18, hinv18, h_v63⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v45 h_v46 h_v47 h_v48 h_v50 h_v51 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62
  step as ⟨e_v64, he_v64⟩
  store_step with CtorSpec.eo_concat.construct s18 e_v64 (by rw [he_v64]; exact empty_args) hinv18 h64 as ⟨v64, s19, hinv19, h_v64⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v45 h_v46 h_v47 h_v48 h_v50 h_v51 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s19 0#u32 (0) (by scalar_tac) hinv19 h64 as ⟨v65, s20, hinv20, h_v65⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v45 h_v46 h_v47 h_v48 h_v50 h_v51 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64
  step as ⟨e_v66, he_v66⟩
  store_step with CtorSpec.eo_extract.construct s20 e_v66 (by rw [he_v66]; rfl) h_a3 h_v65 hinv20 h64 as ⟨v66, s21, hinv21, h_v66⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v45 h_v46 h_v47 h_v48 h_v50 h_v51 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65
  store_step with Store.apply_rep s21 v66 a0 _ _ hinv21 h64 h_v66 h_a0 (by ns_tac) (by ns_tac) as ⟨v67, s22, hinv22, h_v67⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v45 h_v46 h_v47 h_v48 h_v50 h_v51 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66
  store_step with Store.apply_rep s22 v64 v67 _ _ hinv22 h64 h_v64 h_v67 (by ns_tac) (by ns_tac) as ⟨v68, s23, hinv23, h_v68⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v45 h_v46 h_v47 h_v48 h_v50 h_v51 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67
  step as ⟨e_v69, he_v69⟩
  store_step with CtorSpec.eo_concat.construct s23 e_v69 (by rw [he_v69]; exact empty_args) hinv23 h64 as ⟨v69, s24, hinv24, h_v69⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v45 h_v46 h_v47 h_v48 h_v50 h_v51 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68
  step as ⟨e_v70, he_v70⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s24 e_v70 (by rw [he_v70]; rfl) h_a1 hinv24 h64 as ⟨v70, s25, hinv25, h_v70⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v45 h_v46 h_v47 h_v48 h_v50 h_v51 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s25 0#u32 (0) (by scalar_tac) hinv25 h64 as ⟨v71, s26, hinv26, h_v71⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v45 h_v46 h_v47 h_v48 h_v50 h_v51 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70
  store_step with Store.apply_rep s26 v70 v71 _ _ hinv26 h64 h_v70 h_v71 (by ns_tac) (by ns_tac) as ⟨v72, s27, hinv27, h_v72⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v45 h_v46 h_v47 h_v48 h_v50 h_v51 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70 h_v71
  store_step with Store.apply_rep s27 v69 v72 _ _ hinv27 h64 h_v69 h_v72 (by ns_tac) (by ns_tac) as ⟨v73, s28, hinv28, h_v73⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v45 h_v46 h_v47 h_v48 h_v50 h_v51 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70 h_v71 h_v72
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s28 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv28 h64 as ⟨v74, s29, hinv29, h_v74⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v45 h_v46 h_v47 h_v48 h_v50 h_v51 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70 h_v71 h_v72 h_v73
  store_step with Store.apply_rep s29 v73 v74 _ _ hinv29 h64 h_v73 h_v74 (by ns_tac) (by ns_tac) as ⟨v75, s30, hinv30, h_v75⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v45 h_v46 h_v47 h_v48 h_v50 h_v51 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70 h_v71 h_v72 h_v73 h_v74
  store_step with Store.apply_rep s30 v68 v75 _ _ hinv30 h64 h_v68 h_v75 (by ns_tac) (by ns_tac) as ⟨v76, s31, hinv31, h_v76⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v45 h_v46 h_v47 h_v48 h_v50 h_v51 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70 h_v71 h_v72 h_v73 h_v74 h_v75
  store_step with Store.apply_rep s31 v63 v76 _ _ hinv31 h64 h_v63 h_v76 (by ns_tac) (by ns_tac) as ⟨v77, s32, hinv32, h_v77⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v45 h_v46 h_v47 h_v48 h_v50 h_v51 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70 h_v71 h_v72 h_v73 h_v74 h_v75 h_v76
  case_done hinv32 hG with h_v77 in EoCases.__eo_prog_bv_shl_by_const_1.case_0 using hn_a0 hn_a1 hn_a2 hn_a3 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v13 hn_v14 hn_v17 hn_v18 hn_v24 hn_v25 hn_v27 hn_v28 hn_v31 hn_v32 hn_v34 hn_v35 hn_v38 hn_v39 hn_v42 hn_v43 hn_v45 hn_v46 hn_v50 hn_v51 hn_v53 hn_v54

/-- logos's `__eo_prog_bv_shl_by_const_1` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d1.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) (hw_a4 : Valid.valid x_a4) (hw_a5 : Valid.valid x_a5) :
    __eo_prog_bv_shl_by_const_1 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_bv_shl_by_const_1.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_bv_shl_by_const_1
  unfold EoCases.__eo_prog_bv_shl_by_const_1.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d1_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) :
    body_eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d1 s a0 a1 a2 a3 a4 a5 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_shl_by_const_1 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d1.rust_eq x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3) (by valid_tac hinv h_a4) (by valid_tac hinv h_a5)]
  unfold body_eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d1
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  stuck_check h_a3 : x_a3 as hn_a3 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d1_spec n ih s a0 a1 a2 a3 a4 a5 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 hn_a0 hn_a1 hn_a2 hn_a3
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 using hn_a0 hn_a1 hn_a2 hn_a3
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hn_a3 hc0 in EoCases.__eo_prog_bv_shl_by_const_1.case_0

theorem eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d1_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d1.Spec n := by
  intro s a0 a1 a2 a3 a4 a5 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5
  unfold eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d1
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d1 s1 a0 a1 a2 a3 a4 a5) (fun s' t => Represents.rep s' t (__eo_prog_bv_shl_by_const_1 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d1_spec m (ih m hm) s1 a0 a1 a2 a3 a4 a5 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn) (by congr_one h_a4 hn) (by congr_one h_a5 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d2_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 a6 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) (h_a6 : Represents.rep s a6 x_a6) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d2 s a0 a1 a2 a3 a4 a5 a6 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_bv_shl_by_const_2.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_bv_shl_by_const_2.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d2 more_0_eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d2 more_1_eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d2 more_2_eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d2 more_3_eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d2
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a4 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_bv_shl_by_const_2.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_shl_by_const_2.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_shl_by_const_2.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v1 h_v3 h_v4 h_v6 h_v7
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_shl_by_const_2.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_shl_by_const_2.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_shl_by_const_2.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__3e_3d.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_shl_by_const_2.case_0
  pat_same v14 a1 with h_v14 h_a1 using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_shl_by_const_2.case_0
  pat_unapply h_v11 as ⟨v17, v18, x_v17, x_v18, h_v17, h_v18, hn_v17, hn_v18⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_shl_by_const_2.case_0
  step as ⟨e_v19, he_v19⟩
  store_step with CtorSpec.eo__40bvsize.construct s2 e_v19 (by rw [he_v19]; exact empty_args) hinv2 h64 as ⟨v19, s3, hinv3, h_v19⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18
  pat_same v17 v19 with h_v17 h_v19 using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_shl_by_const_2.case_0
  pat_same v18 a0 with h_v18 h_a0 using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_shl_by_const_2.case_0
  store_step with Store.literal_boolean_spec s3 true hinv3 h64 as ⟨v20, s4, hinv4, h_v20⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19
  pat_same v4 v20 with h_v4 h_v20 using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_shl_by_const_2.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a5 as ⟨v22, x_v22, h_v22⟩ else hinv4 hG in EoCases.__eo_prog_bv_shl_by_const_2.case_0
  pat_unapply h_v22 as ⟨v24, v25, x_v24, x_v25, h_v24, h_v25, hn_v24, hn_v25⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_shl_by_const_2.case_0
  pat_unapply h_v24 as ⟨v27, v28, x_v27, x_v28, h_v27, h_v28, hn_v27, hn_v28⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_shl_by_const_2.case_0
  step as ⟨e_v29, he_v29⟩
  store_step with CtorSpec.eo__3d.construct s4 e_v29 (by rw [he_v29]; exact empty_args) hinv4 h64 as ⟨v29, s5, hinv5, h_v29⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28
  pat_same v27 v29 with h_v27 h_v29 using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_shl_by_const_2.case_0
  pat_unapply h_v28 as ⟨v31, v32, x_v31, x_v32, h_v31, h_v32, hn_v31, hn_v32⟩ using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_shl_by_const_2.case_0
  pat_unapply h_v31 as ⟨v34, v35, x_v34, x_v35, h_v34, h_v35, hn_v34, hn_v35⟩ using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_shl_by_const_2.case_0
  step as ⟨e_v36, he_v36⟩
  store_step with CtorSpec.eo__3c.construct s5 e_v36 (by rw [he_v36]; exact empty_args) hinv5 h64 as ⟨v36, s6, hinv6, h_v36⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35
  pat_same v34 v36 with h_v34 h_v36 using hinv6 else hinv6 hG in EoCases.__eo_prog_bv_shl_by_const_2.case_0
  pat_same v35 a1 with h_v35 h_a1 using hinv6 else hinv6 hG in EoCases.__eo_prog_bv_shl_by_const_2.case_0
  pat_unapply h_v32 as ⟨v38, v39, x_v38, x_v39, h_v38, h_v39, hn_v38, hn_v39⟩ using hinv6 else hinv6 hG in EoCases.__eo_prog_bv_shl_by_const_2.case_0
  step as ⟨e_v40, he_v40⟩
  store_step with CtorSpec.eo_int_2epow2.construct s6 e_v40 (by rw [he_v40]; exact empty_args) hinv6 h64 as ⟨v40, s7, hinv7, h_v40⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39
  pat_same v38 v40 with h_v38 h_v40 using hinv7 else hinv7 hG in EoCases.__eo_prog_bv_shl_by_const_2.case_0
  pat_unapply h_v39 as ⟨v42, v43, x_v42, x_v43, h_v42, h_v43, hn_v42, hn_v43⟩ using hinv7 else hinv7 hG in EoCases.__eo_prog_bv_shl_by_const_2.case_0
  step as ⟨e_v44, he_v44⟩
  store_step with CtorSpec.eo__40bvsize.construct s7 e_v44 (by rw [he_v44]; exact empty_args) hinv7 h64 as ⟨v44, s8, hinv8, h_v44⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43
  pat_same v42 v44 with h_v42 h_v44 using hinv8 else hinv8 hG in EoCases.__eo_prog_bv_shl_by_const_2.case_0
  pat_same v43 a0 with h_v43 h_a0 using hinv8 else hinv8 hG in EoCases.__eo_prog_bv_shl_by_const_2.case_0
  store_step with Store.literal_boolean_spec s8 true hinv8 h64 as ⟨v45, s9, hinv9, h_v45⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v44
  pat_same v25 v45 with h_v25 h_v45 using hinv9 else hinv9 hG in EoCases.__eo_prog_bv_shl_by_const_2.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a6 as ⟨v47, x_v47, h_v47⟩ else hinv9 hG in EoCases.__eo_prog_bv_shl_by_const_2.case_0
  pat_unapply h_v47 as ⟨v49, v50, x_v49, x_v50, h_v49, h_v50, hn_v49, hn_v50⟩ using hinv9 else hinv9 hG in EoCases.__eo_prog_bv_shl_by_const_2.case_0
  pat_unapply h_v49 as ⟨v52, v53, x_v52, x_v53, h_v52, h_v53, hn_v52, hn_v53⟩ using hinv9 else hinv9 hG in EoCases.__eo_prog_bv_shl_by_const_2.case_0
  step as ⟨e_v54, he_v54⟩
  store_step with CtorSpec.eo__3d.construct s9 e_v54 (by rw [he_v54]; exact empty_args) hinv9 h64 as ⟨v54, s10, hinv10, h_v54⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v44 h_v45 h_v47 h_v49 h_v50 h_v52 h_v53
  pat_same v52 v54 with h_v52 h_v54 using hinv10 else hinv10 hG in EoCases.__eo_prog_bv_shl_by_const_2.case_0
  pat_same v53 a3 with h_v53 h_a3 using hinv10 else hinv10 hG in EoCases.__eo_prog_bv_shl_by_const_2.case_0
  pat_unapply h_v50 as ⟨v56, v57, x_v56, x_v57, h_v56, h_v57, hn_v56, hn_v57⟩ using hinv10 else hinv10 hG in EoCases.__eo_prog_bv_shl_by_const_2.case_0
  step as ⟨e_v58, he_v58⟩
  store_step with CtorSpec.eo__40bvsize.construct s10 e_v58 (by rw [he_v58]; exact empty_args) hinv10 h64 as ⟨v58, s11, hinv11, h_v58⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v44 h_v45 h_v47 h_v49 h_v50 h_v52 h_v53 h_v54 h_v56 h_v57
  pat_same v56 v58 with h_v56 h_v58 using hinv11 else hinv11 hG in EoCases.__eo_prog_bv_shl_by_const_2.case_0
  pat_same v57 a0 with h_v57 h_a0 using hinv11 else hinv11 hG in EoCases.__eo_prog_bv_shl_by_const_2.case_0
  step as ⟨e_v59, he_v59⟩
  store_step with CtorSpec.eo__3d.construct s11 e_v59 (by rw [he_v59]; exact empty_args) hinv11 h64 as ⟨v59, s12, hinv12, h_v59⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v44 h_v45 h_v47 h_v49 h_v50 h_v52 h_v53 h_v54 h_v56 h_v57 h_v58
  step as ⟨e_v60, he_v60⟩
  store_step with CtorSpec.eo_bvshl.construct s12 e_v60 (by rw [he_v60]; exact empty_args) hinv12 h64 as ⟨v60, s13, hinv13, h_v60⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v44 h_v45 h_v47 h_v49 h_v50 h_v52 h_v53 h_v54 h_v56 h_v57 h_v58 h_v59
  store_step with Store.apply_rep s13 v60 a0 _ _ hinv13 h64 h_v60 h_a0 (by ns_tac) (by ns_tac) as ⟨v61, s14, hinv14, h_v61⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v44 h_v45 h_v47 h_v49 h_v50 h_v52 h_v53 h_v54 h_v56 h_v57 h_v58 h_v59 h_v60
  step as ⟨e_v62, he_v62⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s14 e_v62 (by rw [he_v62]; rfl) h_a2 hinv14 h64 as ⟨v62, s15, hinv15, h_v62⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v44 h_v45 h_v47 h_v49 h_v50 h_v52 h_v53 h_v54 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61
  store_step with Store.apply_rep s15 v62 a1 _ _ hinv15 h64 h_v62 h_a1 (by ns_tac) (by ns_tac) as ⟨v63, s16, hinv16, h_v63⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v44 h_v45 h_v47 h_v49 h_v50 h_v52 h_v53 h_v54 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62
  store_step with Store.apply_rep s16 v61 v63 _ _ hinv16 h64 h_v61 h_v63 (by ns_tac) (by ns_tac) as ⟨v64, s17, hinv17, h_v64⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v44 h_v45 h_v47 h_v49 h_v50 h_v52 h_v53 h_v54 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63
  store_step with Store.apply_rep s17 v59 v64 _ _ hinv17 h64 h_v59 h_v64 (by ns_tac) (by ns_tac) as ⟨v65, s18, hinv18, h_v65⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v44 h_v45 h_v47 h_v49 h_v50 h_v52 h_v53 h_v54 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64
  step as ⟨e_v66, he_v66⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s18 e_v66 (by rw [he_v66]; rfl) h_a3 hinv18 h64 as ⟨v66, s19, hinv19, h_v66⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v44 h_v45 h_v47 h_v49 h_v50 h_v52 h_v53 h_v54 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s19 0#u32 (0) (by scalar_tac) hinv19 h64 as ⟨v67, s20, hinv20, h_v67⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v44 h_v45 h_v47 h_v49 h_v50 h_v52 h_v53 h_v54 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66
  store_step with Store.apply_rep s20 v66 v67 _ _ hinv20 h64 h_v66 h_v67 (by ns_tac) (by ns_tac) as ⟨v68, s21, hinv21, h_v68⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v44 h_v45 h_v47 h_v49 h_v50 h_v52 h_v53 h_v54 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67
  store_step with Store.apply_rep s21 v65 v68 _ _ hinv21 h64 h_v65 h_v68 (by ns_tac) (by ns_tac) as ⟨v69, s22, hinv22, h_v69⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v44 h_v45 h_v47 h_v49 h_v50 h_v52 h_v53 h_v54 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68
  case_done hinv22 hG with h_v69 in EoCases.__eo_prog_bv_shl_by_const_2.case_0 using hn_a0 hn_a1 hn_a2 hn_a3 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v13 hn_v14 hn_v17 hn_v18 hn_v24 hn_v25 hn_v27 hn_v28 hn_v31 hn_v32 hn_v34 hn_v35 hn_v38 hn_v39 hn_v42 hn_v43 hn_v49 hn_v50 hn_v52 hn_v53 hn_v56 hn_v57

/-- logos's `__eo_prog_bv_shl_by_const_2` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d2.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) (hw_a4 : Valid.valid x_a4) (hw_a5 : Valid.valid x_a5) (hw_a6 : Valid.valid x_a6) :
    __eo_prog_bv_shl_by_const_2 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_bv_shl_by_const_2.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_bv_shl_by_const_2
  unfold EoCases.__eo_prog_bv_shl_by_const_2.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d2_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 a6 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) (h_a6 : Represents.rep s a6 x_a6) :
    body_eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d2 s a0 a1 a2 a3 a4 a5 a6 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_shl_by_const_2 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d2.rust_eq x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3) (by valid_tac hinv h_a4) (by valid_tac hinv h_a5) (by valid_tac hinv h_a6)]
  unfold body_eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d2
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  stuck_check h_a3 : x_a3 as hn_a3 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d2_spec n ih s a0 a1 a2 a3 a4 a5 a6 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 hn_a0 hn_a1 hn_a2 hn_a3
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 using hn_a0 hn_a1 hn_a2 hn_a3
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hn_a3 hc0 in EoCases.__eo_prog_bv_shl_by_const_2.case_0

theorem eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d2_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d2.Spec n := by
  intro s a0 a1 a2 a3 a4 a5 a6 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6
  unfold eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d2
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d2 s1 a0 a1 a2 a3 a4 a5 a6) (fun s' t => Represents.rep s' t (__eo_prog_bv_shl_by_const_2 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d2_spec m (ih m hm) s1 a0 a1 a2 a3 a4 a5 a6 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn) (by congr_one h_a4 hn) (by congr_one h_a5 hn) (by congr_one h_a6 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fbv_2dshl_2dzero_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fbv_2dshl_2dzero s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_bv_shl_zero.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_bv_shl_zero.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fbv_2dshl_2dzero
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_bvshl.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s2 e_v2 (by rw [he_v2]; rfl) h_a1 hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s3 0#u32 (0) (by scalar_tac) hinv3 h64 as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v2 v3 _ _ hinv4 h64 h_v2 h_v3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3
  store_step with Store.apply_rep s5 v1 v4 _ _ hinv5 h64 h_v1 h_v4 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4
  store_step with Store.apply_rep s6 v5 a0 _ _ hinv6 h64 h_v5 h_a0 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with Store.apply_rep s7 v0 v6 _ _ hinv7 h64 h_v0 h_v6 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s8 e_v8 (by rw [he_v8]; rfl) h_a1 hinv8 h64 as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s9 0#u32 (0) (by scalar_tac) hinv9 h64 as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
  store_step with Store.apply_rep s10 v8 v9 _ _ hinv10 h64 h_v8 h_v9 (by ns_tac) (by ns_tac) as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  store_step with Store.apply_rep s11 v7 v10 _ _ hinv11 h64 h_v7 h_v10 (by ns_tac) (by ns_tac) as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
  case_done hinv12 hG with h_v11 in EoCases.__eo_prog_bv_shl_zero.case_0 using hn_a0 hn_a1

/-- logos's `__eo_prog_bv_shl_zero` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fbv_2dshl_2dzero.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_bv_shl_zero x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_bv_shl_zero.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_bv_shl_zero
  unfold EoCases.__eo_prog_bv_shl_zero.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fbv_2dshl_2dzero_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5fbv_2dshl_2dzero s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_shl_zero x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fbv_2dshl_2dzero.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5fbv_2dshl_2dzero
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fbv_2dshl_2dzero_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_bv_shl_zero.case_0

theorem eo__24eo_5fprog_5fbv_2dshl_2dzero_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fbv_2dshl_2dzero.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5fbv_2dshl_2dzero
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fbv_2dshl_2dzero s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_bv_shl_zero x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fbv_2dshl_2dzero_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fbv_2dsign_2dextend_2deliminate_2d0_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fbv_2dsign_2dextend_2deliminate_2d0 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_bv_sign_extend_eliminate_0.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_bv_sign_extend_eliminate_0.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fbv_2dsign_2dextend_2deliminate_2d0
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s1 0#u32 (0) (by scalar_tac) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo_sign_5fextend.construct s2 e_v2 (by rw [he_v2]; rfl) h_v1 hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a0 _ _ hinv3 h64 h_v2 h_a0 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v0 v3 _ _ hinv4 h64 h_v0 h_v3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3
  store_step with Store.apply_rep s5 v4 a0 _ _ hinv5 h64 h_v4 h_a0 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4
  case_done hinv6 hG with h_v5 in EoCases.__eo_prog_bv_sign_extend_eliminate_0.case_0 using hn_a0

/-- logos's `__eo_prog_bv_sign_extend_eliminate_0` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fbv_2dsign_2dextend_2deliminate_2d0.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_bv_sign_extend_eliminate_0 x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_bv_sign_extend_eliminate_0.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_bv_sign_extend_eliminate_0
  unfold EoCases.__eo_prog_bv_sign_extend_eliminate_0.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fbv_2dsign_2dextend_2deliminate_2d0_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fbv_2dsign_2dextend_2deliminate_2d0 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_sign_extend_eliminate_0 x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fbv_2dsign_2dextend_2deliminate_2d0.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fbv_2dsign_2dextend_2deliminate_2d0
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fbv_2dsign_2dextend_2deliminate_2d0_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_bv_sign_extend_eliminate_0.case_0

theorem eo__24eo_5fprog_5fbv_2dsign_2dextend_2deliminate_2d0_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fbv_2dsign_2dextend_2deliminate_2d0.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fbv_2dsign_2dextend_2deliminate_2d0
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fbv_2dsign_2dextend_2deliminate_2d0 s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_bv_sign_extend_eliminate_0 x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fbv_2dsign_2dextend_2deliminate_2d0_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fbv_2dsle_2deliminate_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fbv_2dsle_2deliminate s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_bv_sle_eliminate.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_bv_sle_eliminate.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fbv_2dsle_2deliminate
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_bvsle.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a1 _ _ hinv3 h64 h_v2 h_a1 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v0 v3 _ _ hinv4 h64 h_v0 h_v3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo_not.construct s5 e_v5 (by rw [he_v5]; exact empty_args) hinv5 h64 as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_bvslt.construct s6 e_v6 (by rw [he_v6]; exact empty_args) hinv6 h64 as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with Store.apply_rep s7 v6 a1 _ _ hinv7 h64 h_v6 h_a1 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  store_step with Store.apply_rep s8 v7 a0 _ _ hinv8 h64 h_v7 h_a0 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  store_step with Store.apply_rep s9 v5 v8 _ _ hinv9 h64 h_v5 h_v8 (by ns_tac) (by ns_tac) as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
  store_step with Store.apply_rep s10 v4 v9 _ _ hinv10 h64 h_v4 h_v9 (by ns_tac) (by ns_tac) as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  case_done hinv11 hG with h_v10 in EoCases.__eo_prog_bv_sle_eliminate.case_0 using hn_a0 hn_a1

/-- logos's `__eo_prog_bv_sle_eliminate` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fbv_2dsle_2deliminate.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_bv_sle_eliminate x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_bv_sle_eliminate.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_bv_sle_eliminate
  unfold EoCases.__eo_prog_bv_sle_eliminate.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fbv_2dsle_2deliminate_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5fbv_2dsle_2deliminate s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_sle_eliminate x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fbv_2dsle_2deliminate.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5fbv_2dsle_2deliminate
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fbv_2dsle_2deliminate_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_bv_sle_eliminate.case_0

theorem eo__24eo_5fprog_5fbv_2dsle_2deliminate_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fbv_2dsle_2deliminate.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5fbv_2dsle_2deliminate
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fbv_2dsle_2deliminate s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_bv_sle_eliminate x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fbv_2dsle_2deliminate_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fbv_2dsle_2dself_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fbv_2dsle_2dself s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_bv_sle_self.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_bv_sle_self.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fbv_2dsle_2dself
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_bvsle.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a0 _ _ hinv3 h64 h_v2 h_a0 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v0 v3 _ _ hinv4 h64 h_v0 h_v3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3
  store_step with Store.literal_boolean_spec s5 true hinv5 h64 as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4
  store_step with Store.apply_rep s6 v4 v5 _ _ hinv6 h64 h_v4 h_v5 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5
  case_done hinv7 hG with h_v6 in EoCases.__eo_prog_bv_sle_self.case_0 using hn_a0

/-- logos's `__eo_prog_bv_sle_self` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fbv_2dsle_2dself.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_bv_sle_self x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_bv_sle_self.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_bv_sle_self
  unfold EoCases.__eo_prog_bv_sle_self.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fbv_2dsle_2dself_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fbv_2dsle_2dself s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_sle_self x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fbv_2dsle_2dself.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fbv_2dsle_2dself
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fbv_2dsle_2dself_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_bv_sle_self.case_0

theorem eo__24eo_5fprog_5fbv_2dsle_2dself_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fbv_2dsle_2dself.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fbv_2dsle_2dself
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fbv_2dsle_2dself s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_bv_sle_self x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fbv_2dsle_2dself_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fbv_2dsrem_2deliminate_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fbv_2dsrem_2deliminate s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_bv_srem_eliminate.case_0 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_bv_srem_eliminate.case_0 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fbv_2dsrem_2deliminate more_0_eo__24eo_5fprog_5fbv_2dsrem_2deliminate more_1_eo__24eo_5fprog_5fbv_2dsrem_2deliminate more_2_eo__24eo_5fprog_5fbv_2dsrem_2deliminate more_3_eo__24eo_5fprog_5fbv_2dsrem_2deliminate more_4_eo__24eo_5fprog_5fbv_2dsrem_2deliminate more_5_eo__24eo_5fprog_5fbv_2dsrem_2deliminate more_6_eo__24eo_5fprog_5fbv_2dsrem_2deliminate more_7_eo__24eo_5fprog_5fbv_2dsrem_2deliminate
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a3 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_bv_srem_eliminate.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_srem_eliminate.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_srem_eliminate.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_srem_eliminate.case_0
  pat_same v7 a2 with h_v7 h_a2 using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_srem_eliminate.case_0
  pat_unapply h_v4 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_srem_eliminate.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_srem_eliminate.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__2d.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_srem_eliminate.case_0
  pat_unapply h_v14 as ⟨v17, v18, x_v17, x_v18, h_v17, h_v18, hn_v17, hn_v18⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_srem_eliminate.case_0
  step as ⟨e_v19, he_v19⟩
  store_step with CtorSpec.eo__40bvsize.construct s2 e_v19 (by rw [he_v19]; exact empty_args) hinv2 h64 as ⟨v19, s3, hinv3, h_v19⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18
  pat_same v17 v19 with h_v17 h_v19 using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_srem_eliminate.case_0
  pat_same v18 a0 with h_v18 h_a0 using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_srem_eliminate.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s3 1#u32 (1) (by scalar_tac) hinv3 h64 as ⟨v20, s4, hinv4, h_v20⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19
  pat_same v11 v20 with h_v11 h_v20 using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_srem_eliminate.case_0
  step as ⟨e_v21, he_v21⟩
  store_step with CtorSpec.eo__3d.construct s4 e_v21 (by rw [he_v21]; exact empty_args) hinv4 h64 as ⟨v21, s5, hinv5, h_v21⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20
  step as ⟨e_v22, he_v22⟩
  store_step with CtorSpec.eo_bvsrem.construct s5 e_v22 (by rw [he_v22]; exact empty_args) hinv5 h64 as ⟨v22, s6, hinv6, h_v22⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21
  store_step with Store.apply_rep s6 v22 a0 _ _ hinv6 h64 h_v22 h_a0 (by ns_tac) (by ns_tac) as ⟨v23, s7, hinv7, h_v23⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22
  store_step with Store.apply_rep s7 v23 a1 _ _ hinv7 h64 h_v23 h_a1 (by ns_tac) (by ns_tac) as ⟨v24, s8, hinv8, h_v24⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23
  store_step with Store.apply_rep s8 v21 v24 _ _ hinv8 h64 h_v21 h_v24 (by ns_tac) (by ns_tac) as ⟨v25, s9, hinv9, h_v25⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24
  step as ⟨e_v26, he_v26⟩
  store_step with CtorSpec.eo_ite.construct s9 e_v26 (by rw [he_v26]; exact empty_args) hinv9 h64 as ⟨v26, s10, hinv10, h_v26⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25
  step as ⟨e_v27, he_v27⟩
  store_step with CtorSpec.eo__3d.construct s10 e_v27 (by rw [he_v27]; exact empty_args) hinv10 h64 as ⟨v27, s11, hinv11, h_v27⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26
  step as ⟨e_v28, he_v28⟩
  store_step with CtorSpec.eo_extract.construct s11 e_v28 (by rw [he_v28]; rfl) h_a2 h_a2 hinv11 h64 as ⟨v28, s12, hinv12, h_v28⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27
  store_step with Store.apply_rep s12 v28 a0 _ _ hinv12 h64 h_v28 h_a0 (by ns_tac) (by ns_tac) as ⟨v29, s13, hinv13, h_v29⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28
  store_step with Store.apply_rep s13 v27 v29 _ _ hinv13 h64 h_v27 h_v29 (by ns_tac) (by ns_tac) as ⟨v30, s14, hinv14, h_v30⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s14 1#u32 (1) (by scalar_tac) hinv14 h64 as ⟨v31, s15, hinv15, h_v31⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30
  step as ⟨e_v32, he_v32⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s15 e_v32 (by rw [he_v32]; rfl) h_v31 hinv15 h64 as ⟨v32, s16, hinv16, h_v32⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s16 1#u32 (1) (by scalar_tac) hinv16 h64 as ⟨v33, s17, hinv17, h_v33⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32
  store_step with Store.apply_rep s17 v32 v33 _ _ hinv17 h64 h_v32 h_v33 (by ns_tac) (by ns_tac) as ⟨v34, s18, hinv18, h_v34⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33
  store_step with Store.apply_rep s18 v30 v34 _ _ hinv18 h64 h_v30 h_v34 (by ns_tac) (by ns_tac) as ⟨v35, s19, hinv19, h_v35⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34
  store_step with Store.apply_rep s19 v26 v35 _ _ hinv19 h64 h_v26 h_v35 (by ns_tac) (by ns_tac) as ⟨v36, s20, hinv20, h_v36⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35
  step as ⟨e_v37, he_v37⟩
  store_step with CtorSpec.eo_bvneg.construct s20 e_v37 (by rw [he_v37]; exact empty_args) hinv20 h64 as ⟨v37, s21, hinv21, h_v37⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36
  step as ⟨e_v38, he_v38⟩
  store_step with CtorSpec.eo_bvurem.construct s21 e_v38 (by rw [he_v38]; exact empty_args) hinv21 h64 as ⟨v38, s22, hinv22, h_v38⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37
  step as ⟨e_v39, he_v39⟩
  store_step with CtorSpec.eo_ite.construct s22 e_v39 (by rw [he_v39]; exact empty_args) hinv22 h64 as ⟨v39, s23, hinv23, h_v39⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38
  step as ⟨e_v40, he_v40⟩
  store_step with CtorSpec.eo__3d.construct s23 e_v40 (by rw [he_v40]; exact empty_args) hinv23 h64 as ⟨v40, s24, hinv24, h_v40⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39
  step as ⟨e_v41, he_v41⟩
  store_step with CtorSpec.eo_extract.construct s24 e_v41 (by rw [he_v41]; rfl) h_a2 h_a2 hinv24 h64 as ⟨v41, s25, hinv25, h_v41⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40
  store_step with Store.apply_rep s25 v41 a0 _ _ hinv25 h64 h_v41 h_a0 (by ns_tac) (by ns_tac) as ⟨v42, s26, hinv26, h_v42⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41
  store_step with Store.apply_rep s26 v40 v42 _ _ hinv26 h64 h_v40 h_v42 (by ns_tac) (by ns_tac) as ⟨v43, s27, hinv27, h_v43⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s27 1#u32 (1) (by scalar_tac) hinv27 h64 as ⟨v44, s28, hinv28, h_v44⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43
  step as ⟨e_v45, he_v45⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s28 e_v45 (by rw [he_v45]; rfl) h_v44 hinv28 h64 as ⟨v45, s29, hinv29, h_v45⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s29 1#u32 (1) (by scalar_tac) hinv29 h64 as ⟨v46, s30, hinv30, h_v46⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45
  store_step with Store.apply_rep s30 v45 v46 _ _ hinv30 h64 h_v45 h_v46 (by ns_tac) (by ns_tac) as ⟨v47, s31, hinv31, h_v47⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46
  store_step with Store.apply_rep s31 v43 v47 _ _ hinv31 h64 h_v43 h_v47 (by ns_tac) (by ns_tac) as ⟨v48, s32, hinv32, h_v48⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47
  store_step with Store.apply_rep s32 v39 v48 _ _ hinv32 h64 h_v39 h_v48 (by ns_tac) (by ns_tac) as ⟨v49, s33, hinv33, h_v49⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48
  step as ⟨e_v50, he_v50⟩
  store_step with CtorSpec.eo_bvneg.construct s33 e_v50 (by rw [he_v50]; exact empty_args) hinv33 h64 as ⟨v50, s34, hinv34, h_v50⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49
  store_step with Store.apply_rep s34 v50 a0 _ _ hinv34 h64 h_v50 h_a0 (by ns_tac) (by ns_tac) as ⟨v51, s35, hinv35, h_v51⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50
  store_step with Store.apply_rep s35 v49 v51 _ _ hinv35 h64 h_v49 h_v51 (by ns_tac) (by ns_tac) as ⟨v52, s36, hinv36, h_v52⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51
  store_step with Store.apply_rep s36 v52 a0 _ _ hinv36 h64 h_v52 h_a0 (by ns_tac) (by ns_tac) as ⟨v53, s37, hinv37, h_v53⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52
  store_step with Store.apply_rep s37 v38 v53 _ _ hinv37 h64 h_v38 h_v53 (by ns_tac) (by ns_tac) as ⟨v54, s38, hinv38, h_v54⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53
  step as ⟨e_v55, he_v55⟩
  store_step with CtorSpec.eo_ite.construct s38 e_v55 (by rw [he_v55]; exact empty_args) hinv38 h64 as ⟨v55, s39, hinv39, h_v55⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54
  step as ⟨e_v56, he_v56⟩
  store_step with CtorSpec.eo__3d.construct s39 e_v56 (by rw [he_v56]; exact empty_args) hinv39 h64 as ⟨v56, s40, hinv40, h_v56⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55
  step as ⟨e_v57, he_v57⟩
  store_step with CtorSpec.eo_extract.construct s40 e_v57 (by rw [he_v57]; rfl) h_a2 h_a2 hinv40 h64 as ⟨v57, s41, hinv41, h_v57⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56
  store_step with Store.apply_rep s41 v57 a1 _ _ hinv41 h64 h_v57 h_a1 (by ns_tac) (by ns_tac) as ⟨v58, s42, hinv42, h_v58⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57
  store_step with Store.apply_rep s42 v56 v58 _ _ hinv42 h64 h_v56 h_v58 (by ns_tac) (by ns_tac) as ⟨v59, s43, hinv43, h_v59⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s43 1#u32 (1) (by scalar_tac) hinv43 h64 as ⟨v60, s44, hinv44, h_v60⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59
  step as ⟨e_v61, he_v61⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s44 e_v61 (by rw [he_v61]; rfl) h_v60 hinv44 h64 as ⟨v61, s45, hinv45, h_v61⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s45 1#u32 (1) (by scalar_tac) hinv45 h64 as ⟨v62, s46, hinv46, h_v62⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61
  store_step with Store.apply_rep s46 v61 v62 _ _ hinv46 h64 h_v61 h_v62 (by ns_tac) (by ns_tac) as ⟨v63, s47, hinv47, h_v63⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62
  store_step with Store.apply_rep s47 v59 v63 _ _ hinv47 h64 h_v59 h_v63 (by ns_tac) (by ns_tac) as ⟨v64, s48, hinv48, h_v64⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63
  store_step with Store.apply_rep s48 v55 v64 _ _ hinv48 h64 h_v55 h_v64 (by ns_tac) (by ns_tac) as ⟨v65, s49, hinv49, h_v65⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64
  step as ⟨e_v66, he_v66⟩
  store_step with CtorSpec.eo_bvneg.construct s49 e_v66 (by rw [he_v66]; exact empty_args) hinv49 h64 as ⟨v66, s50, hinv50, h_v66⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65
  store_step with Store.apply_rep s50 v66 a1 _ _ hinv50 h64 h_v66 h_a1 (by ns_tac) (by ns_tac) as ⟨v67, s51, hinv51, h_v67⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66
  store_step with Store.apply_rep s51 v65 v67 _ _ hinv51 h64 h_v65 h_v67 (by ns_tac) (by ns_tac) as ⟨v68, s52, hinv52, h_v68⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67
  store_step with Store.apply_rep s52 v68 a1 _ _ hinv52 h64 h_v68 h_a1 (by ns_tac) (by ns_tac) as ⟨v69, s53, hinv53, h_v69⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68
  store_step with Store.apply_rep s53 v54 v69 _ _ hinv53 h64 h_v54 h_v69 (by ns_tac) (by ns_tac) as ⟨v70, s54, hinv54, h_v70⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69
  store_step with Store.apply_rep s54 v37 v70 _ _ hinv54 h64 h_v37 h_v70 (by ns_tac) (by ns_tac) as ⟨v71, s55, hinv55, h_v71⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70
  store_step with Store.apply_rep s55 v36 v71 _ _ hinv55 h64 h_v36 h_v71 (by ns_tac) (by ns_tac) as ⟨v72, s56, hinv56, h_v72⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70 h_v71
  step as ⟨e_v73, he_v73⟩
  store_step with CtorSpec.eo_bvurem.construct s56 e_v73 (by rw [he_v73]; exact empty_args) hinv56 h64 as ⟨v73, s57, hinv57, h_v73⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70 h_v71 h_v72
  step as ⟨e_v74, he_v74⟩
  store_step with CtorSpec.eo_ite.construct s57 e_v74 (by rw [he_v74]; exact empty_args) hinv57 h64 as ⟨v74, s58, hinv58, h_v74⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70 h_v71 h_v72 h_v73
  step as ⟨e_v75, he_v75⟩
  store_step with CtorSpec.eo__3d.construct s58 e_v75 (by rw [he_v75]; exact empty_args) hinv58 h64 as ⟨v75, s59, hinv59, h_v75⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70 h_v71 h_v72 h_v73 h_v74
  step as ⟨e_v76, he_v76⟩
  store_step with CtorSpec.eo_extract.construct s59 e_v76 (by rw [he_v76]; rfl) h_a2 h_a2 hinv59 h64 as ⟨v76, s60, hinv60, h_v76⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70 h_v71 h_v72 h_v73 h_v74 h_v75
  store_step with Store.apply_rep s60 v76 a0 _ _ hinv60 h64 h_v76 h_a0 (by ns_tac) (by ns_tac) as ⟨v77, s61, hinv61, h_v77⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70 h_v71 h_v72 h_v73 h_v74 h_v75 h_v76
  store_step with Store.apply_rep s61 v75 v77 _ _ hinv61 h64 h_v75 h_v77 (by ns_tac) (by ns_tac) as ⟨v78, s62, hinv62, h_v78⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70 h_v71 h_v72 h_v73 h_v74 h_v75 h_v76 h_v77
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s62 1#u32 (1) (by scalar_tac) hinv62 h64 as ⟨v79, s63, hinv63, h_v79⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70 h_v71 h_v72 h_v73 h_v74 h_v75 h_v76 h_v77 h_v78
  step as ⟨e_v80, he_v80⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s63 e_v80 (by rw [he_v80]; rfl) h_v79 hinv63 h64 as ⟨v80, s64, hinv64, h_v80⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70 h_v71 h_v72 h_v73 h_v74 h_v75 h_v76 h_v77 h_v78 h_v79
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s64 1#u32 (1) (by scalar_tac) hinv64 h64 as ⟨v81, s65, hinv65, h_v81⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70 h_v71 h_v72 h_v73 h_v74 h_v75 h_v76 h_v77 h_v78 h_v79 h_v80
  store_step with Store.apply_rep s65 v80 v81 _ _ hinv65 h64 h_v80 h_v81 (by ns_tac) (by ns_tac) as ⟨v82, s66, hinv66, h_v82⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70 h_v71 h_v72 h_v73 h_v74 h_v75 h_v76 h_v77 h_v78 h_v79 h_v80 h_v81
  store_step with Store.apply_rep s66 v78 v82 _ _ hinv66 h64 h_v78 h_v82 (by ns_tac) (by ns_tac) as ⟨v83, s67, hinv67, h_v83⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70 h_v71 h_v72 h_v73 h_v74 h_v75 h_v76 h_v77 h_v78 h_v79 h_v80 h_v81 h_v82
  store_step with Store.apply_rep s67 v74 v83 _ _ hinv67 h64 h_v74 h_v83 (by ns_tac) (by ns_tac) as ⟨v84, s68, hinv68, h_v84⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70 h_v71 h_v72 h_v73 h_v74 h_v75 h_v76 h_v77 h_v78 h_v79 h_v80 h_v81 h_v82 h_v83
  step as ⟨e_v85, he_v85⟩
  store_step with CtorSpec.eo_bvneg.construct s68 e_v85 (by rw [he_v85]; exact empty_args) hinv68 h64 as ⟨v85, s69, hinv69, h_v85⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70 h_v71 h_v72 h_v73 h_v74 h_v75 h_v76 h_v77 h_v78 h_v79 h_v80 h_v81 h_v82 h_v83 h_v84
  store_step with Store.apply_rep s69 v85 a0 _ _ hinv69 h64 h_v85 h_a0 (by ns_tac) (by ns_tac) as ⟨v86, s70, hinv70, h_v86⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70 h_v71 h_v72 h_v73 h_v74 h_v75 h_v76 h_v77 h_v78 h_v79 h_v80 h_v81 h_v82 h_v83 h_v84 h_v85
  store_step with Store.apply_rep s70 v84 v86 _ _ hinv70 h64 h_v84 h_v86 (by ns_tac) (by ns_tac) as ⟨v87, s71, hinv71, h_v87⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70 h_v71 h_v72 h_v73 h_v74 h_v75 h_v76 h_v77 h_v78 h_v79 h_v80 h_v81 h_v82 h_v83 h_v84 h_v85 h_v86
  store_step with Store.apply_rep s71 v87 a0 _ _ hinv71 h64 h_v87 h_a0 (by ns_tac) (by ns_tac) as ⟨v88, s72, hinv72, h_v88⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70 h_v71 h_v72 h_v73 h_v74 h_v75 h_v76 h_v77 h_v78 h_v79 h_v80 h_v81 h_v82 h_v83 h_v84 h_v85 h_v86 h_v87
  store_step with Store.apply_rep s72 v73 v88 _ _ hinv72 h64 h_v73 h_v88 (by ns_tac) (by ns_tac) as ⟨v89, s73, hinv73, h_v89⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70 h_v71 h_v72 h_v73 h_v74 h_v75 h_v76 h_v77 h_v78 h_v79 h_v80 h_v81 h_v82 h_v83 h_v84 h_v85 h_v86 h_v87 h_v88
  step as ⟨e_v90, he_v90⟩
  store_step with CtorSpec.eo_ite.construct s73 e_v90 (by rw [he_v90]; exact empty_args) hinv73 h64 as ⟨v90, s74, hinv74, h_v90⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70 h_v71 h_v72 h_v73 h_v74 h_v75 h_v76 h_v77 h_v78 h_v79 h_v80 h_v81 h_v82 h_v83 h_v84 h_v85 h_v86 h_v87 h_v88 h_v89
  step as ⟨e_v91, he_v91⟩
  store_step with CtorSpec.eo__3d.construct s74 e_v91 (by rw [he_v91]; exact empty_args) hinv74 h64 as ⟨v91, s75, hinv75, h_v91⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70 h_v71 h_v72 h_v73 h_v74 h_v75 h_v76 h_v77 h_v78 h_v79 h_v80 h_v81 h_v82 h_v83 h_v84 h_v85 h_v86 h_v87 h_v88 h_v89 h_v90
  step as ⟨e_v92, he_v92⟩
  store_step with CtorSpec.eo_extract.construct s75 e_v92 (by rw [he_v92]; rfl) h_a2 h_a2 hinv75 h64 as ⟨v92, s76, hinv76, h_v92⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70 h_v71 h_v72 h_v73 h_v74 h_v75 h_v76 h_v77 h_v78 h_v79 h_v80 h_v81 h_v82 h_v83 h_v84 h_v85 h_v86 h_v87 h_v88 h_v89 h_v90 h_v91
  store_step with Store.apply_rep s76 v92 a1 _ _ hinv76 h64 h_v92 h_a1 (by ns_tac) (by ns_tac) as ⟨v93, s77, hinv77, h_v93⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70 h_v71 h_v72 h_v73 h_v74 h_v75 h_v76 h_v77 h_v78 h_v79 h_v80 h_v81 h_v82 h_v83 h_v84 h_v85 h_v86 h_v87 h_v88 h_v89 h_v90 h_v91 h_v92
  store_step with Store.apply_rep s77 v91 v93 _ _ hinv77 h64 h_v91 h_v93 (by ns_tac) (by ns_tac) as ⟨v94, s78, hinv78, h_v94⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70 h_v71 h_v72 h_v73 h_v74 h_v75 h_v76 h_v77 h_v78 h_v79 h_v80 h_v81 h_v82 h_v83 h_v84 h_v85 h_v86 h_v87 h_v88 h_v89 h_v90 h_v91 h_v92 h_v93
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s78 1#u32 (1) (by scalar_tac) hinv78 h64 as ⟨v95, s79, hinv79, h_v95⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70 h_v71 h_v72 h_v73 h_v74 h_v75 h_v76 h_v77 h_v78 h_v79 h_v80 h_v81 h_v82 h_v83 h_v84 h_v85 h_v86 h_v87 h_v88 h_v89 h_v90 h_v91 h_v92 h_v93 h_v94
  step as ⟨e_v96, he_v96⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s79 e_v96 (by rw [he_v96]; rfl) h_v95 hinv79 h64 as ⟨v96, s80, hinv80, h_v96⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70 h_v71 h_v72 h_v73 h_v74 h_v75 h_v76 h_v77 h_v78 h_v79 h_v80 h_v81 h_v82 h_v83 h_v84 h_v85 h_v86 h_v87 h_v88 h_v89 h_v90 h_v91 h_v92 h_v93 h_v94 h_v95
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s80 1#u32 (1) (by scalar_tac) hinv80 h64 as ⟨v97, s81, hinv81, h_v97⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70 h_v71 h_v72 h_v73 h_v74 h_v75 h_v76 h_v77 h_v78 h_v79 h_v80 h_v81 h_v82 h_v83 h_v84 h_v85 h_v86 h_v87 h_v88 h_v89 h_v90 h_v91 h_v92 h_v93 h_v94 h_v95 h_v96
  store_step with Store.apply_rep s81 v96 v97 _ _ hinv81 h64 h_v96 h_v97 (by ns_tac) (by ns_tac) as ⟨v98, s82, hinv82, h_v98⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70 h_v71 h_v72 h_v73 h_v74 h_v75 h_v76 h_v77 h_v78 h_v79 h_v80 h_v81 h_v82 h_v83 h_v84 h_v85 h_v86 h_v87 h_v88 h_v89 h_v90 h_v91 h_v92 h_v93 h_v94 h_v95 h_v96 h_v97
  store_step with Store.apply_rep s82 v94 v98 _ _ hinv82 h64 h_v94 h_v98 (by ns_tac) (by ns_tac) as ⟨v99, s83, hinv83, h_v99⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70 h_v71 h_v72 h_v73 h_v74 h_v75 h_v76 h_v77 h_v78 h_v79 h_v80 h_v81 h_v82 h_v83 h_v84 h_v85 h_v86 h_v87 h_v88 h_v89 h_v90 h_v91 h_v92 h_v93 h_v94 h_v95 h_v96 h_v97 h_v98
  store_step with Store.apply_rep s83 v90 v99 _ _ hinv83 h64 h_v90 h_v99 (by ns_tac) (by ns_tac) as ⟨v100, s84, hinv84, h_v100⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70 h_v71 h_v72 h_v73 h_v74 h_v75 h_v76 h_v77 h_v78 h_v79 h_v80 h_v81 h_v82 h_v83 h_v84 h_v85 h_v86 h_v87 h_v88 h_v89 h_v90 h_v91 h_v92 h_v93 h_v94 h_v95 h_v96 h_v97 h_v98 h_v99
  step as ⟨e_v101, he_v101⟩
  store_step with CtorSpec.eo_bvneg.construct s84 e_v101 (by rw [he_v101]; exact empty_args) hinv84 h64 as ⟨v101, s85, hinv85, h_v101⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70 h_v71 h_v72 h_v73 h_v74 h_v75 h_v76 h_v77 h_v78 h_v79 h_v80 h_v81 h_v82 h_v83 h_v84 h_v85 h_v86 h_v87 h_v88 h_v89 h_v90 h_v91 h_v92 h_v93 h_v94 h_v95 h_v96 h_v97 h_v98 h_v99 h_v100
  store_step with Store.apply_rep s85 v101 a1 _ _ hinv85 h64 h_v101 h_a1 (by ns_tac) (by ns_tac) as ⟨v102, s86, hinv86, h_v102⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70 h_v71 h_v72 h_v73 h_v74 h_v75 h_v76 h_v77 h_v78 h_v79 h_v80 h_v81 h_v82 h_v83 h_v84 h_v85 h_v86 h_v87 h_v88 h_v89 h_v90 h_v91 h_v92 h_v93 h_v94 h_v95 h_v96 h_v97 h_v98 h_v99 h_v100 h_v101
  store_step with Store.apply_rep s86 v100 v102 _ _ hinv86 h64 h_v100 h_v102 (by ns_tac) (by ns_tac) as ⟨v103, s87, hinv87, h_v103⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70 h_v71 h_v72 h_v73 h_v74 h_v75 h_v76 h_v77 h_v78 h_v79 h_v80 h_v81 h_v82 h_v83 h_v84 h_v85 h_v86 h_v87 h_v88 h_v89 h_v90 h_v91 h_v92 h_v93 h_v94 h_v95 h_v96 h_v97 h_v98 h_v99 h_v100 h_v101 h_v102
  store_step with Store.apply_rep s87 v103 a1 _ _ hinv87 h64 h_v103 h_a1 (by ns_tac) (by ns_tac) as ⟨v104, s88, hinv88, h_v104⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70 h_v71 h_v72 h_v73 h_v74 h_v75 h_v76 h_v77 h_v78 h_v79 h_v80 h_v81 h_v82 h_v83 h_v84 h_v85 h_v86 h_v87 h_v88 h_v89 h_v90 h_v91 h_v92 h_v93 h_v94 h_v95 h_v96 h_v97 h_v98 h_v99 h_v100 h_v101 h_v102 h_v103
  store_step with Store.apply_rep s88 v89 v104 _ _ hinv88 h64 h_v89 h_v104 (by ns_tac) (by ns_tac) as ⟨v105, s89, hinv89, h_v105⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70 h_v71 h_v72 h_v73 h_v74 h_v75 h_v76 h_v77 h_v78 h_v79 h_v80 h_v81 h_v82 h_v83 h_v84 h_v85 h_v86 h_v87 h_v88 h_v89 h_v90 h_v91 h_v92 h_v93 h_v94 h_v95 h_v96 h_v97 h_v98 h_v99 h_v100 h_v101 h_v102 h_v103 h_v104
  store_step with Store.apply_rep s89 v72 v105 _ _ hinv89 h64 h_v72 h_v105 (by ns_tac) (by ns_tac) as ⟨v106, s90, hinv90, h_v106⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70 h_v71 h_v72 h_v73 h_v74 h_v75 h_v76 h_v77 h_v78 h_v79 h_v80 h_v81 h_v82 h_v83 h_v84 h_v85 h_v86 h_v87 h_v88 h_v89 h_v90 h_v91 h_v92 h_v93 h_v94 h_v95 h_v96 h_v97 h_v98 h_v99 h_v100 h_v101 h_v102 h_v103 h_v104 h_v105
  store_step with Store.apply_rep s90 v25 v106 _ _ hinv90 h64 h_v25 h_v106 (by ns_tac) (by ns_tac) as ⟨v107, s91, hinv91, h_v107⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70 h_v71 h_v72 h_v73 h_v74 h_v75 h_v76 h_v77 h_v78 h_v79 h_v80 h_v81 h_v82 h_v83 h_v84 h_v85 h_v86 h_v87 h_v88 h_v89 h_v90 h_v91 h_v92 h_v93 h_v94 h_v95 h_v96 h_v97 h_v98 h_v99 h_v100 h_v101 h_v102 h_v103 h_v104 h_v105 h_v106
  case_done hinv91 hG with h_v107 in EoCases.__eo_prog_bv_srem_eliminate.case_0 using hn_a0 hn_a1 hn_a2 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v13 hn_v14 hn_v17 hn_v18

/-- logos's `__eo_prog_bv_srem_eliminate` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fbv_2dsrem_2deliminate.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) :
    __eo_prog_bv_srem_eliminate x_a0 x_a1 x_a2 x_a3 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_bv_srem_eliminate.case_0 x_a0 x_a1 x_a2 x_a3] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_bv_srem_eliminate
  unfold EoCases.__eo_prog_bv_srem_eliminate.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fbv_2dsrem_2deliminate_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) :
    body_eo__24eo_5fprog_5fbv_2dsrem_2deliminate s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_srem_eliminate x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fbv_2dsrem_2deliminate.rust_eq x_a0 x_a1 x_a2 x_a3 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3)]
  unfold body_eo__24eo_5fprog_5fbv_2dsrem_2deliminate
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fbv_2dsrem_2deliminate_spec n ih s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 using hn_a0 hn_a1 hn_a2
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hc0 in EoCases.__eo_prog_bv_srem_eliminate.case_0

theorem eo__24eo_5fprog_5fbv_2dsrem_2deliminate_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fbv_2dsrem_2deliminate.Spec n := by
  intro s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3
  unfold eo__24eo_5fprog_5fbv_2dsrem_2deliminate
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fbv_2dsrem_2deliminate s1 a0 a1 a2 a3) (fun s' t => Represents.rep s' t (__eo_prog_bv_srem_eliminate x_a0 x_a1 x_a2 x_a3))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fbv_2dsrem_2deliminate_spec m (ih m hm) s1 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fbv_2dudiv_2done_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fbv_2dudiv_2done s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_bv_udiv_one.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_bv_udiv_one.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fbv_2dudiv_2done
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_bvudiv.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s3 e_v3 (by rw [he_v3]; rfl) h_a1 hinv3 h64 as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s4 1#u32 (1) (by scalar_tac) hinv4 h64 as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3
  store_step with Store.apply_rep s5 v3 v4 _ _ hinv5 h64 h_v3 h_v4 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4
  store_step with Store.apply_rep s6 v2 v5 _ _ hinv6 h64 h_v2 h_v5 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with Store.apply_rep s7 v0 v6 _ _ hinv7 h64 h_v0 h_v6 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  store_step with Store.apply_rep s8 v7 a0 _ _ hinv8 h64 h_v7 h_a0 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  case_done hinv9 hG with h_v8 in EoCases.__eo_prog_bv_udiv_one.case_0 using hn_a0 hn_a1

/-- logos's `__eo_prog_bv_udiv_one` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fbv_2dudiv_2done.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_bv_udiv_one x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_bv_udiv_one.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_bv_udiv_one
  unfold EoCases.__eo_prog_bv_udiv_one.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fbv_2dudiv_2done_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5fbv_2dudiv_2done s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_udiv_one x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fbv_2dudiv_2done.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5fbv_2dudiv_2done
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fbv_2dudiv_2done_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_bv_udiv_one.case_0

theorem eo__24eo_5fprog_5fbv_2dudiv_2done_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fbv_2dudiv_2done.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5fbv_2dudiv_2done
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fbv_2dudiv_2done s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_bv_udiv_one x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fbv_2dudiv_2done_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fbv_2dudiv_2dpow2_2dnot_2done_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 a6 a7 a8 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _) (x_a7 : _) (x_a8 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) (h_a6 : Represents.rep s a6 x_a6) (h_a7 : Represents.rep s a7 x_a7) (h_a8 : Represents.rep s a8 x_a8) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) (hn_a4 : x_a4 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fbv_2dudiv_2dpow2_2dnot_2done s a0 a1 a2 a3 a4 a5 a6 a7 a8 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_bv_udiv_pow2_not_one.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_bv_udiv_pow2_not_one.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fbv_2dudiv_2dpow2_2dnot_2done more_0_eo__24eo_5fprog_5fbv_2dudiv_2dpow2_2dnot_2done more_1_eo__24eo_5fprog_5fbv_2dudiv_2dpow2_2dnot_2done more_2_eo__24eo_5fprog_5fbv_2dudiv_2dpow2_2dnot_2done more_3_eo__24eo_5fprog_5fbv_2dudiv_2dpow2_2dnot_2done more_4_eo__24eo_5fprog_5fbv_2dudiv_2dpow2_2dnot_2done
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a5 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_bv_udiv_pow2_not_one.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_udiv_pow2_not_one.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_udiv_pow2_not_one.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 h_v1 h_v3 h_v4 h_v6 h_v7
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_udiv_pow2_not_one.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_udiv_pow2_not_one.case_0
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo_int_2eispow2.construct s1 e_v12 (by rw [he_v12]; exact empty_args) hinv1 h64 as ⟨v12, s2, hinv2, h_v12⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11
  pat_same v10 v12 with h_v10 h_v12 using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_udiv_pow2_not_one.case_0
  pat_same v11 a1 with h_v11 h_a1 using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_udiv_pow2_not_one.case_0
  store_step with Store.literal_boolean_spec s2 true hinv2 h64 as ⟨v13, s3, hinv3, h_v13⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12
  pat_same v4 v13 with h_v4 h_v13 using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_udiv_pow2_not_one.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a6 as ⟨v15, x_v15, h_v15⟩ else hinv3 hG in EoCases.__eo_prog_bv_udiv_pow2_not_one.case_0
  pat_unapply h_v15 as ⟨v17, v18, x_v17, x_v18, h_v17, h_v18, hn_v17, hn_v18⟩ using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_udiv_pow2_not_one.case_0
  pat_unapply h_v17 as ⟨v20, v21, x_v20, x_v21, h_v20, h_v21, hn_v20, hn_v21⟩ using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_udiv_pow2_not_one.case_0
  step as ⟨e_v22, he_v22⟩
  store_step with CtorSpec.eo__3d.construct s3 e_v22 (by rw [he_v22]; exact empty_args) hinv3 h64 as ⟨v22, s4, hinv4, h_v22⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v15 h_v17 h_v18 h_v20 h_v21
  pat_same v20 v22 with h_v20 h_v22 using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_udiv_pow2_not_one.case_0
  pat_unapply h_v21 as ⟨v24, v25, x_v24, x_v25, h_v24, h_v25, hn_v24, hn_v25⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_udiv_pow2_not_one.case_0
  pat_unapply h_v24 as ⟨v27, v28, x_v27, x_v28, h_v27, h_v28, hn_v27, hn_v28⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_udiv_pow2_not_one.case_0
  step as ⟨e_v29, he_v29⟩
  store_step with CtorSpec.eo__3e.construct s4 e_v29 (by rw [he_v29]; exact empty_args) hinv4 h64 as ⟨v29, s5, hinv5, h_v29⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v27 h_v28
  pat_same v27 v29 with h_v27 h_v29 using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_udiv_pow2_not_one.case_0
  pat_same v28 a1 with h_v28 h_a1 using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_udiv_pow2_not_one.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s5 1#u32 (1) (by scalar_tac) hinv5 h64 as ⟨v30, s6, hinv6, h_v30⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29
  pat_same v25 v30 with h_v25 h_v30 using hinv6 else hinv6 hG in EoCases.__eo_prog_bv_udiv_pow2_not_one.case_0
  store_step with Store.literal_boolean_spec s6 true hinv6 h64 as ⟨v31, s7, hinv7, h_v31⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v30
  pat_same v18 v31 with h_v18 h_v31 using hinv7 else hinv7 hG in EoCases.__eo_prog_bv_udiv_pow2_not_one.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a7 as ⟨v33, x_v33, h_v33⟩ else hinv7 hG in EoCases.__eo_prog_bv_udiv_pow2_not_one.case_0
  pat_unapply h_v33 as ⟨v35, v36, x_v35, x_v36, h_v35, h_v36, hn_v35, hn_v36⟩ using hinv7 else hinv7 hG in EoCases.__eo_prog_bv_udiv_pow2_not_one.case_0
  pat_unapply h_v35 as ⟨v38, v39, x_v38, x_v39, h_v38, h_v39, hn_v38, hn_v39⟩ using hinv7 else hinv7 hG in EoCases.__eo_prog_bv_udiv_pow2_not_one.case_0
  step as ⟨e_v40, he_v40⟩
  store_step with CtorSpec.eo__3d.construct s7 e_v40 (by rw [he_v40]; exact empty_args) hinv7 h64 as ⟨v40, s8, hinv8, h_v40⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v30 h_v31 h_v33 h_v35 h_v36 h_v38 h_v39
  pat_same v38 v40 with h_v38 h_v40 using hinv8 else hinv8 hG in EoCases.__eo_prog_bv_udiv_pow2_not_one.case_0
  pat_same v39 a3 with h_v39 h_a3 using hinv8 else hinv8 hG in EoCases.__eo_prog_bv_udiv_pow2_not_one.case_0
  pat_unapply h_v36 as ⟨v42, v43, x_v42, x_v43, h_v42, h_v43, hn_v42, hn_v43⟩ using hinv8 else hinv8 hG in EoCases.__eo_prog_bv_udiv_pow2_not_one.case_0
  step as ⟨e_v44, he_v44⟩
  store_step with CtorSpec.eo_int_2elog2.construct s8 e_v44 (by rw [he_v44]; exact empty_args) hinv8 h64 as ⟨v44, s9, hinv9, h_v44⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v30 h_v31 h_v33 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43
  pat_same v42 v44 with h_v42 h_v44 using hinv9 else hinv9 hG in EoCases.__eo_prog_bv_udiv_pow2_not_one.case_0
  pat_same v43 a1 with h_v43 h_a1 using hinv9 else hinv9 hG in EoCases.__eo_prog_bv_udiv_pow2_not_one.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a8 as ⟨v46, x_v46, h_v46⟩ else hinv9 hG in EoCases.__eo_prog_bv_udiv_pow2_not_one.case_0
  pat_unapply h_v46 as ⟨v48, v49, x_v48, x_v49, h_v48, h_v49, hn_v48, hn_v49⟩ using hinv9 else hinv9 hG in EoCases.__eo_prog_bv_udiv_pow2_not_one.case_0
  pat_unapply h_v48 as ⟨v51, v52, x_v51, x_v52, h_v51, h_v52, hn_v51, hn_v52⟩ using hinv9 else hinv9 hG in EoCases.__eo_prog_bv_udiv_pow2_not_one.case_0
  step as ⟨e_v53, he_v53⟩
  store_step with CtorSpec.eo__3d.construct s9 e_v53 (by rw [he_v53]; exact empty_args) hinv9 h64 as ⟨v53, s10, hinv10, h_v53⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v30 h_v31 h_v33 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v44 h_v46 h_v48 h_v49 h_v51 h_v52
  pat_same v51 v53 with h_v51 h_v53 using hinv10 else hinv10 hG in EoCases.__eo_prog_bv_udiv_pow2_not_one.case_0
  pat_same v52 a4 with h_v52 h_a4 using hinv10 else hinv10 hG in EoCases.__eo_prog_bv_udiv_pow2_not_one.case_0
  pat_unapply h_v49 as ⟨v55, v56, x_v55, x_v56, h_v55, h_v56, hn_v55, hn_v56⟩ using hinv10 else hinv10 hG in EoCases.__eo_prog_bv_udiv_pow2_not_one.case_0
  pat_unapply h_v55 as ⟨v58, v59, x_v58, x_v59, h_v58, h_v59, hn_v58, hn_v59⟩ using hinv10 else hinv10 hG in EoCases.__eo_prog_bv_udiv_pow2_not_one.case_0
  step as ⟨e_v60, he_v60⟩
  store_step with CtorSpec.eo__2d.construct s10 e_v60 (by rw [he_v60]; exact empty_args) hinv10 h64 as ⟨v60, s11, hinv11, h_v60⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v30 h_v31 h_v33 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v44 h_v46 h_v48 h_v49 h_v51 h_v52 h_v53 h_v55 h_v56 h_v58 h_v59
  pat_same v58 v60 with h_v58 h_v60 using hinv11 else hinv11 hG in EoCases.__eo_prog_bv_udiv_pow2_not_one.case_0
  pat_same v59 a2 with h_v59 h_a2 using hinv11 else hinv11 hG in EoCases.__eo_prog_bv_udiv_pow2_not_one.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s11 1#u32 (1) (by scalar_tac) hinv11 h64 as ⟨v61, s12, hinv12, h_v61⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v30 h_v31 h_v33 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v44 h_v46 h_v48 h_v49 h_v51 h_v52 h_v53 h_v55 h_v56 h_v58 h_v59 h_v60
  pat_same v56 v61 with h_v56 h_v61 using hinv12 else hinv12 hG in EoCases.__eo_prog_bv_udiv_pow2_not_one.case_0
  step as ⟨e_v62, he_v62⟩
  store_step with CtorSpec.eo__3d.construct s12 e_v62 (by rw [he_v62]; exact empty_args) hinv12 h64 as ⟨v62, s13, hinv13, h_v62⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v30 h_v31 h_v33 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v44 h_v46 h_v48 h_v49 h_v51 h_v52 h_v53 h_v55 h_v56 h_v58 h_v59 h_v60 h_v61
  step as ⟨e_v63, he_v63⟩
  store_step with CtorSpec.eo_bvudiv.construct s13 e_v63 (by rw [he_v63]; exact empty_args) hinv13 h64 as ⟨v63, s14, hinv14, h_v63⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v30 h_v31 h_v33 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v44 h_v46 h_v48 h_v49 h_v51 h_v52 h_v53 h_v55 h_v56 h_v58 h_v59 h_v60 h_v61 h_v62
  store_step with Store.apply_rep s14 v63 a0 _ _ hinv14 h64 h_v63 h_a0 (by ns_tac) (by ns_tac) as ⟨v64, s15, hinv15, h_v64⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v30 h_v31 h_v33 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v44 h_v46 h_v48 h_v49 h_v51 h_v52 h_v53 h_v55 h_v56 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63
  step as ⟨e_v65, he_v65⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s15 e_v65 (by rw [he_v65]; rfl) h_a2 hinv15 h64 as ⟨v65, s16, hinv16, h_v65⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v30 h_v31 h_v33 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v44 h_v46 h_v48 h_v49 h_v51 h_v52 h_v53 h_v55 h_v56 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64
  store_step with Store.apply_rep s16 v65 a1 _ _ hinv16 h64 h_v65 h_a1 (by ns_tac) (by ns_tac) as ⟨v66, s17, hinv17, h_v66⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v30 h_v31 h_v33 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v44 h_v46 h_v48 h_v49 h_v51 h_v52 h_v53 h_v55 h_v56 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65
  store_step with Store.apply_rep s17 v64 v66 _ _ hinv17 h64 h_v64 h_v66 (by ns_tac) (by ns_tac) as ⟨v67, s18, hinv18, h_v67⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v30 h_v31 h_v33 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v44 h_v46 h_v48 h_v49 h_v51 h_v52 h_v53 h_v55 h_v56 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66
  store_step with Store.apply_rep s18 v62 v67 _ _ hinv18 h64 h_v62 h_v67 (by ns_tac) (by ns_tac) as ⟨v68, s19, hinv19, h_v68⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v30 h_v31 h_v33 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v44 h_v46 h_v48 h_v49 h_v51 h_v52 h_v53 h_v55 h_v56 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67
  step as ⟨e_v69, he_v69⟩
  store_step with CtorSpec.eo_concat.construct s19 e_v69 (by rw [he_v69]; exact empty_args) hinv19 h64 as ⟨v69, s20, hinv20, h_v69⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v30 h_v31 h_v33 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v44 h_v46 h_v48 h_v49 h_v51 h_v52 h_v53 h_v55 h_v56 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68
  step as ⟨e_v70, he_v70⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s20 e_v70 (by rw [he_v70]; rfl) h_a3 hinv20 h64 as ⟨v70, s21, hinv21, h_v70⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v30 h_v31 h_v33 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v44 h_v46 h_v48 h_v49 h_v51 h_v52 h_v53 h_v55 h_v56 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s21 0#u32 (0) (by scalar_tac) hinv21 h64 as ⟨v71, s22, hinv22, h_v71⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v30 h_v31 h_v33 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v44 h_v46 h_v48 h_v49 h_v51 h_v52 h_v53 h_v55 h_v56 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70
  store_step with Store.apply_rep s22 v70 v71 _ _ hinv22 h64 h_v70 h_v71 (by ns_tac) (by ns_tac) as ⟨v72, s23, hinv23, h_v72⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v30 h_v31 h_v33 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v44 h_v46 h_v48 h_v49 h_v51 h_v52 h_v53 h_v55 h_v56 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70 h_v71
  store_step with Store.apply_rep s23 v69 v72 _ _ hinv23 h64 h_v69 h_v72 (by ns_tac) (by ns_tac) as ⟨v73, s24, hinv24, h_v73⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v30 h_v31 h_v33 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v44 h_v46 h_v48 h_v49 h_v51 h_v52 h_v53 h_v55 h_v56 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70 h_v71 h_v72
  step as ⟨e_v74, he_v74⟩
  store_step with CtorSpec.eo_concat.construct s24 e_v74 (by rw [he_v74]; exact empty_args) hinv24 h64 as ⟨v74, s25, hinv25, h_v74⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v30 h_v31 h_v33 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v44 h_v46 h_v48 h_v49 h_v51 h_v52 h_v53 h_v55 h_v56 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70 h_v71 h_v72 h_v73
  step as ⟨e_v75, he_v75⟩
  store_step with CtorSpec.eo_extract.construct s25 e_v75 (by rw [he_v75]; rfl) h_a4 h_a3 hinv25 h64 as ⟨v75, s26, hinv26, h_v75⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v30 h_v31 h_v33 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v44 h_v46 h_v48 h_v49 h_v51 h_v52 h_v53 h_v55 h_v56 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70 h_v71 h_v72 h_v73 h_v74
  store_step with Store.apply_rep s26 v75 a0 _ _ hinv26 h64 h_v75 h_a0 (by ns_tac) (by ns_tac) as ⟨v76, s27, hinv27, h_v76⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v30 h_v31 h_v33 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v44 h_v46 h_v48 h_v49 h_v51 h_v52 h_v53 h_v55 h_v56 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70 h_v71 h_v72 h_v73 h_v74 h_v75
  store_step with Store.apply_rep s27 v74 v76 _ _ hinv27 h64 h_v74 h_v76 (by ns_tac) (by ns_tac) as ⟨v77, s28, hinv28, h_v77⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v30 h_v31 h_v33 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v44 h_v46 h_v48 h_v49 h_v51 h_v52 h_v53 h_v55 h_v56 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70 h_v71 h_v72 h_v73 h_v74 h_v75 h_v76
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s28 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv28 h64 as ⟨v78, s29, hinv29, h_v78⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v30 h_v31 h_v33 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v44 h_v46 h_v48 h_v49 h_v51 h_v52 h_v53 h_v55 h_v56 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70 h_v71 h_v72 h_v73 h_v74 h_v75 h_v76 h_v77
  store_step with Store.apply_rep s29 v77 v78 _ _ hinv29 h64 h_v77 h_v78 (by ns_tac) (by ns_tac) as ⟨v79, s30, hinv30, h_v79⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v30 h_v31 h_v33 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v44 h_v46 h_v48 h_v49 h_v51 h_v52 h_v53 h_v55 h_v56 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70 h_v71 h_v72 h_v73 h_v74 h_v75 h_v76 h_v77 h_v78
  store_step with Store.apply_rep s30 v73 v79 _ _ hinv30 h64 h_v73 h_v79 (by ns_tac) (by ns_tac) as ⟨v80, s31, hinv31, h_v80⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v30 h_v31 h_v33 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v44 h_v46 h_v48 h_v49 h_v51 h_v52 h_v53 h_v55 h_v56 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70 h_v71 h_v72 h_v73 h_v74 h_v75 h_v76 h_v77 h_v78 h_v79
  store_step with Store.apply_rep s31 v68 v80 _ _ hinv31 h64 h_v68 h_v80 (by ns_tac) (by ns_tac) as ⟨v81, s32, hinv32, h_v81⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v30 h_v31 h_v33 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v44 h_v46 h_v48 h_v49 h_v51 h_v52 h_v53 h_v55 h_v56 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70 h_v71 h_v72 h_v73 h_v74 h_v75 h_v76 h_v77 h_v78 h_v79 h_v80
  case_done hinv32 hG with h_v81 in EoCases.__eo_prog_bv_udiv_pow2_not_one.case_0 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v17 hn_v18 hn_v20 hn_v21 hn_v24 hn_v25 hn_v27 hn_v28 hn_v35 hn_v36 hn_v38 hn_v39 hn_v42 hn_v43 hn_v48 hn_v49 hn_v51 hn_v52 hn_v55 hn_v56 hn_v58 hn_v59

/-- logos's `__eo_prog_bv_udiv_pow2_not_one` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fbv_2dudiv_2dpow2_2dnot_2done.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _) (x_a7 : _) (x_a8 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) (hw_a4 : Valid.valid x_a4) (hw_a5 : Valid.valid x_a5) (hw_a6 : Valid.valid x_a6) (hw_a7 : Valid.valid x_a7) (hw_a8 : Valid.valid x_a8) :
    __eo_prog_bv_udiv_pow2_not_one x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else if x_a4 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_bv_udiv_pow2_not_one.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_bv_udiv_pow2_not_one
  unfold EoCases.__eo_prog_bv_udiv_pow2_not_one.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fbv_2dudiv_2dpow2_2dnot_2done_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 a6 a7 a8 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _) (x_a7 : _) (x_a8 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) (h_a6 : Represents.rep s a6 x_a6) (h_a7 : Represents.rep s a7 x_a7) (h_a8 : Represents.rep s a8 x_a8) :
    body_eo__24eo_5fprog_5fbv_2dudiv_2dpow2_2dnot_2done s a0 a1 a2 a3 a4 a5 a6 a7 a8 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_udiv_pow2_not_one x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fbv_2dudiv_2dpow2_2dnot_2done.rust_eq x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3) (by valid_tac hinv h_a4) (by valid_tac hinv h_a5) (by valid_tac hinv h_a6) (by valid_tac hinv h_a7) (by valid_tac hinv h_a8)]
  unfold body_eo__24eo_5fprog_5fbv_2dudiv_2dpow2_2dnot_2done
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  stuck_check h_a3 : x_a3 as hn_a3 else hinv hG
  stuck_check h_a4 : x_a4 as hn_a4 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fbv_2dudiv_2dpow2_2dnot_2done_spec n ih s a0 a1 a2 a3 a4 a5 a6 a7 a8 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 hn_a0 hn_a1 hn_a2 hn_a3 hn_a4
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hc0 in EoCases.__eo_prog_bv_udiv_pow2_not_one.case_0

theorem eo__24eo_5fprog_5fbv_2dudiv_2dpow2_2dnot_2done_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fbv_2dudiv_2dpow2_2dnot_2done.Spec n := by
  intro s a0 a1 a2 a3 a4 a5 a6 a7 a8 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8
  unfold eo__24eo_5fprog_5fbv_2dudiv_2dpow2_2dnot_2done
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fbv_2dudiv_2dpow2_2dnot_2done s1 a0 a1 a2 a3 a4 a5 a6 a7 a8) (fun s' t => Represents.rep s' t (__eo_prog_bv_udiv_pow2_not_one x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fbv_2dudiv_2dpow2_2dnot_2done_spec m (ih m hm) s1 a0 a1 a2 a3 a4 a5 a6 a7 a8 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn) (by congr_one h_a4 hn) (by congr_one h_a5 hn) (by congr_one h_a6 hn) (by congr_one h_a7 hn) (by congr_one h_a8 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fbv_2dudiv_2dzero_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fbv_2dudiv_2dzero s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_bv_udiv_zero.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_bv_udiv_zero.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fbv_2dudiv_2dzero more_0_eo__24eo_5fprog_5fbv_2dudiv_2dzero
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_bvudiv.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s3 e_v3 (by rw [he_v3]; rfl) h_a1 hinv3 h64 as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s4 0#u32 (0) (by scalar_tac) hinv4 h64 as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3
  store_step with Store.apply_rep s5 v3 v4 _ _ hinv5 h64 h_v3 h_v4 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4
  store_step with Store.apply_rep s6 v2 v5 _ _ hinv6 h64 h_v2 h_v5 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with Store.apply_rep s7 v0 v6 _ _ hinv7 h64 h_v0 h_v6 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo_bvnot.construct s8 e_v8 (by rw [he_v8]; exact empty_args) hinv8 h64 as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s9 e_v9 (by rw [he_v9]; rfl) h_a1 hinv9 h64 as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s10 0#u32 (0) (by scalar_tac) hinv10 h64 as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  store_step with Store.apply_rep s11 v9 v10 _ _ hinv11 h64 h_v9 h_v10 (by ns_tac) (by ns_tac) as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
  store_step with Store.apply_rep s12 v8 v11 _ _ hinv12 h64 h_v8 h_v11 (by ns_tac) (by ns_tac) as ⟨v12, s13, hinv13, h_v12⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11
  store_step with Store.apply_rep s13 v7 v12 _ _ hinv13 h64 h_v7 h_v12 (by ns_tac) (by ns_tac) as ⟨v13, s14, hinv14, h_v13⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
  case_done hinv14 hG with h_v13 in EoCases.__eo_prog_bv_udiv_zero.case_0 using hn_a0 hn_a1

/-- logos's `__eo_prog_bv_udiv_zero` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fbv_2dudiv_2dzero.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_bv_udiv_zero x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_bv_udiv_zero.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_bv_udiv_zero
  unfold EoCases.__eo_prog_bv_udiv_zero.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fbv_2dudiv_2dzero_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5fbv_2dudiv_2dzero s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_udiv_zero x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fbv_2dudiv_2dzero.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5fbv_2dudiv_2dzero
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fbv_2dudiv_2dzero_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_bv_udiv_zero.case_0

theorem eo__24eo_5fprog_5fbv_2dudiv_2dzero_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fbv_2dudiv_2dzero.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5fbv_2dudiv_2dzero
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fbv_2dudiv_2dzero s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_bv_udiv_zero x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fbv_2dudiv_2dzero_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fbv_2duge_2deliminate_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fbv_2duge_2deliminate s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_bv_uge_eliminate.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_bv_uge_eliminate.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fbv_2duge_2deliminate
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_bvuge.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a1 _ _ hinv3 h64 h_v2 h_a1 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v0 v3 _ _ hinv4 h64 h_v0 h_v3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo_bvule.construct s5 e_v5 (by rw [he_v5]; exact empty_args) hinv5 h64 as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4
  store_step with Store.apply_rep s6 v5 a1 _ _ hinv6 h64 h_v5 h_a1 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with Store.apply_rep s7 v6 a0 _ _ hinv7 h64 h_v6 h_a0 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  store_step with Store.apply_rep s8 v4 v7 _ _ hinv8 h64 h_v4 h_v7 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  case_done hinv9 hG with h_v8 in EoCases.__eo_prog_bv_uge_eliminate.case_0 using hn_a0 hn_a1

/-- logos's `__eo_prog_bv_uge_eliminate` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fbv_2duge_2deliminate.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_bv_uge_eliminate x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_bv_uge_eliminate.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_bv_uge_eliminate
  unfold EoCases.__eo_prog_bv_uge_eliminate.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fbv_2duge_2deliminate_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5fbv_2duge_2deliminate s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_uge_eliminate x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fbv_2duge_2deliminate.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5fbv_2duge_2deliminate
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fbv_2duge_2deliminate_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_bv_uge_eliminate.case_0

theorem eo__24eo_5fprog_5fbv_2duge_2deliminate_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fbv_2duge_2deliminate.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5fbv_2duge_2deliminate
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fbv_2duge_2deliminate s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_bv_uge_eliminate x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fbv_2duge_2deliminate_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

end pathos_compiled_checker
