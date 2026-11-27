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
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 dropping he_v0 e_v0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_bvshl.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0 dropping he_v1 hinv1 e_v1 s1
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 dropping h_v1 hinv2 s2 v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s3 e_v3 (by rw [he_v3]; rfl) h_a1 hinv3 h64 as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_v0 h_v2 dropping h_a1 he_v3 hinv3 e_v3 s3
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s4 0#u32 (0) (by scalar_tac) hinv4 h64 as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_v0 h_v2 h_v3 dropping hinv4 s4
  store_step with Store.apply_rep s5 v3 v4 _ _ hinv5 h64 h_v3 h_v4 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_v0 h_v2 dropping h_v3 h_v4 hinv5 s5 v3 v4
  store_step with Store.apply_rep s6 v2 v5 _ _ hinv6 h64 h_v2 h_v5 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_v0 dropping h_v2 h_v5 hinv6 s6 v2 v5
  store_step with Store.apply_rep s7 v0 v6 _ _ hinv7 h64 h_v0 h_v6 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 dropping h_v0 h_v6 hinv7 s7 v0 v6
  store_step with Store.apply_rep s8 v7 a0 _ _ hinv8 h64 h_v7 h_a0 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying dropping h_a0 h_v7 hinv8 s8 v7
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
  unfold case_0_eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d1
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a4 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_bv_shl_by_const_1.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_shl_by_const_1.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_shl_by_const_1.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a5 h_v4 h_v6 h_v7 dropping h_a4 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_shl_by_const_1.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_shl_by_const_1.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_shl_by_const_1.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__3c.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a5 h_v4 h_v11 h_v13 h_v14 dropping h_v10 h_v6 h_v7 h_v8 he_v15 hinv1 e_v15 s1 v10 v6 v7 v8
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_shl_by_const_1.case_0
  pat_same v14 a1 with h_v14 h_a1 using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_shl_by_const_1.case_0
  pat_unapply h_v11 as ⟨v17, v18, x_v17, x_v18, h_v17, h_v18, hn_v17, hn_v18⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_shl_by_const_1.case_0
  step as ⟨e_v19, he_v19⟩
  store_step with CtorSpec.eo__40bvsize.construct s2 e_v19 (by rw [he_v19]; exact empty_args) hinv2 h64 as ⟨v19, s3, hinv3, h_v19⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a5 h_v4 h_v17 h_v18 dropping h_v11 h_v13 h_v14 h_v15 he_v19 hinv2 e_v19 s2 v11 v13 v14 v15
  pat_same v17 v19 with h_v17 h_v19 using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_shl_by_const_1.case_0
  pat_same v18 a0 with h_v18 h_a0 using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_shl_by_const_1.case_0
  store_step with Store.literal_boolean_spec s3 true hinv3 h64 as ⟨v20, s4, hinv4, h_v20⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a5 h_v4 dropping h_v17 h_v18 h_v19 hinv3 s3 v17 v18 v19
  pat_same v4 v20 with h_v4 h_v20 using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_shl_by_const_1.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a5 as ⟨v22, x_v22, h_v22⟩ else hinv4 hG in EoCases.__eo_prog_bv_shl_by_const_1.case_0
  pat_unapply h_v22 as ⟨v24, v25, x_v24, x_v25, h_v24, h_v25, hn_v24, hn_v25⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_shl_by_const_1.case_0
  pat_unapply h_v24 as ⟨v27, v28, x_v27, x_v28, h_v27, h_v28, hn_v27, hn_v28⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_shl_by_const_1.case_0
  step as ⟨e_v29, he_v29⟩
  store_step with CtorSpec.eo__3d.construct s4 e_v29 (by rw [he_v29]; exact empty_args) hinv4 h64 as ⟨v29, s5, hinv5, h_v29⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v25 h_v27 h_v28 dropping h_a5 h_v20 h_v22 h_v24 h_v4 he_v29 hinv4 e_v29 s4 v20 v22 v24 v4
  pat_same v27 v29 with h_v27 h_v29 using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_shl_by_const_1.case_0
  pat_same v28 a3 with h_v28 h_a3 using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_shl_by_const_1.case_0
  pat_unapply h_v25 as ⟨v31, v32, x_v31, x_v32, h_v31, h_v32, hn_v31, hn_v32⟩ using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_shl_by_const_1.case_0
  pat_unapply h_v31 as ⟨v34, v35, x_v34, x_v35, h_v34, h_v35, hn_v34, hn_v35⟩ using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_shl_by_const_1.case_0
  step as ⟨e_v36, he_v36⟩
  store_step with CtorSpec.eo__2d.construct s5 e_v36 (by rw [he_v36]; exact empty_args) hinv5 h64 as ⟨v36, s6, hinv6, h_v36⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v32 h_v34 h_v35 dropping h_v25 h_v27 h_v28 h_v29 h_v31 he_v36 hinv5 e_v36 s5 v25 v27 v28 v29 v31
  pat_same v34 v36 with h_v34 h_v36 using hinv6 else hinv6 hG in EoCases.__eo_prog_bv_shl_by_const_1.case_0
  pat_unapply h_v35 as ⟨v38, v39, x_v38, x_v39, h_v38, h_v39, hn_v38, hn_v39⟩ using hinv6 else hinv6 hG in EoCases.__eo_prog_bv_shl_by_const_1.case_0
  step as ⟨e_v40, he_v40⟩
  store_step with CtorSpec.eo__40bvsize.construct s6 e_v40 (by rw [he_v40]; exact empty_args) hinv6 h64 as ⟨v40, s7, hinv7, h_v40⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v32 h_v38 h_v39 dropping h_v34 h_v35 h_v36 he_v40 hinv6 e_v40 s6 v34 v35 v36
  pat_same v38 v40 with h_v38 h_v40 using hinv7 else hinv7 hG in EoCases.__eo_prog_bv_shl_by_const_1.case_0
  pat_same v39 a0 with h_v39 h_a0 using hinv7 else hinv7 hG in EoCases.__eo_prog_bv_shl_by_const_1.case_0
  pat_unapply h_v32 as ⟨v42, v43, x_v42, x_v43, h_v42, h_v43, hn_v42, hn_v43⟩ using hinv7 else hinv7 hG in EoCases.__eo_prog_bv_shl_by_const_1.case_0
  pat_unapply h_v42 as ⟨v45, v46, x_v45, x_v46, h_v45, h_v46, hn_v45, hn_v46⟩ using hinv7 else hinv7 hG in EoCases.__eo_prog_bv_shl_by_const_1.case_0
  step as ⟨e_v47, he_v47⟩
  store_step with CtorSpec.eo__2b.construct s7 e_v47 (by rw [he_v47]; exact empty_args) hinv7 h64 as ⟨v47, s8, hinv8, h_v47⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v43 h_v45 h_v46 dropping h_v32 h_v38 h_v39 h_v40 h_v42 he_v47 hinv7 e_v47 s7 v32 v38 v39 v40 v42
  pat_same v45 v47 with h_v45 h_v47 using hinv8 else hinv8 hG in EoCases.__eo_prog_bv_shl_by_const_1.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s8 1#u32 (1) (by scalar_tac) hinv8 h64 as ⟨v48, s9, hinv9, h_v48⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v43 h_v46 dropping h_v45 h_v47 hinv8 s8 v45 v47
  pat_same v46 v48 with h_v46 h_v48 using hinv9 else hinv9 hG in EoCases.__eo_prog_bv_shl_by_const_1.case_0
  pat_unapply h_v43 as ⟨v50, v51, x_v50, x_v51, h_v50, h_v51, hn_v50, hn_v51⟩ using hinv9 else hinv9 hG in EoCases.__eo_prog_bv_shl_by_const_1.case_0
  pat_unapply h_v50 as ⟨v53, v54, x_v53, x_v54, h_v53, h_v54, hn_v53, hn_v54⟩ using hinv9 else hinv9 hG in EoCases.__eo_prog_bv_shl_by_const_1.case_0
  step as ⟨e_v55, he_v55⟩
  store_step with CtorSpec.eo__2b.construct s9 e_v55 (by rw [he_v55]; exact empty_args) hinv9 h64 as ⟨v55, s10, hinv10, h_v55⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v51 h_v53 h_v54 dropping h_v43 h_v46 h_v48 h_v50 he_v55 hinv9 e_v55 s9 v43 v46 v48 v50
  pat_same v53 v55 with h_v53 h_v55 using hinv10 else hinv10 hG in EoCases.__eo_prog_bv_shl_by_const_1.case_0
  pat_same v54 a1 with h_v54 h_a1 using hinv10 else hinv10 hG in EoCases.__eo_prog_bv_shl_by_const_1.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s10 0#u32 (0) (by scalar_tac) hinv10 h64 as ⟨v56, s11, hinv11, h_v56⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v51 dropping h_v53 h_v54 h_v55 hinv10 s10 v53 v54 v55
  pat_same v51 v56 with h_v51 h_v56 using hinv11 else hinv11 hG in EoCases.__eo_prog_bv_shl_by_const_1.case_0
  step as ⟨e_v57, he_v57⟩
  store_step with CtorSpec.eo__3d.construct s11 e_v57 (by rw [he_v57]; exact empty_args) hinv11 h64 as ⟨v57, s12, hinv12, h_v57⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 dropping h_v51 h_v56 he_v57 hinv11 e_v57 s11 v51 v56
  step as ⟨e_v58, he_v58⟩
  store_step with CtorSpec.eo_bvshl.construct s12 e_v58 (by rw [he_v58]; exact empty_args) hinv12 h64 as ⟨v58, s13, hinv13, h_v58⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v57 dropping he_v58 hinv12 e_v58 s12
  store_step with Store.apply_rep s13 v58 a0 _ _ hinv13 h64 h_v58 h_a0 (by ns_tac) (by ns_tac) as ⟨v59, s14, hinv14, h_v59⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v57 dropping h_v58 hinv13 s13 v58
  step as ⟨e_v60, he_v60⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s14 e_v60 (by rw [he_v60]; rfl) h_a2 hinv14 h64 as ⟨v60, s15, hinv15, h_v60⟩ growing hG carrying h_a0 h_a1 h_a3 h_v57 h_v59 dropping h_a2 he_v60 hinv14 e_v60 s14
  store_step with Store.apply_rep s15 v60 a1 _ _ hinv15 h64 h_v60 h_a1 (by ns_tac) (by ns_tac) as ⟨v61, s16, hinv16, h_v61⟩ growing hG carrying h_a0 h_a1 h_a3 h_v57 h_v59 dropping h_v60 hinv15 s15 v60
  store_step with Store.apply_rep s16 v59 v61 _ _ hinv16 h64 h_v59 h_v61 (by ns_tac) (by ns_tac) as ⟨v62, s17, hinv17, h_v62⟩ growing hG carrying h_a0 h_a1 h_a3 h_v57 dropping h_v59 h_v61 hinv16 s16 v59 v61
  store_step with Store.apply_rep s17 v57 v62 _ _ hinv17 h64 h_v57 h_v62 (by ns_tac) (by ns_tac) as ⟨v63, s18, hinv18, h_v63⟩ growing hG carrying h_a0 h_a1 h_a3 dropping h_v57 h_v62 hinv17 s17 v57 v62
  step as ⟨e_v64, he_v64⟩
  store_step with CtorSpec.eo_concat.construct s18 e_v64 (by rw [he_v64]; exact empty_args) hinv18 h64 as ⟨v64, s19, hinv19, h_v64⟩ growing hG carrying h_a0 h_a1 h_a3 h_v63 dropping he_v64 hinv18 e_v64 s18
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s19 0#u32 (0) (by scalar_tac) hinv19 h64 as ⟨v65, s20, hinv20, h_v65⟩ growing hG carrying h_a0 h_a1 h_a3 h_v63 h_v64 dropping hinv19 s19
  step as ⟨e_v66, he_v66⟩
  store_step with CtorSpec.eo_extract.construct s20 e_v66 (by rw [he_v66]; rfl) h_a3 h_v65 hinv20 h64 as ⟨v66, s21, hinv21, h_v66⟩ growing hG carrying h_a0 h_a1 h_v63 h_v64 dropping h_a3 h_v65 he_v66 hinv20 e_v66 s20 v65
  store_step with Store.apply_rep s21 v66 a0 _ _ hinv21 h64 h_v66 h_a0 (by ns_tac) (by ns_tac) as ⟨v67, s22, hinv22, h_v67⟩ growing hG carrying h_a1 h_v63 h_v64 dropping h_a0 h_v66 hinv21 s21 v66
  store_step with Store.apply_rep s22 v64 v67 _ _ hinv22 h64 h_v64 h_v67 (by ns_tac) (by ns_tac) as ⟨v68, s23, hinv23, h_v68⟩ growing hG carrying h_a1 h_v63 dropping h_v64 h_v67 hinv22 s22 v64 v67
  step as ⟨e_v69, he_v69⟩
  store_step with CtorSpec.eo_concat.construct s23 e_v69 (by rw [he_v69]; exact empty_args) hinv23 h64 as ⟨v69, s24, hinv24, h_v69⟩ growing hG carrying h_a1 h_v63 h_v68 dropping he_v69 hinv23 e_v69 s23
  step as ⟨e_v70, he_v70⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s24 e_v70 (by rw [he_v70]; rfl) h_a1 hinv24 h64 as ⟨v70, s25, hinv25, h_v70⟩ growing hG carrying h_v63 h_v68 h_v69 dropping h_a1 he_v70 hinv24 e_v70 s24
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s25 0#u32 (0) (by scalar_tac) hinv25 h64 as ⟨v71, s26, hinv26, h_v71⟩ growing hG carrying h_v63 h_v68 h_v69 h_v70 dropping hinv25 s25
  store_step with Store.apply_rep s26 v70 v71 _ _ hinv26 h64 h_v70 h_v71 (by ns_tac) (by ns_tac) as ⟨v72, s27, hinv27, h_v72⟩ growing hG carrying h_v63 h_v68 h_v69 dropping h_v70 h_v71 hinv26 s26 v70 v71
  store_step with Store.apply_rep s27 v69 v72 _ _ hinv27 h64 h_v69 h_v72 (by ns_tac) (by ns_tac) as ⟨v73, s28, hinv28, h_v73⟩ growing hG carrying h_v63 h_v68 dropping h_v69 h_v72 hinv27 s27 v69 v72
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s28 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv28 h64 as ⟨v74, s29, hinv29, h_v74⟩ growing hG carrying h_v63 h_v68 h_v73 dropping hinv28 s28
  store_step with Store.apply_rep s29 v73 v74 _ _ hinv29 h64 h_v73 h_v74 (by ns_tac) (by ns_tac) as ⟨v75, s30, hinv30, h_v75⟩ growing hG carrying h_v63 h_v68 dropping h_v73 h_v74 hinv29 s29 v73 v74
  store_step with Store.apply_rep s30 v68 v75 _ _ hinv30 h64 h_v68 h_v75 (by ns_tac) (by ns_tac) as ⟨v76, s31, hinv31, h_v76⟩ growing hG carrying h_v63 dropping h_v68 h_v75 hinv30 s30 v68 v75
  store_step with Store.apply_rep s31 v63 v76 _ _ hinv31 h64 h_v63 h_v76 (by ns_tac) (by ns_tac) as ⟨v77, s32, hinv32, h_v77⟩ growing hG carrying dropping h_v63 h_v76 hinv31 s31 v63 v76
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
  unfold case_0_eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d2
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a4 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_bv_shl_by_const_2.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_shl_by_const_2.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_shl_by_const_2.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a5 h_a6 h_v4 h_v6 h_v7 dropping h_a4 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_shl_by_const_2.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_shl_by_const_2.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_shl_by_const_2.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__3e_3d.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a5 h_a6 h_v4 h_v11 h_v13 h_v14 dropping h_v10 h_v6 h_v7 h_v8 he_v15 hinv1 e_v15 s1 v10 v6 v7 v8
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_shl_by_const_2.case_0
  pat_same v14 a1 with h_v14 h_a1 using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_shl_by_const_2.case_0
  pat_unapply h_v11 as ⟨v17, v18, x_v17, x_v18, h_v17, h_v18, hn_v17, hn_v18⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_shl_by_const_2.case_0
  step as ⟨e_v19, he_v19⟩
  store_step with CtorSpec.eo__40bvsize.construct s2 e_v19 (by rw [he_v19]; exact empty_args) hinv2 h64 as ⟨v19, s3, hinv3, h_v19⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a5 h_a6 h_v4 h_v17 h_v18 dropping h_v11 h_v13 h_v14 h_v15 he_v19 hinv2 e_v19 s2 v11 v13 v14 v15
  pat_same v17 v19 with h_v17 h_v19 using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_shl_by_const_2.case_0
  pat_same v18 a0 with h_v18 h_a0 using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_shl_by_const_2.case_0
  store_step with Store.literal_boolean_spec s3 true hinv3 h64 as ⟨v20, s4, hinv4, h_v20⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a5 h_a6 h_v4 dropping h_v17 h_v18 h_v19 hinv3 s3 v17 v18 v19
  pat_same v4 v20 with h_v4 h_v20 using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_shl_by_const_2.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a5 as ⟨v22, x_v22, h_v22⟩ else hinv4 hG in EoCases.__eo_prog_bv_shl_by_const_2.case_0
  pat_unapply h_v22 as ⟨v24, v25, x_v24, x_v25, h_v24, h_v25, hn_v24, hn_v25⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_shl_by_const_2.case_0
  pat_unapply h_v24 as ⟨v27, v28, x_v27, x_v28, h_v27, h_v28, hn_v27, hn_v28⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_shl_by_const_2.case_0
  step as ⟨e_v29, he_v29⟩
  store_step with CtorSpec.eo__3d.construct s4 e_v29 (by rw [he_v29]; exact empty_args) hinv4 h64 as ⟨v29, s5, hinv5, h_v29⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a6 h_v25 h_v27 h_v28 dropping h_a5 h_v20 h_v22 h_v24 h_v4 he_v29 hinv4 e_v29 s4 v20 v22 v24 v4
  pat_same v27 v29 with h_v27 h_v29 using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_shl_by_const_2.case_0
  pat_unapply h_v28 as ⟨v31, v32, x_v31, x_v32, h_v31, h_v32, hn_v31, hn_v32⟩ using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_shl_by_const_2.case_0
  pat_unapply h_v31 as ⟨v34, v35, x_v34, x_v35, h_v34, h_v35, hn_v34, hn_v35⟩ using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_shl_by_const_2.case_0
  step as ⟨e_v36, he_v36⟩
  store_step with CtorSpec.eo__3c.construct s5 e_v36 (by rw [he_v36]; exact empty_args) hinv5 h64 as ⟨v36, s6, hinv6, h_v36⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a6 h_v25 h_v32 h_v34 h_v35 dropping h_v27 h_v28 h_v29 h_v31 he_v36 hinv5 e_v36 s5 v27 v28 v29 v31
  pat_same v34 v36 with h_v34 h_v36 using hinv6 else hinv6 hG in EoCases.__eo_prog_bv_shl_by_const_2.case_0
  pat_same v35 a1 with h_v35 h_a1 using hinv6 else hinv6 hG in EoCases.__eo_prog_bv_shl_by_const_2.case_0
  pat_unapply h_v32 as ⟨v38, v39, x_v38, x_v39, h_v38, h_v39, hn_v38, hn_v39⟩ using hinv6 else hinv6 hG in EoCases.__eo_prog_bv_shl_by_const_2.case_0
  step as ⟨e_v40, he_v40⟩
  store_step with CtorSpec.eo_int_2epow2.construct s6 e_v40 (by rw [he_v40]; exact empty_args) hinv6 h64 as ⟨v40, s7, hinv7, h_v40⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a6 h_v25 h_v38 h_v39 dropping h_v32 h_v34 h_v35 h_v36 he_v40 hinv6 e_v40 s6 v32 v34 v35 v36
  pat_same v38 v40 with h_v38 h_v40 using hinv7 else hinv7 hG in EoCases.__eo_prog_bv_shl_by_const_2.case_0
  pat_unapply h_v39 as ⟨v42, v43, x_v42, x_v43, h_v42, h_v43, hn_v42, hn_v43⟩ using hinv7 else hinv7 hG in EoCases.__eo_prog_bv_shl_by_const_2.case_0
  step as ⟨e_v44, he_v44⟩
  store_step with CtorSpec.eo__40bvsize.construct s7 e_v44 (by rw [he_v44]; exact empty_args) hinv7 h64 as ⟨v44, s8, hinv8, h_v44⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a6 h_v25 h_v42 h_v43 dropping h_v38 h_v39 h_v40 he_v44 hinv7 e_v44 s7 v38 v39 v40
  pat_same v42 v44 with h_v42 h_v44 using hinv8 else hinv8 hG in EoCases.__eo_prog_bv_shl_by_const_2.case_0
  pat_same v43 a0 with h_v43 h_a0 using hinv8 else hinv8 hG in EoCases.__eo_prog_bv_shl_by_const_2.case_0
  store_step with Store.literal_boolean_spec s8 true hinv8 h64 as ⟨v45, s9, hinv9, h_v45⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a6 h_v25 dropping h_v42 h_v43 h_v44 hinv8 s8 v42 v43 v44
  pat_same v25 v45 with h_v25 h_v45 using hinv9 else hinv9 hG in EoCases.__eo_prog_bv_shl_by_const_2.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a6 as ⟨v47, x_v47, h_v47⟩ else hinv9 hG in EoCases.__eo_prog_bv_shl_by_const_2.case_0
  pat_unapply h_v47 as ⟨v49, v50, x_v49, x_v50, h_v49, h_v50, hn_v49, hn_v50⟩ using hinv9 else hinv9 hG in EoCases.__eo_prog_bv_shl_by_const_2.case_0
  pat_unapply h_v49 as ⟨v52, v53, x_v52, x_v53, h_v52, h_v53, hn_v52, hn_v53⟩ using hinv9 else hinv9 hG in EoCases.__eo_prog_bv_shl_by_const_2.case_0
  step as ⟨e_v54, he_v54⟩
  store_step with CtorSpec.eo__3d.construct s9 e_v54 (by rw [he_v54]; exact empty_args) hinv9 h64 as ⟨v54, s10, hinv10, h_v54⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v50 h_v52 h_v53 dropping h_a6 h_v25 h_v45 h_v47 h_v49 he_v54 hinv9 e_v54 s9 v25 v45 v47 v49
  pat_same v52 v54 with h_v52 h_v54 using hinv10 else hinv10 hG in EoCases.__eo_prog_bv_shl_by_const_2.case_0
  pat_same v53 a3 with h_v53 h_a3 using hinv10 else hinv10 hG in EoCases.__eo_prog_bv_shl_by_const_2.case_0
  pat_unapply h_v50 as ⟨v56, v57, x_v56, x_v57, h_v56, h_v57, hn_v56, hn_v57⟩ using hinv10 else hinv10 hG in EoCases.__eo_prog_bv_shl_by_const_2.case_0
  step as ⟨e_v58, he_v58⟩
  store_step with CtorSpec.eo__40bvsize.construct s10 e_v58 (by rw [he_v58]; exact empty_args) hinv10 h64 as ⟨v58, s11, hinv11, h_v58⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v56 h_v57 dropping h_v50 h_v52 h_v53 h_v54 he_v58 hinv10 e_v58 s10 v50 v52 v53 v54
  pat_same v56 v58 with h_v56 h_v58 using hinv11 else hinv11 hG in EoCases.__eo_prog_bv_shl_by_const_2.case_0
  pat_same v57 a0 with h_v57 h_a0 using hinv11 else hinv11 hG in EoCases.__eo_prog_bv_shl_by_const_2.case_0
  step as ⟨e_v59, he_v59⟩
  store_step with CtorSpec.eo__3d.construct s11 e_v59 (by rw [he_v59]; exact empty_args) hinv11 h64 as ⟨v59, s12, hinv12, h_v59⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 dropping h_v56 h_v57 h_v58 he_v59 hinv11 e_v59 s11 v56 v57 v58
  step as ⟨e_v60, he_v60⟩
  store_step with CtorSpec.eo_bvshl.construct s12 e_v60 (by rw [he_v60]; exact empty_args) hinv12 h64 as ⟨v60, s13, hinv13, h_v60⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v59 dropping he_v60 hinv12 e_v60 s12
  store_step with Store.apply_rep s13 v60 a0 _ _ hinv13 h64 h_v60 h_a0 (by ns_tac) (by ns_tac) as ⟨v61, s14, hinv14, h_v61⟩ growing hG carrying h_a1 h_a2 h_a3 h_v59 dropping h_a0 h_v60 hinv13 s13 v60
  step as ⟨e_v62, he_v62⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s14 e_v62 (by rw [he_v62]; rfl) h_a2 hinv14 h64 as ⟨v62, s15, hinv15, h_v62⟩ growing hG carrying h_a1 h_a3 h_v59 h_v61 dropping h_a2 he_v62 hinv14 e_v62 s14
  store_step with Store.apply_rep s15 v62 a1 _ _ hinv15 h64 h_v62 h_a1 (by ns_tac) (by ns_tac) as ⟨v63, s16, hinv16, h_v63⟩ growing hG carrying h_a3 h_v59 h_v61 dropping h_a1 h_v62 hinv15 s15 v62
  store_step with Store.apply_rep s16 v61 v63 _ _ hinv16 h64 h_v61 h_v63 (by ns_tac) (by ns_tac) as ⟨v64, s17, hinv17, h_v64⟩ growing hG carrying h_a3 h_v59 dropping h_v61 h_v63 hinv16 s16 v61 v63
  store_step with Store.apply_rep s17 v59 v64 _ _ hinv17 h64 h_v59 h_v64 (by ns_tac) (by ns_tac) as ⟨v65, s18, hinv18, h_v65⟩ growing hG carrying h_a3 dropping h_v59 h_v64 hinv17 s17 v59 v64
  step as ⟨e_v66, he_v66⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s18 e_v66 (by rw [he_v66]; rfl) h_a3 hinv18 h64 as ⟨v66, s19, hinv19, h_v66⟩ growing hG carrying h_v65 dropping h_a3 he_v66 hinv18 e_v66 s18
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s19 0#u32 (0) (by scalar_tac) hinv19 h64 as ⟨v67, s20, hinv20, h_v67⟩ growing hG carrying h_v65 h_v66 dropping hinv19 s19
  store_step with Store.apply_rep s20 v66 v67 _ _ hinv20 h64 h_v66 h_v67 (by ns_tac) (by ns_tac) as ⟨v68, s21, hinv21, h_v68⟩ growing hG carrying h_v65 dropping h_v66 h_v67 hinv20 s20 v66 v67
  store_step with Store.apply_rep s21 v65 v68 _ _ hinv21 h64 h_v65 h_v68 (by ns_tac) (by ns_tac) as ⟨v69, s22, hinv22, h_v69⟩ growing hG carrying dropping h_v65 h_v68 hinv21 s21 v65 v68
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
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 dropping he_v0 e_v0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_bvshl.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0 dropping he_v1 hinv1 e_v1 s1
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s2 e_v2 (by rw [he_v2]; rfl) h_a1 hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 dropping he_v2 hinv2 e_v2 s2
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s3 0#u32 (0) (by scalar_tac) hinv3 h64 as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 dropping hinv3 s3
  store_step with Store.apply_rep s4 v2 v3 _ _ hinv4 h64 h_v2 h_v3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 dropping h_v2 h_v3 hinv4 s4 v2 v3
  store_step with Store.apply_rep s5 v1 v4 _ _ hinv5 h64 h_v1 h_v4 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_v0 dropping h_v1 h_v4 hinv5 s5 v1 v4
  store_step with Store.apply_rep s6 v5 a0 _ _ hinv6 h64 h_v5 h_a0 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a1 h_v0 dropping h_a0 h_v5 hinv6 s6 v5
  store_step with Store.apply_rep s7 v0 v6 _ _ hinv7 h64 h_v0 h_v6 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a1 dropping h_v0 h_v6 hinv7 s7 v0 v6
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s8 e_v8 (by rw [he_v8]; rfl) h_a1 hinv8 h64 as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_v7 dropping h_a1 he_v8 hinv8 e_v8 s8
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s9 0#u32 (0) (by scalar_tac) hinv9 h64 as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_v7 h_v8 dropping hinv9 s9
  store_step with Store.apply_rep s10 v8 v9 _ _ hinv10 h64 h_v8 h_v9 (by ns_tac) (by ns_tac) as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_v7 dropping h_v8 h_v9 hinv10 s10 v8 v9
  store_step with Store.apply_rep s11 v7 v10 _ _ hinv11 h64 h_v7 h_v10 (by ns_tac) (by ns_tac) as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying dropping h_v10 h_v7 hinv11 s11 v10 v7
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
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 dropping he_v0 e_v0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s1 0#u32 (0) (by scalar_tac) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0 dropping hinv1 s1
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo_sign_5fextend.construct s2 e_v2 (by rw [he_v2]; rfl) h_v1 hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_v0 dropping h_v1 he_v2 hinv2 e_v2 s2 v1
  store_step with Store.apply_rep s3 v2 a0 _ _ hinv3 h64 h_v2 h_a0 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_v0 dropping h_v2 hinv3 s3 v2
  store_step with Store.apply_rep s4 v0 v3 _ _ hinv4 h64 h_v0 h_v3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 dropping h_v0 h_v3 hinv4 s4 v0 v3
  store_step with Store.apply_rep s5 v4 a0 _ _ hinv5 h64 h_v4 h_a0 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying dropping h_a0 h_v4 hinv5 s5 v4
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
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 dropping he_v0 e_v0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_bvsle.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0 dropping he_v1 hinv1 e_v1 s1
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 dropping h_v1 hinv2 s2 v1
  store_step with Store.apply_rep s3 v2 a1 _ _ hinv3 h64 h_v2 h_a1 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_v0 dropping h_v2 hinv3 s3 v2
  store_step with Store.apply_rep s4 v0 v3 _ _ hinv4 h64 h_v0 h_v3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 dropping h_v0 h_v3 hinv4 s4 v0 v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo_not.construct s5 e_v5 (by rw [he_v5]; exact empty_args) hinv5 h64 as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_v4 dropping he_v5 hinv5 e_v5 s5
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_bvslt.construct s6 e_v6 (by rw [he_v6]; exact empty_args) hinv6 h64 as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_v4 h_v5 dropping he_v6 hinv6 e_v6 s6
  store_step with Store.apply_rep s7 v6 a1 _ _ hinv7 h64 h_v6 h_a1 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_v4 h_v5 dropping h_a1 h_v6 hinv7 s7 v6
  store_step with Store.apply_rep s8 v7 a0 _ _ hinv8 h64 h_v7 h_a0 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_v4 h_v5 dropping h_a0 h_v7 hinv8 s8 v7
  store_step with Store.apply_rep s9 v5 v8 _ _ hinv9 h64 h_v5 h_v8 (by ns_tac) (by ns_tac) as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_v4 dropping h_v5 h_v8 hinv9 s9 v5 v8
  store_step with Store.apply_rep s10 v4 v9 _ _ hinv10 h64 h_v4 h_v9 (by ns_tac) (by ns_tac) as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying dropping h_v4 h_v9 hinv10 s10 v4 v9
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
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 dropping he_v0 e_v0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_bvsle.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0 dropping he_v1 hinv1 e_v1 s1
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_v0 dropping h_v1 hinv2 s2 v1
  store_step with Store.apply_rep s3 v2 a0 _ _ hinv3 h64 h_v2 h_a0 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_v0 dropping h_a0 h_v2 hinv3 s3 v2
  store_step with Store.apply_rep s4 v0 v3 _ _ hinv4 h64 h_v0 h_v3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying dropping h_v0 h_v3 hinv4 s4 v0 v3
  store_step with Store.literal_boolean_spec s5 true hinv5 h64 as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_v4 dropping hinv5 s5
  store_step with Store.apply_rep s6 v4 v5 _ _ hinv6 h64 h_v4 h_v5 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying dropping h_v4 h_v5 hinv6 s6 v4 v5
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

set_option maxHeartbeats 11910000 in
theorem case_0_eo__24eo_5fprog_5fbv_2dsmod_2deliminate_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fbv_2dsmod_2deliminate s a0 a1 a2 a3 a4 a5 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_bv_smod_eliminate.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_bv_smod_eliminate.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fbv_2dsmod_2deliminate
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a4 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_bv_smod_eliminate.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_smod_eliminate.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_smod_eliminate.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a5 h_v4 h_v6 h_v7 dropping h_a4 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_smod_eliminate.case_0
  pat_same v7 a2 with h_v7 h_a2 using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_smod_eliminate.case_0
  pat_unapply h_v4 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_smod_eliminate.case_0
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo__40bvsize.construct s1 e_v12 (by rw [he_v12]; exact empty_args) hinv1 h64 as ⟨v12, s2, hinv2, h_v12⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a5 h_v10 h_v11 dropping h_v4 h_v6 h_v7 h_v8 he_v12 hinv1 e_v12 s1 v4 v6 v7 v8
  pat_same v10 v12 with h_v10 h_v12 using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_smod_eliminate.case_0
  pat_same v11 a0 with h_v11 h_a0 using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_smod_eliminate.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a5 as ⟨v14, x_v14, h_v14⟩ else hinv2 hG in EoCases.__eo_prog_bv_smod_eliminate.case_0
  pat_unapply h_v14 as ⟨v16, v17, x_v16, x_v17, h_v16, h_v17, hn_v16, hn_v17⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_smod_eliminate.case_0
  pat_unapply h_v16 as ⟨v19, v20, x_v19, x_v20, h_v19, h_v20, hn_v19, hn_v20⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_smod_eliminate.case_0
  step as ⟨e_v21, he_v21⟩
  store_step with CtorSpec.eo__3d.construct s2 e_v21 (by rw [he_v21]; exact empty_args) hinv2 h64 as ⟨v21, s3, hinv3, h_v21⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v17 h_v19 h_v20 dropping h_a5 h_v10 h_v11 h_v12 h_v14 h_v16 he_v21 hinv2 e_v21 s2 v10 v11 v12 v14 v16
  pat_same v19 v21 with h_v19 h_v21 using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_smod_eliminate.case_0
  pat_same v20 a3 with h_v20 h_a3 using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_smod_eliminate.case_0
  pat_unapply h_v17 as ⟨v23, v24, x_v23, x_v24, h_v23, h_v24, hn_v23, hn_v24⟩ using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_smod_eliminate.case_0
  pat_unapply h_v23 as ⟨v26, v27, x_v26, x_v27, h_v26, h_v27, hn_v26, hn_v27⟩ using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_smod_eliminate.case_0
  step as ⟨e_v28, he_v28⟩
  store_step with CtorSpec.eo__2d.construct s3 e_v28 (by rw [he_v28]; exact empty_args) hinv3 h64 as ⟨v28, s4, hinv4, h_v28⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v24 h_v26 h_v27 dropping h_v17 h_v19 h_v20 h_v21 h_v23 he_v28 hinv3 e_v28 s3 v17 v19 v20 v21 v23
  pat_same v26 v28 with h_v26 h_v28 using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_smod_eliminate.case_0
  pat_unapply h_v27 as ⟨v30, v31, x_v30, x_v31, h_v30, h_v31, hn_v30, hn_v31⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_smod_eliminate.case_0
  step as ⟨e_v32, he_v32⟩
  store_step with CtorSpec.eo__40bvsize.construct s4 e_v32 (by rw [he_v32]; exact empty_args) hinv4 h64 as ⟨v32, s5, hinv5, h_v32⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v24 h_v30 h_v31 dropping h_v26 h_v27 h_v28 he_v32 hinv4 e_v32 s4 v26 v27 v28
  pat_same v30 v32 with h_v30 h_v32 using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_smod_eliminate.case_0
  pat_same v31 a0 with h_v31 h_a0 using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_smod_eliminate.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s5 1#u32 (1) (by scalar_tac) hinv5 h64 as ⟨v33, s6, hinv6, h_v33⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v24 dropping h_v30 h_v31 h_v32 hinv5 s5 v30 v31 v32
  pat_same v24 v33 with h_v24 h_v33 using hinv6 else hinv6 hG in EoCases.__eo_prog_bv_smod_eliminate.case_0
  step as ⟨e_v34, he_v34⟩
  store_step with CtorSpec.eo__3d.construct s6 e_v34 (by rw [he_v34]; exact empty_args) hinv6 h64 as ⟨v34, s7, hinv7, h_v34⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 dropping h_v24 h_v33 he_v34 hinv6 e_v34 s6 v24 v33
  step as ⟨e_v35, he_v35⟩
  store_step with CtorSpec.eo_bvsmod.construct s7 e_v35 (by rw [he_v35]; exact empty_args) hinv7 h64 as ⟨v35, s8, hinv8, h_v35⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v34 dropping he_v35 hinv7 e_v35 s7
  store_step with Store.apply_rep s8 v35 a0 _ _ hinv8 h64 h_v35 h_a0 (by ns_tac) (by ns_tac) as ⟨v36, s9, hinv9, h_v36⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v34 dropping h_v35 hinv8 s8 v35
  store_step with Store.apply_rep s9 v36 a1 _ _ hinv9 h64 h_v36 h_a1 (by ns_tac) (by ns_tac) as ⟨v37, s10, hinv10, h_v37⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v34 dropping h_v36 hinv9 s9 v36
  store_step with Store.apply_rep s10 v34 v37 _ _ hinv10 h64 h_v34 h_v37 (by ns_tac) (by ns_tac) as ⟨v38, s11, hinv11, h_v38⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 dropping h_v34 h_v37 hinv10 s10 v34 v37
  step as ⟨e_v39, he_v39⟩
  store_step with CtorSpec.eo_ite.construct s11 e_v39 (by rw [he_v39]; exact empty_args) hinv11 h64 as ⟨v39, s12, hinv12, h_v39⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v38 dropping he_v39 hinv11 e_v39 s11
  step as ⟨e_v40, he_v40⟩
  store_step with CtorSpec.eo__3d.construct s12 e_v40 (by rw [he_v40]; exact empty_args) hinv12 h64 as ⟨v40, s13, hinv13, h_v40⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v38 h_v39 dropping he_v40 hinv12 e_v40 s12
  step as ⟨e_v41, he_v41⟩
  store_step with CtorSpec.eo_bvurem.construct s13 e_v41 (by rw [he_v41]; exact empty_args) hinv13 h64 as ⟨v41, s14, hinv14, h_v41⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v38 h_v39 h_v40 dropping he_v41 hinv13 e_v41 s13
  step as ⟨e_v42, he_v42⟩
  store_step with CtorSpec.eo_ite.construct s14 e_v42 (by rw [he_v42]; exact empty_args) hinv14 h64 as ⟨v42, s15, hinv15, h_v42⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v38 h_v39 h_v40 h_v41 dropping he_v42 hinv14 e_v42 s14
  step as ⟨e_v43, he_v43⟩
  store_step with CtorSpec.eo__3d.construct s15 e_v43 (by rw [he_v43]; exact empty_args) hinv15 h64 as ⟨v43, s16, hinv16, h_v43⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v38 h_v39 h_v40 h_v41 h_v42 dropping he_v43 hinv15 e_v43 s15
  step as ⟨e_v44, he_v44⟩
  store_step with CtorSpec.eo_extract.construct s16 e_v44 (by rw [he_v44]; rfl) h_a3 h_a3 hinv16 h64 as ⟨v44, s17, hinv17, h_v44⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 dropping he_v44 hinv16 e_v44 s16
  store_step with Store.apply_rep s17 v44 a0 _ _ hinv17 h64 h_v44 h_a0 (by ns_tac) (by ns_tac) as ⟨v45, s18, hinv18, h_v45⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 dropping h_v44 hinv17 s17 v44
  store_step with Store.apply_rep s18 v43 v45 _ _ hinv18 h64 h_v43 h_v45 (by ns_tac) (by ns_tac) as ⟨v46, s19, hinv19, h_v46⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v38 h_v39 h_v40 h_v41 h_v42 dropping h_v43 h_v45 hinv18 s18 v43 v45
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s19 1#u32 (1) (by scalar_tac) hinv19 h64 as ⟨v47, s20, hinv20, h_v47⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v38 h_v39 h_v40 h_v41 h_v42 h_v46 dropping hinv19 s19
  step as ⟨e_v48, he_v48⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s20 e_v48 (by rw [he_v48]; rfl) h_v47 hinv20 h64 as ⟨v48, s21, hinv21, h_v48⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v38 h_v39 h_v40 h_v41 h_v42 h_v46 dropping h_v47 he_v48 hinv20 e_v48 s20 v47
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s21 0#u32 (0) (by scalar_tac) hinv21 h64 as ⟨v49, s22, hinv22, h_v49⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v38 h_v39 h_v40 h_v41 h_v42 h_v46 h_v48 dropping hinv21 s21
  store_step with Store.apply_rep s22 v48 v49 _ _ hinv22 h64 h_v48 h_v49 (by ns_tac) (by ns_tac) as ⟨v50, s23, hinv23, h_v50⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v38 h_v39 h_v40 h_v41 h_v42 h_v46 dropping h_v48 h_v49 hinv22 s22 v48 v49
  store_step with Store.apply_rep s23 v46 v50 _ _ hinv23 h64 h_v46 h_v50 (by ns_tac) (by ns_tac) as ⟨v51, s24, hinv24, h_v51⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v38 h_v39 h_v40 h_v41 h_v42 dropping h_v46 h_v50 hinv23 s23 v46 v50
  store_step with Store.apply_rep s24 v42 v51 _ _ hinv24 h64 h_v42 h_v51 (by ns_tac) (by ns_tac) as ⟨v52, s25, hinv25, h_v52⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v38 h_v39 h_v40 h_v41 dropping h_v42 h_v51 hinv24 s24 v42 v51
  store_step with Store.apply_rep s25 v52 a0 _ _ hinv25 h64 h_v52 h_a0 (by ns_tac) (by ns_tac) as ⟨v53, s26, hinv26, h_v53⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v38 h_v39 h_v40 h_v41 dropping h_v52 hinv25 s25 v52
  step as ⟨e_v54, he_v54⟩
  store_step with CtorSpec.eo_bvneg.construct s26 e_v54 (by rw [he_v54]; exact empty_args) hinv26 h64 as ⟨v54, s27, hinv27, h_v54⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v38 h_v39 h_v40 h_v41 h_v53 dropping he_v54 hinv26 e_v54 s26
  store_step with Store.apply_rep s27 v54 a0 _ _ hinv27 h64 h_v54 h_a0 (by ns_tac) (by ns_tac) as ⟨v55, s28, hinv28, h_v55⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v38 h_v39 h_v40 h_v41 h_v53 dropping h_v54 hinv27 s27 v54
  store_step with Store.apply_rep s28 v53 v55 _ _ hinv28 h64 h_v53 h_v55 (by ns_tac) (by ns_tac) as ⟨v56, s29, hinv29, h_v56⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v38 h_v39 h_v40 h_v41 dropping h_v53 h_v55 hinv28 s28 v53 v55
  store_step with Store.apply_rep s29 v41 v56 _ _ hinv29 h64 h_v41 h_v56 (by ns_tac) (by ns_tac) as ⟨v57, s30, hinv30, h_v57⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v38 h_v39 h_v40 dropping h_v41 h_v56 hinv29 s29 v41 v56
  step as ⟨e_v58, he_v58⟩
  store_step with CtorSpec.eo_ite.construct s30 e_v58 (by rw [he_v58]; exact empty_args) hinv30 h64 as ⟨v58, s31, hinv31, h_v58⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v38 h_v39 h_v40 h_v57 dropping he_v58 hinv30 e_v58 s30
  step as ⟨e_v59, he_v59⟩
  store_step with CtorSpec.eo__3d.construct s31 e_v59 (by rw [he_v59]; exact empty_args) hinv31 h64 as ⟨v59, s32, hinv32, h_v59⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v38 h_v39 h_v40 h_v57 h_v58 dropping he_v59 hinv31 e_v59 s31
  step as ⟨e_v60, he_v60⟩
  store_step with CtorSpec.eo_extract.construct s32 e_v60 (by rw [he_v60]; rfl) h_a3 h_a3 hinv32 h64 as ⟨v60, s33, hinv33, h_v60⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v38 h_v39 h_v40 h_v57 h_v58 h_v59 dropping he_v60 hinv32 e_v60 s32
  store_step with Store.apply_rep s33 v60 a1 _ _ hinv33 h64 h_v60 h_a1 (by ns_tac) (by ns_tac) as ⟨v61, s34, hinv34, h_v61⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v38 h_v39 h_v40 h_v57 h_v58 h_v59 dropping h_v60 hinv33 s33 v60
  store_step with Store.apply_rep s34 v59 v61 _ _ hinv34 h64 h_v59 h_v61 (by ns_tac) (by ns_tac) as ⟨v62, s35, hinv35, h_v62⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v38 h_v39 h_v40 h_v57 h_v58 dropping h_v59 h_v61 hinv34 s34 v59 v61
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s35 1#u32 (1) (by scalar_tac) hinv35 h64 as ⟨v63, s36, hinv36, h_v63⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v38 h_v39 h_v40 h_v57 h_v58 h_v62 dropping hinv35 s35
  step as ⟨e_v64, he_v64⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s36 e_v64 (by rw [he_v64]; rfl) h_v63 hinv36 h64 as ⟨v64, s37, hinv37, h_v64⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v38 h_v39 h_v40 h_v57 h_v58 h_v62 dropping h_v63 he_v64 hinv36 e_v64 s36 v63
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s37 0#u32 (0) (by scalar_tac) hinv37 h64 as ⟨v65, s38, hinv38, h_v65⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v38 h_v39 h_v40 h_v57 h_v58 h_v62 h_v64 dropping hinv37 s37
  store_step with Store.apply_rep s38 v64 v65 _ _ hinv38 h64 h_v64 h_v65 (by ns_tac) (by ns_tac) as ⟨v66, s39, hinv39, h_v66⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v38 h_v39 h_v40 h_v57 h_v58 h_v62 dropping h_v64 h_v65 hinv38 s38 v64 v65
  store_step with Store.apply_rep s39 v62 v66 _ _ hinv39 h64 h_v62 h_v66 (by ns_tac) (by ns_tac) as ⟨v67, s40, hinv40, h_v67⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v38 h_v39 h_v40 h_v57 h_v58 dropping h_v62 h_v66 hinv39 s39 v62 v66
  store_step with Store.apply_rep s40 v58 v67 _ _ hinv40 h64 h_v58 h_v67 (by ns_tac) (by ns_tac) as ⟨v68, s41, hinv41, h_v68⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v38 h_v39 h_v40 h_v57 dropping h_v58 h_v67 hinv40 s40 v58 v67
  store_step with Store.apply_rep s41 v68 a1 _ _ hinv41 h64 h_v68 h_a1 (by ns_tac) (by ns_tac) as ⟨v69, s42, hinv42, h_v69⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v38 h_v39 h_v40 h_v57 dropping h_v68 hinv41 s41 v68
  step as ⟨e_v70, he_v70⟩
  store_step with CtorSpec.eo_bvneg.construct s42 e_v70 (by rw [he_v70]; exact empty_args) hinv42 h64 as ⟨v70, s43, hinv43, h_v70⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v38 h_v39 h_v40 h_v57 h_v69 dropping he_v70 hinv42 e_v70 s42
  store_step with Store.apply_rep s43 v70 a1 _ _ hinv43 h64 h_v70 h_a1 (by ns_tac) (by ns_tac) as ⟨v71, s44, hinv44, h_v71⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v38 h_v39 h_v40 h_v57 h_v69 dropping h_v70 hinv43 s43 v70
  store_step with Store.apply_rep s44 v69 v71 _ _ hinv44 h64 h_v69 h_v71 (by ns_tac) (by ns_tac) as ⟨v72, s45, hinv45, h_v72⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v38 h_v39 h_v40 h_v57 dropping h_v69 h_v71 hinv44 s44 v69 v71
  store_step with Store.apply_rep s45 v57 v72 _ _ hinv45 h64 h_v57 h_v72 (by ns_tac) (by ns_tac) as ⟨v73, s46, hinv46, h_v73⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v38 h_v39 h_v40 dropping h_v57 h_v72 hinv45 s45 v57 v72
  store_step with Store.apply_rep s46 v40 v73 _ _ hinv46 h64 h_v40 h_v73 (by ns_tac) (by ns_tac) as ⟨v74, s47, hinv47, h_v74⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v38 h_v39 dropping h_v40 h_v73 hinv46 s46 v40 v73
  step as ⟨e_v75, he_v75⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s47 e_v75 (by rw [he_v75]; rfl) h_a2 hinv47 h64 as ⟨v75, s48, hinv48, h_v75⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v39 h_v74 dropping h_a2 he_v75 hinv47 e_v75 s47
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s48 0#u32 (0) (by scalar_tac) hinv48 h64 as ⟨v76, s49, hinv49, h_v76⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v39 h_v74 h_v75 dropping hinv48 s48
  store_step with Store.apply_rep s49 v75 v76 _ _ hinv49 h64 h_v75 h_v76 (by ns_tac) (by ns_tac) as ⟨v77, s50, hinv50, h_v77⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v39 h_v74 dropping h_v75 h_v76 hinv49 s49 v75 v76
  store_step with Store.apply_rep s50 v74 v77 _ _ hinv50 h64 h_v74 h_v77 (by ns_tac) (by ns_tac) as ⟨v78, s51, hinv51, h_v78⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v39 dropping h_v74 h_v77 hinv50 s50 v74 v77
  store_step with Store.apply_rep s51 v39 v78 _ _ hinv51 h64 h_v39 h_v78 (by ns_tac) (by ns_tac) as ⟨v79, s52, hinv52, h_v79⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 dropping h_v39 h_v78 hinv51 s51 v39 v78
  step as ⟨e_v80, he_v80⟩
  store_step with CtorSpec.eo_bvurem.construct s52 e_v80 (by rw [he_v80]; exact empty_args) hinv52 h64 as ⟨v80, s53, hinv53, h_v80⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v79 dropping he_v80 hinv52 e_v80 s52
  step as ⟨e_v81, he_v81⟩
  store_step with CtorSpec.eo_ite.construct s53 e_v81 (by rw [he_v81]; exact empty_args) hinv53 h64 as ⟨v81, s54, hinv54, h_v81⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v79 h_v80 dropping he_v81 hinv53 e_v81 s53
  step as ⟨e_v82, he_v82⟩
  store_step with CtorSpec.eo__3d.construct s54 e_v82 (by rw [he_v82]; exact empty_args) hinv54 h64 as ⟨v82, s55, hinv55, h_v82⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v79 h_v80 h_v81 dropping he_v82 hinv54 e_v82 s54
  step as ⟨e_v83, he_v83⟩
  store_step with CtorSpec.eo_extract.construct s55 e_v83 (by rw [he_v83]; rfl) h_a3 h_a3 hinv55 h64 as ⟨v83, s56, hinv56, h_v83⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v79 h_v80 h_v81 h_v82 dropping he_v83 hinv55 e_v83 s55
  store_step with Store.apply_rep s56 v83 a0 _ _ hinv56 h64 h_v83 h_a0 (by ns_tac) (by ns_tac) as ⟨v84, s57, hinv57, h_v84⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v79 h_v80 h_v81 h_v82 dropping h_v83 hinv56 s56 v83
  store_step with Store.apply_rep s57 v82 v84 _ _ hinv57 h64 h_v82 h_v84 (by ns_tac) (by ns_tac) as ⟨v85, s58, hinv58, h_v85⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v79 h_v80 h_v81 dropping h_v82 h_v84 hinv57 s57 v82 v84
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s58 1#u32 (1) (by scalar_tac) hinv58 h64 as ⟨v86, s59, hinv59, h_v86⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v79 h_v80 h_v81 h_v85 dropping hinv58 s58
  step as ⟨e_v87, he_v87⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s59 e_v87 (by rw [he_v87]; rfl) h_v86 hinv59 h64 as ⟨v87, s60, hinv60, h_v87⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v79 h_v80 h_v81 h_v85 dropping h_v86 he_v87 hinv59 e_v87 s59 v86
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s60 0#u32 (0) (by scalar_tac) hinv60 h64 as ⟨v88, s61, hinv61, h_v88⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v79 h_v80 h_v81 h_v85 h_v87 dropping hinv60 s60
  store_step with Store.apply_rep s61 v87 v88 _ _ hinv61 h64 h_v87 h_v88 (by ns_tac) (by ns_tac) as ⟨v89, s62, hinv62, h_v89⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v79 h_v80 h_v81 h_v85 dropping h_v87 h_v88 hinv61 s61 v87 v88
  store_step with Store.apply_rep s62 v85 v89 _ _ hinv62 h64 h_v85 h_v89 (by ns_tac) (by ns_tac) as ⟨v90, s63, hinv63, h_v90⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v79 h_v80 h_v81 dropping h_v85 h_v89 hinv62 s62 v85 v89
  store_step with Store.apply_rep s63 v81 v90 _ _ hinv63 h64 h_v81 h_v90 (by ns_tac) (by ns_tac) as ⟨v91, s64, hinv64, h_v91⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v79 h_v80 dropping h_v81 h_v90 hinv63 s63 v81 v90
  store_step with Store.apply_rep s64 v91 a0 _ _ hinv64 h64 h_v91 h_a0 (by ns_tac) (by ns_tac) as ⟨v92, s65, hinv65, h_v92⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v79 h_v80 dropping h_v91 hinv64 s64 v91
  step as ⟨e_v93, he_v93⟩
  store_step with CtorSpec.eo_bvneg.construct s65 e_v93 (by rw [he_v93]; exact empty_args) hinv65 h64 as ⟨v93, s66, hinv66, h_v93⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v79 h_v80 h_v92 dropping he_v93 hinv65 e_v93 s65
  store_step with Store.apply_rep s66 v93 a0 _ _ hinv66 h64 h_v93 h_a0 (by ns_tac) (by ns_tac) as ⟨v94, s67, hinv67, h_v94⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v79 h_v80 h_v92 dropping h_v93 hinv66 s66 v93
  store_step with Store.apply_rep s67 v92 v94 _ _ hinv67 h64 h_v92 h_v94 (by ns_tac) (by ns_tac) as ⟨v95, s68, hinv68, h_v95⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v79 h_v80 dropping h_v92 h_v94 hinv67 s67 v92 v94
  store_step with Store.apply_rep s68 v80 v95 _ _ hinv68 h64 h_v80 h_v95 (by ns_tac) (by ns_tac) as ⟨v96, s69, hinv69, h_v96⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v79 dropping h_v80 h_v95 hinv68 s68 v80 v95
  step as ⟨e_v97, he_v97⟩
  store_step with CtorSpec.eo_ite.construct s69 e_v97 (by rw [he_v97]; exact empty_args) hinv69 h64 as ⟨v97, s70, hinv70, h_v97⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v79 h_v96 dropping he_v97 hinv69 e_v97 s69
  step as ⟨e_v98, he_v98⟩
  store_step with CtorSpec.eo__3d.construct s70 e_v98 (by rw [he_v98]; exact empty_args) hinv70 h64 as ⟨v98, s71, hinv71, h_v98⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v79 h_v96 h_v97 dropping he_v98 hinv70 e_v98 s70
  step as ⟨e_v99, he_v99⟩
  store_step with CtorSpec.eo_extract.construct s71 e_v99 (by rw [he_v99]; rfl) h_a3 h_a3 hinv71 h64 as ⟨v99, s72, hinv72, h_v99⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v79 h_v96 h_v97 h_v98 dropping he_v99 hinv71 e_v99 s71
  store_step with Store.apply_rep s72 v99 a1 _ _ hinv72 h64 h_v99 h_a1 (by ns_tac) (by ns_tac) as ⟨v100, s73, hinv73, h_v100⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v79 h_v96 h_v97 h_v98 dropping h_v99 hinv72 s72 v99
  store_step with Store.apply_rep s73 v98 v100 _ _ hinv73 h64 h_v98 h_v100 (by ns_tac) (by ns_tac) as ⟨v101, s74, hinv74, h_v101⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v79 h_v96 h_v97 dropping h_v100 h_v98 hinv73 s73 v100 v98
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s74 1#u32 (1) (by scalar_tac) hinv74 h64 as ⟨v102, s75, hinv75, h_v102⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v79 h_v96 h_v97 h_v101 dropping hinv74 s74
  step as ⟨e_v103, he_v103⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s75 e_v103 (by rw [he_v103]; rfl) h_v102 hinv75 h64 as ⟨v103, s76, hinv76, h_v103⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v79 h_v96 h_v97 h_v101 dropping h_v102 he_v103 hinv75 e_v103 s75 v102
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s76 0#u32 (0) (by scalar_tac) hinv76 h64 as ⟨v104, s77, hinv77, h_v104⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v79 h_v96 h_v97 h_v101 h_v103 dropping hinv76 s76
  store_step with Store.apply_rep s77 v103 v104 _ _ hinv77 h64 h_v103 h_v104 (by ns_tac) (by ns_tac) as ⟨v105, s78, hinv78, h_v105⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v79 h_v96 h_v97 h_v101 dropping h_v103 h_v104 hinv77 s77 v103 v104
  store_step with Store.apply_rep s78 v101 v105 _ _ hinv78 h64 h_v101 h_v105 (by ns_tac) (by ns_tac) as ⟨v106, s79, hinv79, h_v106⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v79 h_v96 h_v97 dropping h_v101 h_v105 hinv78 s78 v101 v105
  store_step with Store.apply_rep s79 v97 v106 _ _ hinv79 h64 h_v97 h_v106 (by ns_tac) (by ns_tac) as ⟨v107, s80, hinv80, h_v107⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v79 h_v96 dropping h_v106 h_v97 hinv79 s79 v106 v97
  store_step with Store.apply_rep s80 v107 a1 _ _ hinv80 h64 h_v107 h_a1 (by ns_tac) (by ns_tac) as ⟨v108, s81, hinv81, h_v108⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v79 h_v96 dropping h_v107 hinv80 s80 v107
  step as ⟨e_v109, he_v109⟩
  store_step with CtorSpec.eo_bvneg.construct s81 e_v109 (by rw [he_v109]; exact empty_args) hinv81 h64 as ⟨v109, s82, hinv82, h_v109⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v79 h_v96 h_v108 dropping he_v109 hinv81 e_v109 s81
  store_step with Store.apply_rep s82 v109 a1 _ _ hinv82 h64 h_v109 h_a1 (by ns_tac) (by ns_tac) as ⟨v110, s83, hinv83, h_v110⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v79 h_v96 h_v108 dropping h_v109 hinv82 s82 v109
  store_step with Store.apply_rep s83 v108 v110 _ _ hinv83 h64 h_v108 h_v110 (by ns_tac) (by ns_tac) as ⟨v111, s84, hinv84, h_v111⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v79 h_v96 dropping h_v108 h_v110 hinv83 s83 v108 v110
  store_step with Store.apply_rep s84 v96 v111 _ _ hinv84 h64 h_v96 h_v111 (by ns_tac) (by ns_tac) as ⟨v112, s85, hinv85, h_v112⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v79 dropping h_v111 h_v96 hinv84 s84 v111 v96
  store_step with Store.apply_rep s85 v79 v112 _ _ hinv85 h64 h_v79 h_v112 (by ns_tac) (by ns_tac) as ⟨v113, s86, hinv86, h_v113⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 dropping h_v112 h_v79 hinv85 s85 v112 v79
  step as ⟨e_v114, he_v114⟩
  store_step with CtorSpec.eo_ite.construct s86 e_v114 (by rw [he_v114]; exact empty_args) hinv86 h64 as ⟨v114, s87, hinv87, h_v114⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 dropping he_v114 hinv86 e_v114 s86
  step as ⟨e_v115, he_v115⟩
  store_step with CtorSpec.eo_and.construct s87 e_v115 (by rw [he_v115]; exact empty_args) hinv87 h64 as ⟨v115, s88, hinv88, h_v115⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v114 dropping he_v115 hinv87 e_v115 s87
  step as ⟨e_v116, he_v116⟩
  store_step with CtorSpec.eo__3d.construct s88 e_v116 (by rw [he_v116]; exact empty_args) hinv88 h64 as ⟨v116, s89, hinv89, h_v116⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v114 h_v115 dropping he_v116 hinv88 e_v116 s88
  step as ⟨e_v117, he_v117⟩
  store_step with CtorSpec.eo_extract.construct s89 e_v117 (by rw [he_v117]; rfl) h_a3 h_a3 hinv89 h64 as ⟨v117, s90, hinv90, h_v117⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v114 h_v115 h_v116 dropping he_v117 hinv89 e_v117 s89
  store_step with Store.apply_rep s90 v117 a0 _ _ hinv90 h64 h_v117 h_a0 (by ns_tac) (by ns_tac) as ⟨v118, s91, hinv91, h_v118⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v114 h_v115 h_v116 dropping h_v117 hinv90 s90 v117
  store_step with Store.apply_rep s91 v116 v118 _ _ hinv91 h64 h_v116 h_v118 (by ns_tac) (by ns_tac) as ⟨v119, s92, hinv92, h_v119⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v114 h_v115 dropping h_v116 h_v118 hinv91 s91 v116 v118
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s92 1#u32 (1) (by scalar_tac) hinv92 h64 as ⟨v120, s93, hinv93, h_v120⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v114 h_v115 h_v119 dropping hinv92 s92
  step as ⟨e_v121, he_v121⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s93 e_v121 (by rw [he_v121]; rfl) h_v120 hinv93 h64 as ⟨v121, s94, hinv94, h_v121⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v114 h_v115 h_v119 dropping h_v120 he_v121 hinv93 e_v121 s93 v120
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s94 0#u32 (0) (by scalar_tac) hinv94 h64 as ⟨v122, s95, hinv95, h_v122⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v114 h_v115 h_v119 h_v121 dropping hinv94 s94
  store_step with Store.apply_rep s95 v121 v122 _ _ hinv95 h64 h_v121 h_v122 (by ns_tac) (by ns_tac) as ⟨v123, s96, hinv96, h_v123⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v114 h_v115 h_v119 dropping h_v121 h_v122 hinv95 s95 v121 v122
  store_step with Store.apply_rep s96 v119 v123 _ _ hinv96 h64 h_v119 h_v123 (by ns_tac) (by ns_tac) as ⟨v124, s97, hinv97, h_v124⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v114 h_v115 dropping h_v119 h_v123 hinv96 s96 v119 v123
  store_step with Store.apply_rep s97 v115 v124 _ _ hinv97 h64 h_v115 h_v124 (by ns_tac) (by ns_tac) as ⟨v125, s98, hinv98, h_v125⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v114 dropping h_v115 h_v124 hinv97 s97 v115 v124
  step as ⟨e_v126, he_v126⟩
  store_step with CtorSpec.eo_and.construct s98 e_v126 (by rw [he_v126]; exact empty_args) hinv98 h64 as ⟨v126, s99, hinv99, h_v126⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v114 h_v125 dropping he_v126 hinv98 e_v126 s98
  step as ⟨e_v127, he_v127⟩
  store_step with CtorSpec.eo__3d.construct s99 e_v127 (by rw [he_v127]; exact empty_args) hinv99 h64 as ⟨v127, s100, hinv100, h_v127⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v114 h_v125 h_v126 dropping he_v127 hinv99 e_v127 s99
  step as ⟨e_v128, he_v128⟩
  store_step with CtorSpec.eo_extract.construct s100 e_v128 (by rw [he_v128]; rfl) h_a3 h_a3 hinv100 h64 as ⟨v128, s101, hinv101, h_v128⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v114 h_v125 h_v126 h_v127 dropping he_v128 hinv100 e_v128 s100
  store_step with Store.apply_rep s101 v128 a1 _ _ hinv101 h64 h_v128 h_a1 (by ns_tac) (by ns_tac) as ⟨v129, s102, hinv102, h_v129⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v114 h_v125 h_v126 h_v127 dropping h_v128 hinv101 s101 v128
  store_step with Store.apply_rep s102 v127 v129 _ _ hinv102 h64 h_v127 h_v129 (by ns_tac) (by ns_tac) as ⟨v130, s103, hinv103, h_v130⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v114 h_v125 h_v126 dropping h_v127 h_v129 hinv102 s102 v127 v129
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s103 1#u32 (1) (by scalar_tac) hinv103 h64 as ⟨v131, s104, hinv104, h_v131⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v114 h_v125 h_v126 h_v130 dropping hinv103 s103
  step as ⟨e_v132, he_v132⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s104 e_v132 (by rw [he_v132]; rfl) h_v131 hinv104 h64 as ⟨v132, s105, hinv105, h_v132⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v114 h_v125 h_v126 h_v130 dropping h_v131 he_v132 hinv104 e_v132 s104 v131
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s105 0#u32 (0) (by scalar_tac) hinv105 h64 as ⟨v133, s106, hinv106, h_v133⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v114 h_v125 h_v126 h_v130 h_v132 dropping hinv105 s105
  store_step with Store.apply_rep s106 v132 v133 _ _ hinv106 h64 h_v132 h_v133 (by ns_tac) (by ns_tac) as ⟨v134, s107, hinv107, h_v134⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v114 h_v125 h_v126 h_v130 dropping h_v132 h_v133 hinv106 s106 v132 v133
  store_step with Store.apply_rep s107 v130 v134 _ _ hinv107 h64 h_v130 h_v134 (by ns_tac) (by ns_tac) as ⟨v135, s108, hinv108, h_v135⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v114 h_v125 h_v126 dropping h_v130 h_v134 hinv107 s107 v130 v134
  store_step with Store.apply_rep s108 v126 v135 _ _ hinv108 h64 h_v126 h_v135 (by ns_tac) (by ns_tac) as ⟨v136, s109, hinv109, h_v136⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v114 h_v125 dropping h_v126 h_v135 hinv108 s108 v126 v135
  store_step with Store.literal_boolean_spec s109 true hinv109 h64 as ⟨v137, s110, hinv110, h_v137⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v114 h_v125 h_v136 dropping hinv109 s109
  store_step with Store.apply_rep s110 v136 v137 _ _ hinv110 h64 h_v136 h_v137 (by ns_tac) (by ns_tac) as ⟨v138, s111, hinv111, h_v138⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v114 h_v125 dropping h_v136 h_v137 hinv110 s110 v136 v137
  store_step with Store.apply_rep s111 v125 v138 _ _ hinv111 h64 h_v125 h_v138 (by ns_tac) (by ns_tac) as ⟨v139, s112, hinv112, h_v139⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v114 dropping h_v125 h_v138 hinv111 s111 v125 v138
  store_step with Store.apply_rep s112 v114 v139 _ _ hinv112 h64 h_v114 h_v139 (by ns_tac) (by ns_tac) as ⟨v140, s113, hinv113, h_v140⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 dropping h_v114 h_v139 hinv112 s112 v114 v139
  step as ⟨e_v141, he_v141⟩
  store_step with CtorSpec.eo_bvurem.construct s113 e_v141 (by rw [he_v141]; exact empty_args) hinv113 h64 as ⟨v141, s114, hinv114, h_v141⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v140 dropping he_v141 hinv113 e_v141 s113
  step as ⟨e_v142, he_v142⟩
  store_step with CtorSpec.eo_ite.construct s114 e_v142 (by rw [he_v142]; exact empty_args) hinv114 h64 as ⟨v142, s115, hinv115, h_v142⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v140 h_v141 dropping he_v142 hinv114 e_v142 s114
  step as ⟨e_v143, he_v143⟩
  store_step with CtorSpec.eo__3d.construct s115 e_v143 (by rw [he_v143]; exact empty_args) hinv115 h64 as ⟨v143, s116, hinv116, h_v143⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v140 h_v141 h_v142 dropping he_v143 hinv115 e_v143 s115
  step as ⟨e_v144, he_v144⟩
  store_step with CtorSpec.eo_extract.construct s116 e_v144 (by rw [he_v144]; rfl) h_a3 h_a3 hinv116 h64 as ⟨v144, s117, hinv117, h_v144⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v140 h_v141 h_v142 h_v143 dropping he_v144 hinv116 e_v144 s116
  store_step with Store.apply_rep s117 v144 a0 _ _ hinv117 h64 h_v144 h_a0 (by ns_tac) (by ns_tac) as ⟨v145, s118, hinv118, h_v145⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v140 h_v141 h_v142 h_v143 dropping h_v144 hinv117 s117 v144
  store_step with Store.apply_rep s118 v143 v145 _ _ hinv118 h64 h_v143 h_v145 (by ns_tac) (by ns_tac) as ⟨v146, s119, hinv119, h_v146⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v140 h_v141 h_v142 dropping h_v143 h_v145 hinv118 s118 v143 v145
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s119 1#u32 (1) (by scalar_tac) hinv119 h64 as ⟨v147, s120, hinv120, h_v147⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v140 h_v141 h_v142 h_v146 dropping hinv119 s119
  step as ⟨e_v148, he_v148⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s120 e_v148 (by rw [he_v148]; rfl) h_v147 hinv120 h64 as ⟨v148, s121, hinv121, h_v148⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v140 h_v141 h_v142 h_v146 dropping h_v147 he_v148 hinv120 e_v148 s120 v147
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s121 0#u32 (0) (by scalar_tac) hinv121 h64 as ⟨v149, s122, hinv122, h_v149⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v140 h_v141 h_v142 h_v146 h_v148 dropping hinv121 s121
  store_step with Store.apply_rep s122 v148 v149 _ _ hinv122 h64 h_v148 h_v149 (by ns_tac) (by ns_tac) as ⟨v150, s123, hinv123, h_v150⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v140 h_v141 h_v142 h_v146 dropping h_v148 h_v149 hinv122 s122 v148 v149
  store_step with Store.apply_rep s123 v146 v150 _ _ hinv123 h64 h_v146 h_v150 (by ns_tac) (by ns_tac) as ⟨v151, s124, hinv124, h_v151⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v140 h_v141 h_v142 dropping h_v146 h_v150 hinv123 s123 v146 v150
  store_step with Store.apply_rep s124 v142 v151 _ _ hinv124 h64 h_v142 h_v151 (by ns_tac) (by ns_tac) as ⟨v152, s125, hinv125, h_v152⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v140 h_v141 dropping h_v142 h_v151 hinv124 s124 v142 v151
  store_step with Store.apply_rep s125 v152 a0 _ _ hinv125 h64 h_v152 h_a0 (by ns_tac) (by ns_tac) as ⟨v153, s126, hinv126, h_v153⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v140 h_v141 dropping h_v152 hinv125 s125 v152
  step as ⟨e_v154, he_v154⟩
  store_step with CtorSpec.eo_bvneg.construct s126 e_v154 (by rw [he_v154]; exact empty_args) hinv126 h64 as ⟨v154, s127, hinv127, h_v154⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v140 h_v141 h_v153 dropping he_v154 hinv126 e_v154 s126
  store_step with Store.apply_rep s127 v154 a0 _ _ hinv127 h64 h_v154 h_a0 (by ns_tac) (by ns_tac) as ⟨v155, s128, hinv128, h_v155⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v140 h_v141 h_v153 dropping h_v154 hinv127 s127 v154
  store_step with Store.apply_rep s128 v153 v155 _ _ hinv128 h64 h_v153 h_v155 (by ns_tac) (by ns_tac) as ⟨v156, s129, hinv129, h_v156⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v140 h_v141 dropping h_v153 h_v155 hinv128 s128 v153 v155
  store_step with Store.apply_rep s129 v141 v156 _ _ hinv129 h64 h_v141 h_v156 (by ns_tac) (by ns_tac) as ⟨v157, s130, hinv130, h_v157⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v140 dropping h_v141 h_v156 hinv129 s129 v141 v156
  step as ⟨e_v158, he_v158⟩
  store_step with CtorSpec.eo_ite.construct s130 e_v158 (by rw [he_v158]; exact empty_args) hinv130 h64 as ⟨v158, s131, hinv131, h_v158⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v140 h_v157 dropping he_v158 hinv130 e_v158 s130
  step as ⟨e_v159, he_v159⟩
  store_step with CtorSpec.eo__3d.construct s131 e_v159 (by rw [he_v159]; exact empty_args) hinv131 h64 as ⟨v159, s132, hinv132, h_v159⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v140 h_v157 h_v158 dropping he_v159 hinv131 e_v159 s131
  step as ⟨e_v160, he_v160⟩
  store_step with CtorSpec.eo_extract.construct s132 e_v160 (by rw [he_v160]; rfl) h_a3 h_a3 hinv132 h64 as ⟨v160, s133, hinv133, h_v160⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v140 h_v157 h_v158 h_v159 dropping he_v160 hinv132 e_v160 s132
  store_step with Store.apply_rep s133 v160 a1 _ _ hinv133 h64 h_v160 h_a1 (by ns_tac) (by ns_tac) as ⟨v161, s134, hinv134, h_v161⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v140 h_v157 h_v158 h_v159 dropping h_v160 hinv133 s133 v160
  store_step with Store.apply_rep s134 v159 v161 _ _ hinv134 h64 h_v159 h_v161 (by ns_tac) (by ns_tac) as ⟨v162, s135, hinv135, h_v162⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v140 h_v157 h_v158 dropping h_v159 h_v161 hinv134 s134 v159 v161
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s135 1#u32 (1) (by scalar_tac) hinv135 h64 as ⟨v163, s136, hinv136, h_v163⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v140 h_v157 h_v158 h_v162 dropping hinv135 s135
  step as ⟨e_v164, he_v164⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s136 e_v164 (by rw [he_v164]; rfl) h_v163 hinv136 h64 as ⟨v164, s137, hinv137, h_v164⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v140 h_v157 h_v158 h_v162 dropping h_v163 he_v164 hinv136 e_v164 s136 v163
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s137 0#u32 (0) (by scalar_tac) hinv137 h64 as ⟨v165, s138, hinv138, h_v165⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v140 h_v157 h_v158 h_v162 h_v164 dropping hinv137 s137
  store_step with Store.apply_rep s138 v164 v165 _ _ hinv138 h64 h_v164 h_v165 (by ns_tac) (by ns_tac) as ⟨v166, s139, hinv139, h_v166⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v140 h_v157 h_v158 h_v162 dropping h_v164 h_v165 hinv138 s138 v164 v165
  store_step with Store.apply_rep s139 v162 v166 _ _ hinv139 h64 h_v162 h_v166 (by ns_tac) (by ns_tac) as ⟨v167, s140, hinv140, h_v167⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v140 h_v157 h_v158 dropping h_v162 h_v166 hinv139 s139 v162 v166
  store_step with Store.apply_rep s140 v158 v167 _ _ hinv140 h64 h_v158 h_v167 (by ns_tac) (by ns_tac) as ⟨v168, s141, hinv141, h_v168⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v140 h_v157 dropping h_v158 h_v167 hinv140 s140 v158 v167
  store_step with Store.apply_rep s141 v168 a1 _ _ hinv141 h64 h_v168 h_a1 (by ns_tac) (by ns_tac) as ⟨v169, s142, hinv142, h_v169⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v140 h_v157 dropping h_v168 hinv141 s141 v168
  step as ⟨e_v170, he_v170⟩
  store_step with CtorSpec.eo_bvneg.construct s142 e_v170 (by rw [he_v170]; exact empty_args) hinv142 h64 as ⟨v170, s143, hinv143, h_v170⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v140 h_v157 h_v169 dropping he_v170 hinv142 e_v170 s142
  store_step with Store.apply_rep s143 v170 a1 _ _ hinv143 h64 h_v170 h_a1 (by ns_tac) (by ns_tac) as ⟨v171, s144, hinv144, h_v171⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v140 h_v157 h_v169 dropping h_v170 hinv143 s143 v170
  store_step with Store.apply_rep s144 v169 v171 _ _ hinv144 h64 h_v169 h_v171 (by ns_tac) (by ns_tac) as ⟨v172, s145, hinv145, h_v172⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v140 h_v157 dropping h_v169 h_v171 hinv144 s144 v169 v171
  store_step with Store.apply_rep s145 v157 v172 _ _ hinv145 h64 h_v157 h_v172 (by ns_tac) (by ns_tac) as ⟨v173, s146, hinv146, h_v173⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v140 dropping h_v157 h_v172 hinv145 s145 v157 v172
  store_step with Store.apply_rep s146 v140 v173 _ _ hinv146 h64 h_v140 h_v173 (by ns_tac) (by ns_tac) as ⟨v174, s147, hinv147, h_v174⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 dropping h_v140 h_v173 hinv146 s146 v140 v173
  step as ⟨e_v175, he_v175⟩
  store_step with CtorSpec.eo_ite.construct s147 e_v175 (by rw [he_v175]; exact empty_args) hinv147 h64 as ⟨v175, s148, hinv148, h_v175⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 dropping he_v175 hinv147 e_v175 s147
  step as ⟨e_v176, he_v176⟩
  store_step with CtorSpec.eo_and.construct s148 e_v176 (by rw [he_v176]; exact empty_args) hinv148 h64 as ⟨v176, s149, hinv149, h_v176⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v175 dropping he_v176 hinv148 e_v176 s148
  step as ⟨e_v177, he_v177⟩
  store_step with CtorSpec.eo__3d.construct s149 e_v177 (by rw [he_v177]; exact empty_args) hinv149 h64 as ⟨v177, s150, hinv150, h_v177⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v175 h_v176 dropping he_v177 hinv149 e_v177 s149
  step as ⟨e_v178, he_v178⟩
  store_step with CtorSpec.eo_extract.construct s150 e_v178 (by rw [he_v178]; rfl) h_a3 h_a3 hinv150 h64 as ⟨v178, s151, hinv151, h_v178⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v175 h_v176 h_v177 dropping he_v178 hinv150 e_v178 s150
  store_step with Store.apply_rep s151 v178 a0 _ _ hinv151 h64 h_v178 h_a0 (by ns_tac) (by ns_tac) as ⟨v179, s152, hinv152, h_v179⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v175 h_v176 h_v177 dropping h_v178 hinv151 s151 v178
  store_step with Store.apply_rep s152 v177 v179 _ _ hinv152 h64 h_v177 h_v179 (by ns_tac) (by ns_tac) as ⟨v180, s153, hinv153, h_v180⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v175 h_v176 dropping h_v177 h_v179 hinv152 s152 v177 v179
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s153 1#u32 (1) (by scalar_tac) hinv153 h64 as ⟨v181, s154, hinv154, h_v181⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v175 h_v176 h_v180 dropping hinv153 s153
  step as ⟨e_v182, he_v182⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s154 e_v182 (by rw [he_v182]; rfl) h_v181 hinv154 h64 as ⟨v182, s155, hinv155, h_v182⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v175 h_v176 h_v180 dropping h_v181 he_v182 hinv154 e_v182 s154 v181
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s155 1#u32 (1) (by scalar_tac) hinv155 h64 as ⟨v183, s156, hinv156, h_v183⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v175 h_v176 h_v180 h_v182 dropping hinv155 s155
  store_step with Store.apply_rep s156 v182 v183 _ _ hinv156 h64 h_v182 h_v183 (by ns_tac) (by ns_tac) as ⟨v184, s157, hinv157, h_v184⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v175 h_v176 h_v180 dropping h_v182 h_v183 hinv156 s156 v182 v183
  store_step with Store.apply_rep s157 v180 v184 _ _ hinv157 h64 h_v180 h_v184 (by ns_tac) (by ns_tac) as ⟨v185, s158, hinv158, h_v185⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v175 h_v176 dropping h_v180 h_v184 hinv157 s157 v180 v184
  store_step with Store.apply_rep s158 v176 v185 _ _ hinv158 h64 h_v176 h_v185 (by ns_tac) (by ns_tac) as ⟨v186, s159, hinv159, h_v186⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v175 dropping h_v176 h_v185 hinv158 s158 v176 v185
  step as ⟨e_v187, he_v187⟩
  store_step with CtorSpec.eo_and.construct s159 e_v187 (by rw [he_v187]; exact empty_args) hinv159 h64 as ⟨v187, s160, hinv160, h_v187⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v175 h_v186 dropping he_v187 hinv159 e_v187 s159
  step as ⟨e_v188, he_v188⟩
  store_step with CtorSpec.eo__3d.construct s160 e_v188 (by rw [he_v188]; exact empty_args) hinv160 h64 as ⟨v188, s161, hinv161, h_v188⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v175 h_v186 h_v187 dropping he_v188 hinv160 e_v188 s160
  step as ⟨e_v189, he_v189⟩
  store_step with CtorSpec.eo_extract.construct s161 e_v189 (by rw [he_v189]; rfl) h_a3 h_a3 hinv161 h64 as ⟨v189, s162, hinv162, h_v189⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v175 h_v186 h_v187 h_v188 dropping he_v189 hinv161 e_v189 s161
  store_step with Store.apply_rep s162 v189 a1 _ _ hinv162 h64 h_v189 h_a1 (by ns_tac) (by ns_tac) as ⟨v190, s163, hinv163, h_v190⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v175 h_v186 h_v187 h_v188 dropping h_v189 hinv162 s162 v189
  store_step with Store.apply_rep s163 v188 v190 _ _ hinv163 h64 h_v188 h_v190 (by ns_tac) (by ns_tac) as ⟨v191, s164, hinv164, h_v191⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v175 h_v186 h_v187 dropping h_v188 h_v190 hinv163 s163 v188 v190
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s164 1#u32 (1) (by scalar_tac) hinv164 h64 as ⟨v192, s165, hinv165, h_v192⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v175 h_v186 h_v187 h_v191 dropping hinv164 s164
  step as ⟨e_v193, he_v193⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s165 e_v193 (by rw [he_v193]; rfl) h_v192 hinv165 h64 as ⟨v193, s166, hinv166, h_v193⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v175 h_v186 h_v187 h_v191 dropping h_v192 he_v193 hinv165 e_v193 s165 v192
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s166 0#u32 (0) (by scalar_tac) hinv166 h64 as ⟨v194, s167, hinv167, h_v194⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v175 h_v186 h_v187 h_v191 h_v193 dropping hinv166 s166
  store_step with Store.apply_rep s167 v193 v194 _ _ hinv167 h64 h_v193 h_v194 (by ns_tac) (by ns_tac) as ⟨v195, s168, hinv168, h_v195⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v175 h_v186 h_v187 h_v191 dropping h_v193 h_v194 hinv167 s167 v193 v194
  store_step with Store.apply_rep s168 v191 v195 _ _ hinv168 h64 h_v191 h_v195 (by ns_tac) (by ns_tac) as ⟨v196, s169, hinv169, h_v196⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v175 h_v186 h_v187 dropping h_v191 h_v195 hinv168 s168 v191 v195
  store_step with Store.apply_rep s169 v187 v196 _ _ hinv169 h64 h_v187 h_v196 (by ns_tac) (by ns_tac) as ⟨v197, s170, hinv170, h_v197⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v175 h_v186 dropping h_v187 h_v196 hinv169 s169 v187 v196
  store_step with Store.literal_boolean_spec s170 true hinv170 h64 as ⟨v198, s171, hinv171, h_v198⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v175 h_v186 h_v197 dropping hinv170 s170
  store_step with Store.apply_rep s171 v197 v198 _ _ hinv171 h64 h_v197 h_v198 (by ns_tac) (by ns_tac) as ⟨v199, s172, hinv172, h_v199⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v175 h_v186 dropping h_v197 h_v198 hinv171 s171 v197 v198
  store_step with Store.apply_rep s172 v186 v199 _ _ hinv172 h64 h_v186 h_v199 (by ns_tac) (by ns_tac) as ⟨v200, s173, hinv173, h_v200⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v175 dropping h_v186 h_v199 hinv172 s172 v186 v199
  store_step with Store.apply_rep s173 v175 v200 _ _ hinv173 h64 h_v175 h_v200 (by ns_tac) (by ns_tac) as ⟨v201, s174, hinv174, h_v201⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 dropping h_v175 h_v200 hinv173 s173 v175 v200
  step as ⟨e_v202, he_v202⟩
  store_step with CtorSpec.eo_bvadd.construct s174 e_v202 (by rw [he_v202]; exact empty_args) hinv174 h64 as ⟨v202, s175, hinv175, h_v202⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v201 dropping he_v202 hinv174 e_v202 s174
  step as ⟨e_v203, he_v203⟩
  store_step with CtorSpec.eo_bvneg.construct s175 e_v203 (by rw [he_v203]; exact empty_args) hinv175 h64 as ⟨v203, s176, hinv176, h_v203⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v201 h_v202 dropping he_v203 hinv175 e_v203 s175
  step as ⟨e_v204, he_v204⟩
  store_step with CtorSpec.eo_bvurem.construct s176 e_v204 (by rw [he_v204]; exact empty_args) hinv176 h64 as ⟨v204, s177, hinv177, h_v204⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v201 h_v202 h_v203 dropping he_v204 hinv176 e_v204 s176
  step as ⟨e_v205, he_v205⟩
  store_step with CtorSpec.eo_ite.construct s177 e_v205 (by rw [he_v205]; exact empty_args) hinv177 h64 as ⟨v205, s178, hinv178, h_v205⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v201 h_v202 h_v203 h_v204 dropping he_v205 hinv177 e_v205 s177
  step as ⟨e_v206, he_v206⟩
  store_step with CtorSpec.eo__3d.construct s178 e_v206 (by rw [he_v206]; exact empty_args) hinv178 h64 as ⟨v206, s179, hinv179, h_v206⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v201 h_v202 h_v203 h_v204 h_v205 dropping he_v206 hinv178 e_v206 s178
  step as ⟨e_v207, he_v207⟩
  store_step with CtorSpec.eo_extract.construct s179 e_v207 (by rw [he_v207]; rfl) h_a3 h_a3 hinv179 h64 as ⟨v207, s180, hinv180, h_v207⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v201 h_v202 h_v203 h_v204 h_v205 h_v206 dropping he_v207 hinv179 e_v207 s179
  store_step with Store.apply_rep s180 v207 a0 _ _ hinv180 h64 h_v207 h_a0 (by ns_tac) (by ns_tac) as ⟨v208, s181, hinv181, h_v208⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v201 h_v202 h_v203 h_v204 h_v205 h_v206 dropping h_v207 hinv180 s180 v207
  store_step with Store.apply_rep s181 v206 v208 _ _ hinv181 h64 h_v206 h_v208 (by ns_tac) (by ns_tac) as ⟨v209, s182, hinv182, h_v209⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v201 h_v202 h_v203 h_v204 h_v205 dropping h_v206 h_v208 hinv181 s181 v206 v208
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s182 1#u32 (1) (by scalar_tac) hinv182 h64 as ⟨v210, s183, hinv183, h_v210⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v201 h_v202 h_v203 h_v204 h_v205 h_v209 dropping hinv182 s182
  step as ⟨e_v211, he_v211⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s183 e_v211 (by rw [he_v211]; rfl) h_v210 hinv183 h64 as ⟨v211, s184, hinv184, h_v211⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v201 h_v202 h_v203 h_v204 h_v205 h_v209 dropping h_v210 he_v211 hinv183 e_v211 s183 v210
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s184 0#u32 (0) (by scalar_tac) hinv184 h64 as ⟨v212, s185, hinv185, h_v212⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v201 h_v202 h_v203 h_v204 h_v205 h_v209 h_v211 dropping hinv184 s184
  store_step with Store.apply_rep s185 v211 v212 _ _ hinv185 h64 h_v211 h_v212 (by ns_tac) (by ns_tac) as ⟨v213, s186, hinv186, h_v213⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v201 h_v202 h_v203 h_v204 h_v205 h_v209 dropping h_v211 h_v212 hinv185 s185 v211 v212
  store_step with Store.apply_rep s186 v209 v213 _ _ hinv186 h64 h_v209 h_v213 (by ns_tac) (by ns_tac) as ⟨v214, s187, hinv187, h_v214⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v201 h_v202 h_v203 h_v204 h_v205 dropping h_v209 h_v213 hinv186 s186 v209 v213
  store_step with Store.apply_rep s187 v205 v214 _ _ hinv187 h64 h_v205 h_v214 (by ns_tac) (by ns_tac) as ⟨v215, s188, hinv188, h_v215⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v201 h_v202 h_v203 h_v204 dropping h_v205 h_v214 hinv187 s187 v205 v214
  store_step with Store.apply_rep s188 v215 a0 _ _ hinv188 h64 h_v215 h_a0 (by ns_tac) (by ns_tac) as ⟨v216, s189, hinv189, h_v216⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v201 h_v202 h_v203 h_v204 dropping h_v215 hinv188 s188 v215
  step as ⟨e_v217, he_v217⟩
  store_step with CtorSpec.eo_bvneg.construct s189 e_v217 (by rw [he_v217]; exact empty_args) hinv189 h64 as ⟨v217, s190, hinv190, h_v217⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v201 h_v202 h_v203 h_v204 h_v216 dropping he_v217 hinv189 e_v217 s189
  store_step with Store.apply_rep s190 v217 a0 _ _ hinv190 h64 h_v217 h_a0 (by ns_tac) (by ns_tac) as ⟨v218, s191, hinv191, h_v218⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v201 h_v202 h_v203 h_v204 h_v216 dropping h_v217 hinv190 s190 v217
  store_step with Store.apply_rep s191 v216 v218 _ _ hinv191 h64 h_v216 h_v218 (by ns_tac) (by ns_tac) as ⟨v219, s192, hinv192, h_v219⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v201 h_v202 h_v203 h_v204 dropping h_v216 h_v218 hinv191 s191 v216 v218
  store_step with Store.apply_rep s192 v204 v219 _ _ hinv192 h64 h_v204 h_v219 (by ns_tac) (by ns_tac) as ⟨v220, s193, hinv193, h_v220⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v201 h_v202 h_v203 dropping h_v204 h_v219 hinv192 s192 v204 v219
  step as ⟨e_v221, he_v221⟩
  store_step with CtorSpec.eo_ite.construct s193 e_v221 (by rw [he_v221]; exact empty_args) hinv193 h64 as ⟨v221, s194, hinv194, h_v221⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v201 h_v202 h_v203 h_v220 dropping he_v221 hinv193 e_v221 s193
  step as ⟨e_v222, he_v222⟩
  store_step with CtorSpec.eo__3d.construct s194 e_v222 (by rw [he_v222]; exact empty_args) hinv194 h64 as ⟨v222, s195, hinv195, h_v222⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v201 h_v202 h_v203 h_v220 h_v221 dropping he_v222 hinv194 e_v222 s194
  step as ⟨e_v223, he_v223⟩
  store_step with CtorSpec.eo_extract.construct s195 e_v223 (by rw [he_v223]; rfl) h_a3 h_a3 hinv195 h64 as ⟨v223, s196, hinv196, h_v223⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v201 h_v202 h_v203 h_v220 h_v221 h_v222 dropping he_v223 hinv195 e_v223 s195
  store_step with Store.apply_rep s196 v223 a1 _ _ hinv196 h64 h_v223 h_a1 (by ns_tac) (by ns_tac) as ⟨v224, s197, hinv197, h_v224⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v201 h_v202 h_v203 h_v220 h_v221 h_v222 dropping h_v223 hinv196 s196 v223
  store_step with Store.apply_rep s197 v222 v224 _ _ hinv197 h64 h_v222 h_v224 (by ns_tac) (by ns_tac) as ⟨v225, s198, hinv198, h_v225⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v201 h_v202 h_v203 h_v220 h_v221 dropping h_v222 h_v224 hinv197 s197 v222 v224
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s198 1#u32 (1) (by scalar_tac) hinv198 h64 as ⟨v226, s199, hinv199, h_v226⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v201 h_v202 h_v203 h_v220 h_v221 h_v225 dropping hinv198 s198
  step as ⟨e_v227, he_v227⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s199 e_v227 (by rw [he_v227]; rfl) h_v226 hinv199 h64 as ⟨v227, s200, hinv200, h_v227⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v201 h_v202 h_v203 h_v220 h_v221 h_v225 dropping h_v226 he_v227 hinv199 e_v227 s199 v226
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s200 0#u32 (0) (by scalar_tac) hinv200 h64 as ⟨v228, s201, hinv201, h_v228⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v201 h_v202 h_v203 h_v220 h_v221 h_v225 h_v227 dropping hinv200 s200
  store_step with Store.apply_rep s201 v227 v228 _ _ hinv201 h64 h_v227 h_v228 (by ns_tac) (by ns_tac) as ⟨v229, s202, hinv202, h_v229⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v201 h_v202 h_v203 h_v220 h_v221 h_v225 dropping h_v227 h_v228 hinv201 s201 v227 v228
  store_step with Store.apply_rep s202 v225 v229 _ _ hinv202 h64 h_v225 h_v229 (by ns_tac) (by ns_tac) as ⟨v230, s203, hinv203, h_v230⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v201 h_v202 h_v203 h_v220 h_v221 dropping h_v225 h_v229 hinv202 s202 v225 v229
  store_step with Store.apply_rep s203 v221 v230 _ _ hinv203 h64 h_v221 h_v230 (by ns_tac) (by ns_tac) as ⟨v231, s204, hinv204, h_v231⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v201 h_v202 h_v203 h_v220 dropping h_v221 h_v230 hinv203 s203 v221 v230
  store_step with Store.apply_rep s204 v231 a1 _ _ hinv204 h64 h_v231 h_a1 (by ns_tac) (by ns_tac) as ⟨v232, s205, hinv205, h_v232⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v201 h_v202 h_v203 h_v220 dropping h_v231 hinv204 s204 v231
  step as ⟨e_v233, he_v233⟩
  store_step with CtorSpec.eo_bvneg.construct s205 e_v233 (by rw [he_v233]; exact empty_args) hinv205 h64 as ⟨v233, s206, hinv206, h_v233⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v201 h_v202 h_v203 h_v220 h_v232 dropping he_v233 hinv205 e_v233 s205
  store_step with Store.apply_rep s206 v233 a1 _ _ hinv206 h64 h_v233 h_a1 (by ns_tac) (by ns_tac) as ⟨v234, s207, hinv207, h_v234⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v201 h_v202 h_v203 h_v220 h_v232 dropping h_v233 hinv206 s206 v233
  store_step with Store.apply_rep s207 v232 v234 _ _ hinv207 h64 h_v232 h_v234 (by ns_tac) (by ns_tac) as ⟨v235, s208, hinv208, h_v235⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v201 h_v202 h_v203 h_v220 dropping h_v232 h_v234 hinv207 s207 v232 v234
  store_step with Store.apply_rep s208 v220 v235 _ _ hinv208 h64 h_v220 h_v235 (by ns_tac) (by ns_tac) as ⟨v236, s209, hinv209, h_v236⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v201 h_v202 h_v203 dropping h_v220 h_v235 hinv208 s208 v220 v235
  store_step with Store.apply_rep s209 v203 v236 _ _ hinv209 h64 h_v203 h_v236 (by ns_tac) (by ns_tac) as ⟨v237, s210, hinv210, h_v237⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v201 h_v202 dropping h_v203 h_v236 hinv209 s209 v203 v236
  store_step with Store.apply_rep s210 v202 v237 _ _ hinv210 h64 h_v202 h_v237 (by ns_tac) (by ns_tac) as ⟨v238, s211, hinv211, h_v238⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v201 dropping h_v202 h_v237 hinv210 s210 v202 v237
  step as ⟨e_v239, he_v239⟩
  store_step with CtorSpec.eo_bvadd.construct s211 e_v239 (by rw [he_v239]; exact empty_args) hinv211 h64 as ⟨v239, s212, hinv212, h_v239⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v201 h_v238 dropping he_v239 hinv211 e_v239 s211
  store_step with Store.apply_rep s212 v239 a1 _ _ hinv212 h64 h_v239 h_a1 (by ns_tac) (by ns_tac) as ⟨v240, s213, hinv213, h_v240⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v201 h_v238 dropping h_v239 hinv212 s212 v239
  step as ⟨e_v241, he_v241⟩
  store_step with CtorSpec.eo_bvadd.construct s213 e_v241 (by rw [he_v241]; exact empty_args) hinv213 h64 as ⟨v241, s214, hinv214, h_v241⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v201 h_v238 h_v240 dropping he_v241 hinv213 e_v241 s213
  step as ⟨e_v242, he_v242⟩
  store_step with CtorSpec.eo_bvneg.construct s214 e_v242 (by rw [he_v242]; exact empty_args) hinv214 h64 as ⟨v242, s215, hinv215, h_v242⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v201 h_v238 h_v240 h_v241 dropping he_v242 hinv214 e_v242 s214
  step as ⟨e_v243, he_v243⟩
  store_step with CtorSpec.eo_bvurem.construct s215 e_v243 (by rw [he_v243]; exact empty_args) hinv215 h64 as ⟨v243, s216, hinv216, h_v243⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v201 h_v238 h_v240 h_v241 h_v242 dropping he_v243 hinv215 e_v243 s215
  step as ⟨e_v244, he_v244⟩
  store_step with CtorSpec.eo_ite.construct s216 e_v244 (by rw [he_v244]; exact empty_args) hinv216 h64 as ⟨v244, s217, hinv217, h_v244⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v201 h_v238 h_v240 h_v241 h_v242 h_v243 dropping he_v244 hinv216 e_v244 s216
  step as ⟨e_v245, he_v245⟩
  store_step with CtorSpec.eo__3d.construct s217 e_v245 (by rw [he_v245]; exact empty_args) hinv217 h64 as ⟨v245, s218, hinv218, h_v245⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v201 h_v238 h_v240 h_v241 h_v242 h_v243 h_v244 dropping he_v245 hinv217 e_v245 s217
  step as ⟨e_v246, he_v246⟩
  store_step with CtorSpec.eo_extract.construct s218 e_v246 (by rw [he_v246]; rfl) h_a3 h_a3 hinv218 h64 as ⟨v246, s219, hinv219, h_v246⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v201 h_v238 h_v240 h_v241 h_v242 h_v243 h_v244 h_v245 dropping he_v246 hinv218 e_v246 s218
  store_step with Store.apply_rep s219 v246 a0 _ _ hinv219 h64 h_v246 h_a0 (by ns_tac) (by ns_tac) as ⟨v247, s220, hinv220, h_v247⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v201 h_v238 h_v240 h_v241 h_v242 h_v243 h_v244 h_v245 dropping h_v246 hinv219 s219 v246
  store_step with Store.apply_rep s220 v245 v247 _ _ hinv220 h64 h_v245 h_v247 (by ns_tac) (by ns_tac) as ⟨v248, s221, hinv221, h_v248⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v201 h_v238 h_v240 h_v241 h_v242 h_v243 h_v244 dropping h_v245 h_v247 hinv220 s220 v245 v247
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s221 1#u32 (1) (by scalar_tac) hinv221 h64 as ⟨v249, s222, hinv222, h_v249⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v201 h_v238 h_v240 h_v241 h_v242 h_v243 h_v244 h_v248 dropping hinv221 s221
  step as ⟨e_v250, he_v250⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s222 e_v250 (by rw [he_v250]; rfl) h_v249 hinv222 h64 as ⟨v250, s223, hinv223, h_v250⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v201 h_v238 h_v240 h_v241 h_v242 h_v243 h_v244 h_v248 dropping h_v249 he_v250 hinv222 e_v250 s222 v249
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s223 0#u32 (0) (by scalar_tac) hinv223 h64 as ⟨v251, s224, hinv224, h_v251⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v201 h_v238 h_v240 h_v241 h_v242 h_v243 h_v244 h_v248 h_v250 dropping hinv223 s223
  store_step with Store.apply_rep s224 v250 v251 _ _ hinv224 h64 h_v250 h_v251 (by ns_tac) (by ns_tac) as ⟨v252, s225, hinv225, h_v252⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v201 h_v238 h_v240 h_v241 h_v242 h_v243 h_v244 h_v248 dropping h_v250 h_v251 hinv224 s224 v250 v251
  store_step with Store.apply_rep s225 v248 v252 _ _ hinv225 h64 h_v248 h_v252 (by ns_tac) (by ns_tac) as ⟨v253, s226, hinv226, h_v253⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v201 h_v238 h_v240 h_v241 h_v242 h_v243 h_v244 dropping h_v248 h_v252 hinv225 s225 v248 v252
  store_step with Store.apply_rep s226 v244 v253 _ _ hinv226 h64 h_v244 h_v253 (by ns_tac) (by ns_tac) as ⟨v254, s227, hinv227, h_v254⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v201 h_v238 h_v240 h_v241 h_v242 h_v243 dropping h_v244 h_v253 hinv226 s226 v244 v253
  store_step with Store.apply_rep s227 v254 a0 _ _ hinv227 h64 h_v254 h_a0 (by ns_tac) (by ns_tac) as ⟨v255, s228, hinv228, h_v255⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v201 h_v238 h_v240 h_v241 h_v242 h_v243 dropping h_v254 hinv227 s227 v254
  step as ⟨e_v256, he_v256⟩
  store_step with CtorSpec.eo_bvneg.construct s228 e_v256 (by rw [he_v256]; exact empty_args) hinv228 h64 as ⟨v256, s229, hinv229, h_v256⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v201 h_v238 h_v240 h_v241 h_v242 h_v243 h_v255 dropping he_v256 hinv228 e_v256 s228
  store_step with Store.apply_rep s229 v256 a0 _ _ hinv229 h64 h_v256 h_a0 (by ns_tac) (by ns_tac) as ⟨v257, s230, hinv230, h_v257⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v201 h_v238 h_v240 h_v241 h_v242 h_v243 h_v255 dropping h_v256 hinv229 s229 v256
  store_step with Store.apply_rep s230 v255 v257 _ _ hinv230 h64 h_v255 h_v257 (by ns_tac) (by ns_tac) as ⟨v258, s231, hinv231, h_v258⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v201 h_v238 h_v240 h_v241 h_v242 h_v243 dropping h_v255 h_v257 hinv230 s230 v255 v257
  store_step with Store.apply_rep s231 v243 v258 _ _ hinv231 h64 h_v243 h_v258 (by ns_tac) (by ns_tac) as ⟨v259, s232, hinv232, h_v259⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v201 h_v238 h_v240 h_v241 h_v242 dropping h_v243 h_v258 hinv231 s231 v243 v258
  step as ⟨e_v260, he_v260⟩
  store_step with CtorSpec.eo_ite.construct s232 e_v260 (by rw [he_v260]; exact empty_args) hinv232 h64 as ⟨v260, s233, hinv233, h_v260⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v201 h_v238 h_v240 h_v241 h_v242 h_v259 dropping he_v260 hinv232 e_v260 s232
  step as ⟨e_v261, he_v261⟩
  store_step with CtorSpec.eo__3d.construct s233 e_v261 (by rw [he_v261]; exact empty_args) hinv233 h64 as ⟨v261, s234, hinv234, h_v261⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v201 h_v238 h_v240 h_v241 h_v242 h_v259 h_v260 dropping he_v261 hinv233 e_v261 s233
  step as ⟨e_v262, he_v262⟩
  store_step with CtorSpec.eo_extract.construct s234 e_v262 (by rw [he_v262]; rfl) h_a3 h_a3 hinv234 h64 as ⟨v262, s235, hinv235, h_v262⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v201 h_v238 h_v240 h_v241 h_v242 h_v259 h_v260 h_v261 dropping he_v262 hinv234 e_v262 s234
  store_step with Store.apply_rep s235 v262 a1 _ _ hinv235 h64 h_v262 h_a1 (by ns_tac) (by ns_tac) as ⟨v263, s236, hinv236, h_v263⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v201 h_v238 h_v240 h_v241 h_v242 h_v259 h_v260 h_v261 dropping h_v262 hinv235 s235 v262
  store_step with Store.apply_rep s236 v261 v263 _ _ hinv236 h64 h_v261 h_v263 (by ns_tac) (by ns_tac) as ⟨v264, s237, hinv237, h_v264⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v201 h_v238 h_v240 h_v241 h_v242 h_v259 h_v260 dropping h_v261 h_v263 hinv236 s236 v261 v263
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s237 1#u32 (1) (by scalar_tac) hinv237 h64 as ⟨v265, s238, hinv238, h_v265⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v201 h_v238 h_v240 h_v241 h_v242 h_v259 h_v260 h_v264 dropping hinv237 s237
  step as ⟨e_v266, he_v266⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s238 e_v266 (by rw [he_v266]; rfl) h_v265 hinv238 h64 as ⟨v266, s239, hinv239, h_v266⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v201 h_v238 h_v240 h_v241 h_v242 h_v259 h_v260 h_v264 dropping h_v265 he_v266 hinv238 e_v266 s238 v265
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s239 0#u32 (0) (by scalar_tac) hinv239 h64 as ⟨v267, s240, hinv240, h_v267⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v201 h_v238 h_v240 h_v241 h_v242 h_v259 h_v260 h_v264 h_v266 dropping hinv239 s239
  store_step with Store.apply_rep s240 v266 v267 _ _ hinv240 h64 h_v266 h_v267 (by ns_tac) (by ns_tac) as ⟨v268, s241, hinv241, h_v268⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v201 h_v238 h_v240 h_v241 h_v242 h_v259 h_v260 h_v264 dropping h_v266 h_v267 hinv240 s240 v266 v267
  store_step with Store.apply_rep s241 v264 v268 _ _ hinv241 h64 h_v264 h_v268 (by ns_tac) (by ns_tac) as ⟨v269, s242, hinv242, h_v269⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v201 h_v238 h_v240 h_v241 h_v242 h_v259 h_v260 dropping h_v264 h_v268 hinv241 s241 v264 v268
  store_step with Store.apply_rep s242 v260 v269 _ _ hinv242 h64 h_v260 h_v269 (by ns_tac) (by ns_tac) as ⟨v270, s243, hinv243, h_v270⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v201 h_v238 h_v240 h_v241 h_v242 h_v259 dropping h_v260 h_v269 hinv242 s242 v260 v269
  store_step with Store.apply_rep s243 v270 a1 _ _ hinv243 h64 h_v270 h_a1 (by ns_tac) (by ns_tac) as ⟨v271, s244, hinv244, h_v271⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v201 h_v238 h_v240 h_v241 h_v242 h_v259 dropping h_v270 hinv243 s243 v270
  step as ⟨e_v272, he_v272⟩
  store_step with CtorSpec.eo_bvneg.construct s244 e_v272 (by rw [he_v272]; exact empty_args) hinv244 h64 as ⟨v272, s245, hinv245, h_v272⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v201 h_v238 h_v240 h_v241 h_v242 h_v259 h_v271 dropping he_v272 hinv244 e_v272 s244
  store_step with Store.apply_rep s245 v272 a1 _ _ hinv245 h64 h_v272 h_a1 (by ns_tac) (by ns_tac) as ⟨v273, s246, hinv246, h_v273⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v201 h_v238 h_v240 h_v241 h_v242 h_v259 h_v271 dropping h_v272 hinv245 s245 v272
  store_step with Store.apply_rep s246 v271 v273 _ _ hinv246 h64 h_v271 h_v273 (by ns_tac) (by ns_tac) as ⟨v274, s247, hinv247, h_v274⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v201 h_v238 h_v240 h_v241 h_v242 h_v259 dropping h_v271 h_v273 hinv246 s246 v271 v273
  store_step with Store.apply_rep s247 v259 v274 _ _ hinv247 h64 h_v259 h_v274 (by ns_tac) (by ns_tac) as ⟨v275, s248, hinv248, h_v275⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v201 h_v238 h_v240 h_v241 h_v242 dropping h_v259 h_v274 hinv247 s247 v259 v274
  store_step with Store.apply_rep s248 v242 v275 _ _ hinv248 h64 h_v242 h_v275 (by ns_tac) (by ns_tac) as ⟨v276, s249, hinv249, h_v276⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v201 h_v238 h_v240 h_v241 dropping h_v242 h_v275 hinv248 s248 v242 v275
  store_step with ih.eo__24eo_5ftypeof s249 v276 _ hinv249 h64 (hG.rem hrem) h_v276 as ⟨v277, s250, hinv250, h_v277⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v201 h_v238 h_v240 h_v241 dropping h_v276 hinv249 s249 v276
  store_step with ih.eo__24eo_5fnil s250 v241 v277 _ _ hinv250 h64 (hG.rem hrem) h_v241 h_v277 as ⟨v278, s251, hinv251, h_v278⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v201 h_v238 h_v240 dropping h_v241 h_v277 hinv250 s250 v241 v277
  store_step with Store.apply_mk_rep s251 v240 v278 _ _ hinv251 h64 h_v240 h_v278 as ⟨v279, s252, hinv252, h_v279⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v201 h_v238 dropping h_v240 h_v278 hinv251 s251 v240 v278
  store_step with Store.apply_mk_rep s252 v238 v279 _ _ hinv252 h64 h_v238 h_v279 as ⟨v280, s253, hinv253, h_v280⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v201 dropping h_v238 h_v279 hinv252 s252 v238 v279
  store_step with Store.apply_mk_rep s253 v201 v280 _ _ hinv253 h64 h_v201 h_v280 as ⟨v281, s254, hinv254, h_v281⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 dropping h_v201 h_v280 hinv253 s253 v201 v280
  step as ⟨e_v282, he_v282⟩
  store_step with CtorSpec.eo_ite.construct s254 e_v282 (by rw [he_v282]; exact empty_args) hinv254 h64 as ⟨v282, s255, hinv255, h_v282⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 dropping he_v282 hinv254 e_v282 s254
  step as ⟨e_v283, he_v283⟩
  store_step with CtorSpec.eo_and.construct s255 e_v283 (by rw [he_v283]; exact empty_args) hinv255 h64 as ⟨v283, s256, hinv256, h_v283⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v282 dropping he_v283 hinv255 e_v283 s255
  step as ⟨e_v284, he_v284⟩
  store_step with CtorSpec.eo__3d.construct s256 e_v284 (by rw [he_v284]; exact empty_args) hinv256 h64 as ⟨v284, s257, hinv257, h_v284⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v282 h_v283 dropping he_v284 hinv256 e_v284 s256
  step as ⟨e_v285, he_v285⟩
  store_step with CtorSpec.eo_extract.construct s257 e_v285 (by rw [he_v285]; rfl) h_a3 h_a3 hinv257 h64 as ⟨v285, s258, hinv258, h_v285⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v282 h_v283 h_v284 dropping he_v285 hinv257 e_v285 s257
  store_step with Store.apply_rep s258 v285 a0 _ _ hinv258 h64 h_v285 h_a0 (by ns_tac) (by ns_tac) as ⟨v286, s259, hinv259, h_v286⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v282 h_v283 h_v284 dropping h_v285 hinv258 s258 v285
  store_step with Store.apply_rep s259 v284 v286 _ _ hinv259 h64 h_v284 h_v286 (by ns_tac) (by ns_tac) as ⟨v287, s260, hinv260, h_v287⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v282 h_v283 dropping h_v284 h_v286 hinv259 s259 v284 v286
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s260 1#u32 (1) (by scalar_tac) hinv260 h64 as ⟨v288, s261, hinv261, h_v288⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v282 h_v283 h_v287 dropping hinv260 s260
  step as ⟨e_v289, he_v289⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s261 e_v289 (by rw [he_v289]; rfl) h_v288 hinv261 h64 as ⟨v289, s262, hinv262, h_v289⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v282 h_v283 h_v287 dropping h_v288 he_v289 hinv261 e_v289 s261 v288
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s262 0#u32 (0) (by scalar_tac) hinv262 h64 as ⟨v290, s263, hinv263, h_v290⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v282 h_v283 h_v287 h_v289 dropping hinv262 s262
  store_step with Store.apply_rep s263 v289 v290 _ _ hinv263 h64 h_v289 h_v290 (by ns_tac) (by ns_tac) as ⟨v291, s264, hinv264, h_v291⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v282 h_v283 h_v287 dropping h_v289 h_v290 hinv263 s263 v289 v290
  store_step with Store.apply_rep s264 v287 v291 _ _ hinv264 h64 h_v287 h_v291 (by ns_tac) (by ns_tac) as ⟨v292, s265, hinv265, h_v292⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v282 h_v283 dropping h_v287 h_v291 hinv264 s264 v287 v291
  store_step with Store.apply_rep s265 v283 v292 _ _ hinv265 h64 h_v283 h_v292 (by ns_tac) (by ns_tac) as ⟨v293, s266, hinv266, h_v293⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v282 dropping h_v283 h_v292 hinv265 s265 v283 v292
  step as ⟨e_v294, he_v294⟩
  store_step with CtorSpec.eo_and.construct s266 e_v294 (by rw [he_v294]; exact empty_args) hinv266 h64 as ⟨v294, s267, hinv267, h_v294⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v282 h_v293 dropping he_v294 hinv266 e_v294 s266
  step as ⟨e_v295, he_v295⟩
  store_step with CtorSpec.eo__3d.construct s267 e_v295 (by rw [he_v295]; exact empty_args) hinv267 h64 as ⟨v295, s268, hinv268, h_v295⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v282 h_v293 h_v294 dropping he_v295 hinv267 e_v295 s267
  step as ⟨e_v296, he_v296⟩
  store_step with CtorSpec.eo_extract.construct s268 e_v296 (by rw [he_v296]; rfl) h_a3 h_a3 hinv268 h64 as ⟨v296, s269, hinv269, h_v296⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v282 h_v293 h_v294 h_v295 dropping he_v296 hinv268 e_v296 s268
  store_step with Store.apply_rep s269 v296 a1 _ _ hinv269 h64 h_v296 h_a1 (by ns_tac) (by ns_tac) as ⟨v297, s270, hinv270, h_v297⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v282 h_v293 h_v294 h_v295 dropping h_v296 hinv269 s269 v296
  store_step with Store.apply_rep s270 v295 v297 _ _ hinv270 h64 h_v295 h_v297 (by ns_tac) (by ns_tac) as ⟨v298, s271, hinv271, h_v298⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v282 h_v293 h_v294 dropping h_v295 h_v297 hinv270 s270 v295 v297
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s271 1#u32 (1) (by scalar_tac) hinv271 h64 as ⟨v299, s272, hinv272, h_v299⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v282 h_v293 h_v294 h_v298 dropping hinv271 s271
  step as ⟨e_v300, he_v300⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s272 e_v300 (by rw [he_v300]; rfl) h_v299 hinv272 h64 as ⟨v300, s273, hinv273, h_v300⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v282 h_v293 h_v294 h_v298 dropping h_v299 he_v300 hinv272 e_v300 s272 v299
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s273 1#u32 (1) (by scalar_tac) hinv273 h64 as ⟨v301, s274, hinv274, h_v301⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v282 h_v293 h_v294 h_v298 h_v300 dropping hinv273 s273
  store_step with Store.apply_rep s274 v300 v301 _ _ hinv274 h64 h_v300 h_v301 (by ns_tac) (by ns_tac) as ⟨v302, s275, hinv275, h_v302⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v282 h_v293 h_v294 h_v298 dropping h_v300 h_v301 hinv274 s274 v300 v301
  store_step with Store.apply_rep s275 v298 v302 _ _ hinv275 h64 h_v298 h_v302 (by ns_tac) (by ns_tac) as ⟨v303, s276, hinv276, h_v303⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v282 h_v293 h_v294 dropping h_v298 h_v302 hinv275 s275 v298 v302
  store_step with Store.apply_rep s276 v294 v303 _ _ hinv276 h64 h_v294 h_v303 (by ns_tac) (by ns_tac) as ⟨v304, s277, hinv277, h_v304⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v282 h_v293 dropping h_v294 h_v303 hinv276 s276 v294 v303
  store_step with Store.literal_boolean_spec s277 true hinv277 h64 as ⟨v305, s278, hinv278, h_v305⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v282 h_v293 h_v304 dropping hinv277 s277
  store_step with Store.apply_rep s278 v304 v305 _ _ hinv278 h64 h_v304 h_v305 (by ns_tac) (by ns_tac) as ⟨v306, s279, hinv279, h_v306⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v282 h_v293 dropping h_v304 h_v305 hinv278 s278 v304 v305
  store_step with Store.apply_rep s279 v293 v306 _ _ hinv279 h64 h_v293 h_v306 (by ns_tac) (by ns_tac) as ⟨v307, s280, hinv280, h_v307⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v282 dropping h_v293 h_v306 hinv279 s279 v293 v306
  store_step with Store.apply_rep s280 v282 v307 _ _ hinv280 h64 h_v282 h_v307 (by ns_tac) (by ns_tac) as ⟨v308, s281, hinv281, h_v308⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 dropping h_v282 h_v307 hinv280 s280 v282 v307
  step as ⟨e_v309, he_v309⟩
  store_step with CtorSpec.eo_bvadd.construct s281 e_v309 (by rw [he_v309]; exact empty_args) hinv281 h64 as ⟨v309, s282, hinv282, h_v309⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v308 dropping he_v309 hinv281 e_v309 s281
  step as ⟨e_v310, he_v310⟩
  store_step with CtorSpec.eo_bvurem.construct s282 e_v310 (by rw [he_v310]; exact empty_args) hinv282 h64 as ⟨v310, s283, hinv283, h_v310⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v308 h_v309 dropping he_v310 hinv282 e_v310 s282
  step as ⟨e_v311, he_v311⟩
  store_step with CtorSpec.eo_ite.construct s283 e_v311 (by rw [he_v311]; exact empty_args) hinv283 h64 as ⟨v311, s284, hinv284, h_v311⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v308 h_v309 h_v310 dropping he_v311 hinv283 e_v311 s283
  step as ⟨e_v312, he_v312⟩
  store_step with CtorSpec.eo__3d.construct s284 e_v312 (by rw [he_v312]; exact empty_args) hinv284 h64 as ⟨v312, s285, hinv285, h_v312⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v308 h_v309 h_v310 h_v311 dropping he_v312 hinv284 e_v312 s284
  step as ⟨e_v313, he_v313⟩
  store_step with CtorSpec.eo_extract.construct s285 e_v313 (by rw [he_v313]; rfl) h_a3 h_a3 hinv285 h64 as ⟨v313, s286, hinv286, h_v313⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v308 h_v309 h_v310 h_v311 h_v312 dropping he_v313 hinv285 e_v313 s285
  store_step with Store.apply_rep s286 v313 a0 _ _ hinv286 h64 h_v313 h_a0 (by ns_tac) (by ns_tac) as ⟨v314, s287, hinv287, h_v314⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v308 h_v309 h_v310 h_v311 h_v312 dropping h_v313 hinv286 s286 v313
  store_step with Store.apply_rep s287 v312 v314 _ _ hinv287 h64 h_v312 h_v314 (by ns_tac) (by ns_tac) as ⟨v315, s288, hinv288, h_v315⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v308 h_v309 h_v310 h_v311 dropping h_v312 h_v314 hinv287 s287 v312 v314
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s288 1#u32 (1) (by scalar_tac) hinv288 h64 as ⟨v316, s289, hinv289, h_v316⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v308 h_v309 h_v310 h_v311 h_v315 dropping hinv288 s288
  step as ⟨e_v317, he_v317⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s289 e_v317 (by rw [he_v317]; rfl) h_v316 hinv289 h64 as ⟨v317, s290, hinv290, h_v317⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v308 h_v309 h_v310 h_v311 h_v315 dropping h_v316 he_v317 hinv289 e_v317 s289 v316
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s290 0#u32 (0) (by scalar_tac) hinv290 h64 as ⟨v318, s291, hinv291, h_v318⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v308 h_v309 h_v310 h_v311 h_v315 h_v317 dropping hinv290 s290
  store_step with Store.apply_rep s291 v317 v318 _ _ hinv291 h64 h_v317 h_v318 (by ns_tac) (by ns_tac) as ⟨v319, s292, hinv292, h_v319⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v308 h_v309 h_v310 h_v311 h_v315 dropping h_v317 h_v318 hinv291 s291 v317 v318
  store_step with Store.apply_rep s292 v315 v319 _ _ hinv292 h64 h_v315 h_v319 (by ns_tac) (by ns_tac) as ⟨v320, s293, hinv293, h_v320⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v308 h_v309 h_v310 h_v311 dropping h_v315 h_v319 hinv292 s292 v315 v319
  store_step with Store.apply_rep s293 v311 v320 _ _ hinv293 h64 h_v311 h_v320 (by ns_tac) (by ns_tac) as ⟨v321, s294, hinv294, h_v321⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v308 h_v309 h_v310 dropping h_v311 h_v320 hinv293 s293 v311 v320
  store_step with Store.apply_rep s294 v321 a0 _ _ hinv294 h64 h_v321 h_a0 (by ns_tac) (by ns_tac) as ⟨v322, s295, hinv295, h_v322⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v308 h_v309 h_v310 dropping h_v321 hinv294 s294 v321
  step as ⟨e_v323, he_v323⟩
  store_step with CtorSpec.eo_bvneg.construct s295 e_v323 (by rw [he_v323]; exact empty_args) hinv295 h64 as ⟨v323, s296, hinv296, h_v323⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v308 h_v309 h_v310 h_v322 dropping he_v323 hinv295 e_v323 s295
  store_step with Store.apply_rep s296 v323 a0 _ _ hinv296 h64 h_v323 h_a0 (by ns_tac) (by ns_tac) as ⟨v324, s297, hinv297, h_v324⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v308 h_v309 h_v310 h_v322 dropping h_v323 hinv296 s296 v323
  store_step with Store.apply_rep s297 v322 v324 _ _ hinv297 h64 h_v322 h_v324 (by ns_tac) (by ns_tac) as ⟨v325, s298, hinv298, h_v325⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v308 h_v309 h_v310 dropping h_v322 h_v324 hinv297 s297 v322 v324
  store_step with Store.apply_rep s298 v310 v325 _ _ hinv298 h64 h_v310 h_v325 (by ns_tac) (by ns_tac) as ⟨v326, s299, hinv299, h_v326⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v308 h_v309 dropping h_v310 h_v325 hinv298 s298 v310 v325
  step as ⟨e_v327, he_v327⟩
  store_step with CtorSpec.eo_ite.construct s299 e_v327 (by rw [he_v327]; exact empty_args) hinv299 h64 as ⟨v327, s300, hinv300, h_v327⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v308 h_v309 h_v326 dropping he_v327 hinv299 e_v327 s299
  step as ⟨e_v328, he_v328⟩
  store_step with CtorSpec.eo__3d.construct s300 e_v328 (by rw [he_v328]; exact empty_args) hinv300 h64 as ⟨v328, s301, hinv301, h_v328⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v308 h_v309 h_v326 h_v327 dropping he_v328 hinv300 e_v328 s300
  step as ⟨e_v329, he_v329⟩
  store_step with CtorSpec.eo_extract.construct s301 e_v329 (by rw [he_v329]; rfl) h_a3 h_a3 hinv301 h64 as ⟨v329, s302, hinv302, h_v329⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v308 h_v309 h_v326 h_v327 h_v328 dropping he_v329 hinv301 e_v329 s301
  store_step with Store.apply_rep s302 v329 a1 _ _ hinv302 h64 h_v329 h_a1 (by ns_tac) (by ns_tac) as ⟨v330, s303, hinv303, h_v330⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v308 h_v309 h_v326 h_v327 h_v328 dropping h_v329 hinv302 s302 v329
  store_step with Store.apply_rep s303 v328 v330 _ _ hinv303 h64 h_v328 h_v330 (by ns_tac) (by ns_tac) as ⟨v331, s304, hinv304, h_v331⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v308 h_v309 h_v326 h_v327 dropping h_v328 h_v330 hinv303 s303 v328 v330
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s304 1#u32 (1) (by scalar_tac) hinv304 h64 as ⟨v332, s305, hinv305, h_v332⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v308 h_v309 h_v326 h_v327 h_v331 dropping hinv304 s304
  step as ⟨e_v333, he_v333⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s305 e_v333 (by rw [he_v333]; rfl) h_v332 hinv305 h64 as ⟨v333, s306, hinv306, h_v333⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v308 h_v309 h_v326 h_v327 h_v331 dropping h_v332 he_v333 hinv305 e_v333 s305 v332
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s306 0#u32 (0) (by scalar_tac) hinv306 h64 as ⟨v334, s307, hinv307, h_v334⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v308 h_v309 h_v326 h_v327 h_v331 h_v333 dropping hinv306 s306
  store_step with Store.apply_rep s307 v333 v334 _ _ hinv307 h64 h_v333 h_v334 (by ns_tac) (by ns_tac) as ⟨v335, s308, hinv308, h_v335⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v308 h_v309 h_v326 h_v327 h_v331 dropping h_v333 h_v334 hinv307 s307 v333 v334
  store_step with Store.apply_rep s308 v331 v335 _ _ hinv308 h64 h_v331 h_v335 (by ns_tac) (by ns_tac) as ⟨v336, s309, hinv309, h_v336⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v308 h_v309 h_v326 h_v327 dropping h_v331 h_v335 hinv308 s308 v331 v335
  store_step with Store.apply_rep s309 v327 v336 _ _ hinv309 h64 h_v327 h_v336 (by ns_tac) (by ns_tac) as ⟨v337, s310, hinv310, h_v337⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v308 h_v309 h_v326 dropping h_v327 h_v336 hinv309 s309 v327 v336
  store_step with Store.apply_rep s310 v337 a1 _ _ hinv310 h64 h_v337 h_a1 (by ns_tac) (by ns_tac) as ⟨v338, s311, hinv311, h_v338⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v308 h_v309 h_v326 dropping h_v337 hinv310 s310 v337
  step as ⟨e_v339, he_v339⟩
  store_step with CtorSpec.eo_bvneg.construct s311 e_v339 (by rw [he_v339]; exact empty_args) hinv311 h64 as ⟨v339, s312, hinv312, h_v339⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v308 h_v309 h_v326 h_v338 dropping he_v339 hinv311 e_v339 s311
  store_step with Store.apply_rep s312 v339 a1 _ _ hinv312 h64 h_v339 h_a1 (by ns_tac) (by ns_tac) as ⟨v340, s313, hinv313, h_v340⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v308 h_v309 h_v326 h_v338 dropping h_v339 hinv312 s312 v339
  store_step with Store.apply_rep s313 v338 v340 _ _ hinv313 h64 h_v338 h_v340 (by ns_tac) (by ns_tac) as ⟨v341, s314, hinv314, h_v341⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v308 h_v309 h_v326 dropping h_v338 h_v340 hinv313 s313 v338 v340
  store_step with Store.apply_rep s314 v326 v341 _ _ hinv314 h64 h_v326 h_v341 (by ns_tac) (by ns_tac) as ⟨v342, s315, hinv315, h_v342⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v308 h_v309 dropping h_v326 h_v341 hinv314 s314 v326 v341
  store_step with Store.apply_rep s315 v309 v342 _ _ hinv315 h64 h_v309 h_v342 (by ns_tac) (by ns_tac) as ⟨v343, s316, hinv316, h_v343⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v308 dropping h_v309 h_v342 hinv315 s315 v309 v342
  step as ⟨e_v344, he_v344⟩
  store_step with CtorSpec.eo_bvadd.construct s316 e_v344 (by rw [he_v344]; exact empty_args) hinv316 h64 as ⟨v344, s317, hinv317, h_v344⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v308 h_v343 dropping he_v344 hinv316 e_v344 s316
  store_step with Store.apply_rep s317 v344 a1 _ _ hinv317 h64 h_v344 h_a1 (by ns_tac) (by ns_tac) as ⟨v345, s318, hinv318, h_v345⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v308 h_v343 dropping h_v344 hinv317 s317 v344
  step as ⟨e_v346, he_v346⟩
  store_step with CtorSpec.eo_bvadd.construct s318 e_v346 (by rw [he_v346]; exact empty_args) hinv318 h64 as ⟨v346, s319, hinv319, h_v346⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v308 h_v343 h_v345 dropping he_v346 hinv318 e_v346 s318
  step as ⟨e_v347, he_v347⟩
  store_step with CtorSpec.eo_bvurem.construct s319 e_v347 (by rw [he_v347]; exact empty_args) hinv319 h64 as ⟨v347, s320, hinv320, h_v347⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v308 h_v343 h_v345 h_v346 dropping he_v347 hinv319 e_v347 s319
  step as ⟨e_v348, he_v348⟩
  store_step with CtorSpec.eo_ite.construct s320 e_v348 (by rw [he_v348]; exact empty_args) hinv320 h64 as ⟨v348, s321, hinv321, h_v348⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v308 h_v343 h_v345 h_v346 h_v347 dropping he_v348 hinv320 e_v348 s320
  step as ⟨e_v349, he_v349⟩
  store_step with CtorSpec.eo__3d.construct s321 e_v349 (by rw [he_v349]; exact empty_args) hinv321 h64 as ⟨v349, s322, hinv322, h_v349⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v308 h_v343 h_v345 h_v346 h_v347 h_v348 dropping he_v349 hinv321 e_v349 s321
  step as ⟨e_v350, he_v350⟩
  store_step with CtorSpec.eo_extract.construct s322 e_v350 (by rw [he_v350]; rfl) h_a3 h_a3 hinv322 h64 as ⟨v350, s323, hinv323, h_v350⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v308 h_v343 h_v345 h_v346 h_v347 h_v348 h_v349 dropping he_v350 hinv322 e_v350 s322
  store_step with Store.apply_rep s323 v350 a0 _ _ hinv323 h64 h_v350 h_a0 (by ns_tac) (by ns_tac) as ⟨v351, s324, hinv324, h_v351⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v308 h_v343 h_v345 h_v346 h_v347 h_v348 h_v349 dropping h_v350 hinv323 s323 v350
  store_step with Store.apply_rep s324 v349 v351 _ _ hinv324 h64 h_v349 h_v351 (by ns_tac) (by ns_tac) as ⟨v352, s325, hinv325, h_v352⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v308 h_v343 h_v345 h_v346 h_v347 h_v348 dropping h_v349 h_v351 hinv324 s324 v349 v351
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s325 1#u32 (1) (by scalar_tac) hinv325 h64 as ⟨v353, s326, hinv326, h_v353⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v308 h_v343 h_v345 h_v346 h_v347 h_v348 h_v352 dropping hinv325 s325
  step as ⟨e_v354, he_v354⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s326 e_v354 (by rw [he_v354]; rfl) h_v353 hinv326 h64 as ⟨v354, s327, hinv327, h_v354⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v308 h_v343 h_v345 h_v346 h_v347 h_v348 h_v352 dropping h_v353 he_v354 hinv326 e_v354 s326 v353
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s327 0#u32 (0) (by scalar_tac) hinv327 h64 as ⟨v355, s328, hinv328, h_v355⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v308 h_v343 h_v345 h_v346 h_v347 h_v348 h_v352 h_v354 dropping hinv327 s327
  store_step with Store.apply_rep s328 v354 v355 _ _ hinv328 h64 h_v354 h_v355 (by ns_tac) (by ns_tac) as ⟨v356, s329, hinv329, h_v356⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v308 h_v343 h_v345 h_v346 h_v347 h_v348 h_v352 dropping h_v354 h_v355 hinv328 s328 v354 v355
  store_step with Store.apply_rep s329 v352 v356 _ _ hinv329 h64 h_v352 h_v356 (by ns_tac) (by ns_tac) as ⟨v357, s330, hinv330, h_v357⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v308 h_v343 h_v345 h_v346 h_v347 h_v348 dropping h_v352 h_v356 hinv329 s329 v352 v356
  store_step with Store.apply_rep s330 v348 v357 _ _ hinv330 h64 h_v348 h_v357 (by ns_tac) (by ns_tac) as ⟨v358, s331, hinv331, h_v358⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v308 h_v343 h_v345 h_v346 h_v347 dropping h_v348 h_v357 hinv330 s330 v348 v357
  store_step with Store.apply_rep s331 v358 a0 _ _ hinv331 h64 h_v358 h_a0 (by ns_tac) (by ns_tac) as ⟨v359, s332, hinv332, h_v359⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v308 h_v343 h_v345 h_v346 h_v347 dropping h_v358 hinv331 s331 v358
  step as ⟨e_v360, he_v360⟩
  store_step with CtorSpec.eo_bvneg.construct s332 e_v360 (by rw [he_v360]; exact empty_args) hinv332 h64 as ⟨v360, s333, hinv333, h_v360⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v308 h_v343 h_v345 h_v346 h_v347 h_v359 dropping he_v360 hinv332 e_v360 s332
  store_step with Store.apply_rep s333 v360 a0 _ _ hinv333 h64 h_v360 h_a0 (by ns_tac) (by ns_tac) as ⟨v361, s334, hinv334, h_v361⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v308 h_v343 h_v345 h_v346 h_v347 h_v359 dropping h_v360 hinv333 s333 v360
  store_step with Store.apply_rep s334 v359 v361 _ _ hinv334 h64 h_v359 h_v361 (by ns_tac) (by ns_tac) as ⟨v362, s335, hinv335, h_v362⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v308 h_v343 h_v345 h_v346 h_v347 dropping h_v359 h_v361 hinv334 s334 v359 v361
  store_step with Store.apply_rep s335 v347 v362 _ _ hinv335 h64 h_v347 h_v362 (by ns_tac) (by ns_tac) as ⟨v363, s336, hinv336, h_v363⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v308 h_v343 h_v345 h_v346 dropping h_v347 h_v362 hinv335 s335 v347 v362
  step as ⟨e_v364, he_v364⟩
  store_step with CtorSpec.eo_ite.construct s336 e_v364 (by rw [he_v364]; exact empty_args) hinv336 h64 as ⟨v364, s337, hinv337, h_v364⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v308 h_v343 h_v345 h_v346 h_v363 dropping he_v364 hinv336 e_v364 s336
  step as ⟨e_v365, he_v365⟩
  store_step with CtorSpec.eo__3d.construct s337 e_v365 (by rw [he_v365]; exact empty_args) hinv337 h64 as ⟨v365, s338, hinv338, h_v365⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v308 h_v343 h_v345 h_v346 h_v363 h_v364 dropping he_v365 hinv337 e_v365 s337
  step as ⟨e_v366, he_v366⟩
  store_step with CtorSpec.eo_extract.construct s338 e_v366 (by rw [he_v366]; rfl) h_a3 h_a3 hinv338 h64 as ⟨v366, s339, hinv339, h_v366⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v308 h_v343 h_v345 h_v346 h_v363 h_v364 h_v365 dropping he_v366 hinv338 e_v366 s338
  store_step with Store.apply_rep s339 v366 a1 _ _ hinv339 h64 h_v366 h_a1 (by ns_tac) (by ns_tac) as ⟨v367, s340, hinv340, h_v367⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v308 h_v343 h_v345 h_v346 h_v363 h_v364 h_v365 dropping h_v366 hinv339 s339 v366
  store_step with Store.apply_rep s340 v365 v367 _ _ hinv340 h64 h_v365 h_v367 (by ns_tac) (by ns_tac) as ⟨v368, s341, hinv341, h_v368⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v308 h_v343 h_v345 h_v346 h_v363 h_v364 dropping h_v365 h_v367 hinv340 s340 v365 v367
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s341 1#u32 (1) (by scalar_tac) hinv341 h64 as ⟨v369, s342, hinv342, h_v369⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v308 h_v343 h_v345 h_v346 h_v363 h_v364 h_v368 dropping hinv341 s341
  step as ⟨e_v370, he_v370⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s342 e_v370 (by rw [he_v370]; rfl) h_v369 hinv342 h64 as ⟨v370, s343, hinv343, h_v370⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v308 h_v343 h_v345 h_v346 h_v363 h_v364 h_v368 dropping h_v369 he_v370 hinv342 e_v370 s342 v369
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s343 0#u32 (0) (by scalar_tac) hinv343 h64 as ⟨v371, s344, hinv344, h_v371⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v308 h_v343 h_v345 h_v346 h_v363 h_v364 h_v368 h_v370 dropping hinv343 s343
  store_step with Store.apply_rep s344 v370 v371 _ _ hinv344 h64 h_v370 h_v371 (by ns_tac) (by ns_tac) as ⟨v372, s345, hinv345, h_v372⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v308 h_v343 h_v345 h_v346 h_v363 h_v364 h_v368 dropping h_v370 h_v371 hinv344 s344 v370 v371
  store_step with Store.apply_rep s345 v368 v372 _ _ hinv345 h64 h_v368 h_v372 (by ns_tac) (by ns_tac) as ⟨v373, s346, hinv346, h_v373⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v308 h_v343 h_v345 h_v346 h_v363 h_v364 dropping h_v368 h_v372 hinv345 s345 v368 v372
  store_step with Store.apply_rep s346 v364 v373 _ _ hinv346 h64 h_v364 h_v373 (by ns_tac) (by ns_tac) as ⟨v374, s347, hinv347, h_v374⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v308 h_v343 h_v345 h_v346 h_v363 dropping h_v364 h_v373 hinv346 s346 v364 v373
  store_step with Store.apply_rep s347 v374 a1 _ _ hinv347 h64 h_v374 h_a1 (by ns_tac) (by ns_tac) as ⟨v375, s348, hinv348, h_v375⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v308 h_v343 h_v345 h_v346 h_v363 dropping h_v374 hinv347 s347 v374
  step as ⟨e_v376, he_v376⟩
  store_step with CtorSpec.eo_bvneg.construct s348 e_v376 (by rw [he_v376]; exact empty_args) hinv348 h64 as ⟨v376, s349, hinv349, h_v376⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v308 h_v343 h_v345 h_v346 h_v363 h_v375 dropping he_v376 hinv348 e_v376 s348
  store_step with Store.apply_rep s349 v376 a1 _ _ hinv349 h64 h_v376 h_a1 (by ns_tac) (by ns_tac) as ⟨v377, s350, hinv350, h_v377⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v308 h_v343 h_v345 h_v346 h_v363 h_v375 dropping h_v376 hinv349 s349 v376
  store_step with Store.apply_rep s350 v375 v377 _ _ hinv350 h64 h_v375 h_v377 (by ns_tac) (by ns_tac) as ⟨v378, s351, hinv351, h_v378⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v308 h_v343 h_v345 h_v346 h_v363 dropping h_v375 h_v377 hinv350 s350 v375 v377
  store_step with Store.apply_rep s351 v363 v378 _ _ hinv351 h64 h_v363 h_v378 (by ns_tac) (by ns_tac) as ⟨v379, s352, hinv352, h_v379⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v308 h_v343 h_v345 h_v346 dropping h_v363 h_v378 hinv351 s351 v363 v378
  store_step with ih.eo__24eo_5ftypeof s352 v379 _ hinv352 h64 (hG.rem hrem) h_v379 as ⟨v380, s353, hinv353, h_v380⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v308 h_v343 h_v345 h_v346 dropping h_v379 hinv352 s352 v379
  store_step with ih.eo__24eo_5fnil s353 v346 v380 _ _ hinv353 h64 (hG.rem hrem) h_v346 h_v380 as ⟨v381, s354, hinv354, h_v381⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v308 h_v343 h_v345 dropping h_v346 h_v380 hinv353 s353 v346 v380
  store_step with Store.apply_mk_rep s354 v345 v381 _ _ hinv354 h64 h_v345 h_v381 as ⟨v382, s355, hinv355, h_v382⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v308 h_v343 dropping h_v345 h_v381 hinv354 s354 v345 v381
  store_step with Store.apply_mk_rep s355 v343 v382 _ _ hinv355 h64 h_v343 h_v382 as ⟨v383, s356, hinv356, h_v383⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v308 dropping h_v343 h_v382 hinv355 s355 v343 v382
  store_step with Store.apply_mk_rep s356 v308 v383 _ _ hinv356 h64 h_v308 h_v383 as ⟨v384, s357, hinv357, h_v384⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 dropping h_v308 h_v383 hinv356 s356 v308 v383
  step as ⟨e_v385, he_v385⟩
  store_step with CtorSpec.eo_bvneg.construct s357 e_v385 (by rw [he_v385]; exact empty_args) hinv357 h64 as ⟨v385, s358, hinv358, h_v385⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v384 dropping he_v385 hinv357 e_v385 s357
  step as ⟨e_v386, he_v386⟩
  store_step with CtorSpec.eo_bvurem.construct s358 e_v386 (by rw [he_v386]; exact empty_args) hinv358 h64 as ⟨v386, s359, hinv359, h_v386⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v384 h_v385 dropping he_v386 hinv358 e_v386 s358
  step as ⟨e_v387, he_v387⟩
  store_step with CtorSpec.eo_ite.construct s359 e_v387 (by rw [he_v387]; exact empty_args) hinv359 h64 as ⟨v387, s360, hinv360, h_v387⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v384 h_v385 h_v386 dropping he_v387 hinv359 e_v387 s359
  step as ⟨e_v388, he_v388⟩
  store_step with CtorSpec.eo__3d.construct s360 e_v388 (by rw [he_v388]; exact empty_args) hinv360 h64 as ⟨v388, s361, hinv361, h_v388⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v384 h_v385 h_v386 h_v387 dropping he_v388 hinv360 e_v388 s360
  step as ⟨e_v389, he_v389⟩
  store_step with CtorSpec.eo_extract.construct s361 e_v389 (by rw [he_v389]; rfl) h_a3 h_a3 hinv361 h64 as ⟨v389, s362, hinv362, h_v389⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v384 h_v385 h_v386 h_v387 h_v388 dropping he_v389 hinv361 e_v389 s361
  store_step with Store.apply_rep s362 v389 a0 _ _ hinv362 h64 h_v389 h_a0 (by ns_tac) (by ns_tac) as ⟨v390, s363, hinv363, h_v390⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v384 h_v385 h_v386 h_v387 h_v388 dropping h_v389 hinv362 s362 v389
  store_step with Store.apply_rep s363 v388 v390 _ _ hinv363 h64 h_v388 h_v390 (by ns_tac) (by ns_tac) as ⟨v391, s364, hinv364, h_v391⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v384 h_v385 h_v386 h_v387 dropping h_v388 h_v390 hinv363 s363 v388 v390
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s364 1#u32 (1) (by scalar_tac) hinv364 h64 as ⟨v392, s365, hinv365, h_v392⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v384 h_v385 h_v386 h_v387 h_v391 dropping hinv364 s364
  step as ⟨e_v393, he_v393⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s365 e_v393 (by rw [he_v393]; rfl) h_v392 hinv365 h64 as ⟨v393, s366, hinv366, h_v393⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v384 h_v385 h_v386 h_v387 h_v391 dropping h_v392 he_v393 hinv365 e_v393 s365 v392
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s366 0#u32 (0) (by scalar_tac) hinv366 h64 as ⟨v394, s367, hinv367, h_v394⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v384 h_v385 h_v386 h_v387 h_v391 h_v393 dropping hinv366 s366
  store_step with Store.apply_rep s367 v393 v394 _ _ hinv367 h64 h_v393 h_v394 (by ns_tac) (by ns_tac) as ⟨v395, s368, hinv368, h_v395⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v384 h_v385 h_v386 h_v387 h_v391 dropping h_v393 h_v394 hinv367 s367 v393 v394
  store_step with Store.apply_rep s368 v391 v395 _ _ hinv368 h64 h_v391 h_v395 (by ns_tac) (by ns_tac) as ⟨v396, s369, hinv369, h_v396⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v384 h_v385 h_v386 h_v387 dropping h_v391 h_v395 hinv368 s368 v391 v395
  store_step with Store.apply_rep s369 v387 v396 _ _ hinv369 h64 h_v387 h_v396 (by ns_tac) (by ns_tac) as ⟨v397, s370, hinv370, h_v397⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v384 h_v385 h_v386 dropping h_v387 h_v396 hinv369 s369 v387 v396
  store_step with Store.apply_rep s370 v397 a0 _ _ hinv370 h64 h_v397 h_a0 (by ns_tac) (by ns_tac) as ⟨v398, s371, hinv371, h_v398⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v384 h_v385 h_v386 dropping h_v397 hinv370 s370 v397
  step as ⟨e_v399, he_v399⟩
  store_step with CtorSpec.eo_bvneg.construct s371 e_v399 (by rw [he_v399]; exact empty_args) hinv371 h64 as ⟨v399, s372, hinv372, h_v399⟩ growing hG carrying h_a0 h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v384 h_v385 h_v386 h_v398 dropping he_v399 hinv371 e_v399 s371
  store_step with Store.apply_rep s372 v399 a0 _ _ hinv372 h64 h_v399 h_a0 (by ns_tac) (by ns_tac) as ⟨v400, s373, hinv373, h_v400⟩ growing hG carrying h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v384 h_v385 h_v386 h_v398 dropping h_a0 h_v399 hinv372 s372 v399
  store_step with Store.apply_rep s373 v398 v400 _ _ hinv373 h64 h_v398 h_v400 (by ns_tac) (by ns_tac) as ⟨v401, s374, hinv374, h_v401⟩ growing hG carrying h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v384 h_v385 h_v386 dropping h_v398 h_v400 hinv373 s373 v398 v400
  store_step with Store.apply_rep s374 v386 v401 _ _ hinv374 h64 h_v386 h_v401 (by ns_tac) (by ns_tac) as ⟨v402, s375, hinv375, h_v402⟩ growing hG carrying h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v384 h_v385 dropping h_v386 h_v401 hinv374 s374 v386 v401
  step as ⟨e_v403, he_v403⟩
  store_step with CtorSpec.eo_ite.construct s375 e_v403 (by rw [he_v403]; exact empty_args) hinv375 h64 as ⟨v403, s376, hinv376, h_v403⟩ growing hG carrying h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v384 h_v385 h_v402 dropping he_v403 hinv375 e_v403 s375
  step as ⟨e_v404, he_v404⟩
  store_step with CtorSpec.eo__3d.construct s376 e_v404 (by rw [he_v404]; exact empty_args) hinv376 h64 as ⟨v404, s377, hinv377, h_v404⟩ growing hG carrying h_a1 h_a3 h_v38 h_v113 h_v174 h_v281 h_v384 h_v385 h_v402 h_v403 dropping he_v404 hinv376 e_v404 s376
  step as ⟨e_v405, he_v405⟩
  store_step with CtorSpec.eo_extract.construct s377 e_v405 (by rw [he_v405]; rfl) h_a3 h_a3 hinv377 h64 as ⟨v405, s378, hinv378, h_v405⟩ growing hG carrying h_a1 h_v38 h_v113 h_v174 h_v281 h_v384 h_v385 h_v402 h_v403 h_v404 dropping h_a3 he_v405 hinv377 e_v405 s377
  store_step with Store.apply_rep s378 v405 a1 _ _ hinv378 h64 h_v405 h_a1 (by ns_tac) (by ns_tac) as ⟨v406, s379, hinv379, h_v406⟩ growing hG carrying h_a1 h_v38 h_v113 h_v174 h_v281 h_v384 h_v385 h_v402 h_v403 h_v404 dropping h_v405 hinv378 s378 v405
  store_step with Store.apply_rep s379 v404 v406 _ _ hinv379 h64 h_v404 h_v406 (by ns_tac) (by ns_tac) as ⟨v407, s380, hinv380, h_v407⟩ growing hG carrying h_a1 h_v38 h_v113 h_v174 h_v281 h_v384 h_v385 h_v402 h_v403 dropping h_v404 h_v406 hinv379 s379 v404 v406
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s380 1#u32 (1) (by scalar_tac) hinv380 h64 as ⟨v408, s381, hinv381, h_v408⟩ growing hG carrying h_a1 h_v38 h_v113 h_v174 h_v281 h_v384 h_v385 h_v402 h_v403 h_v407 dropping hinv380 s380
  step as ⟨e_v409, he_v409⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s381 e_v409 (by rw [he_v409]; rfl) h_v408 hinv381 h64 as ⟨v409, s382, hinv382, h_v409⟩ growing hG carrying h_a1 h_v38 h_v113 h_v174 h_v281 h_v384 h_v385 h_v402 h_v403 h_v407 dropping h_v408 he_v409 hinv381 e_v409 s381 v408
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s382 0#u32 (0) (by scalar_tac) hinv382 h64 as ⟨v410, s383, hinv383, h_v410⟩ growing hG carrying h_a1 h_v38 h_v113 h_v174 h_v281 h_v384 h_v385 h_v402 h_v403 h_v407 h_v409 dropping hinv382 s382
  store_step with Store.apply_rep s383 v409 v410 _ _ hinv383 h64 h_v409 h_v410 (by ns_tac) (by ns_tac) as ⟨v411, s384, hinv384, h_v411⟩ growing hG carrying h_a1 h_v38 h_v113 h_v174 h_v281 h_v384 h_v385 h_v402 h_v403 h_v407 dropping h_v409 h_v410 hinv383 s383 v409 v410
  store_step with Store.apply_rep s384 v407 v411 _ _ hinv384 h64 h_v407 h_v411 (by ns_tac) (by ns_tac) as ⟨v412, s385, hinv385, h_v412⟩ growing hG carrying h_a1 h_v38 h_v113 h_v174 h_v281 h_v384 h_v385 h_v402 h_v403 dropping h_v407 h_v411 hinv384 s384 v407 v411
  store_step with Store.apply_rep s385 v403 v412 _ _ hinv385 h64 h_v403 h_v412 (by ns_tac) (by ns_tac) as ⟨v413, s386, hinv386, h_v413⟩ growing hG carrying h_a1 h_v38 h_v113 h_v174 h_v281 h_v384 h_v385 h_v402 dropping h_v403 h_v412 hinv385 s385 v403 v412
  store_step with Store.apply_rep s386 v413 a1 _ _ hinv386 h64 h_v413 h_a1 (by ns_tac) (by ns_tac) as ⟨v414, s387, hinv387, h_v414⟩ growing hG carrying h_a1 h_v38 h_v113 h_v174 h_v281 h_v384 h_v385 h_v402 dropping h_v413 hinv386 s386 v413
  step as ⟨e_v415, he_v415⟩
  store_step with CtorSpec.eo_bvneg.construct s387 e_v415 (by rw [he_v415]; exact empty_args) hinv387 h64 as ⟨v415, s388, hinv388, h_v415⟩ growing hG carrying h_a1 h_v38 h_v113 h_v174 h_v281 h_v384 h_v385 h_v402 h_v414 dropping he_v415 hinv387 e_v415 s387
  store_step with Store.apply_rep s388 v415 a1 _ _ hinv388 h64 h_v415 h_a1 (by ns_tac) (by ns_tac) as ⟨v416, s389, hinv389, h_v416⟩ growing hG carrying h_v38 h_v113 h_v174 h_v281 h_v384 h_v385 h_v402 h_v414 dropping h_a1 h_v415 hinv388 s388 v415
  store_step with Store.apply_rep s389 v414 v416 _ _ hinv389 h64 h_v414 h_v416 (by ns_tac) (by ns_tac) as ⟨v417, s390, hinv390, h_v417⟩ growing hG carrying h_v38 h_v113 h_v174 h_v281 h_v384 h_v385 h_v402 dropping h_v414 h_v416 hinv389 s389 v414 v416
  store_step with Store.apply_rep s390 v402 v417 _ _ hinv390 h64 h_v402 h_v417 (by ns_tac) (by ns_tac) as ⟨v418, s391, hinv391, h_v418⟩ growing hG carrying h_v38 h_v113 h_v174 h_v281 h_v384 h_v385 dropping h_v402 h_v417 hinv390 s390 v402 v417
  store_step with Store.apply_rep s391 v385 v418 _ _ hinv391 h64 h_v385 h_v418 (by ns_tac) (by ns_tac) as ⟨v419, s392, hinv392, h_v419⟩ growing hG carrying h_v38 h_v113 h_v174 h_v281 h_v384 dropping h_v385 h_v418 hinv391 s391 v385 v418
  store_step with Store.apply_mk_rep s392 v384 v419 _ _ hinv392 h64 h_v384 h_v419 as ⟨v420, s393, hinv393, h_v420⟩ growing hG carrying h_v38 h_v113 h_v174 h_v281 dropping h_v384 h_v419 hinv392 s392 v384 v419
  store_step with Store.apply_mk_rep s393 v281 v420 _ _ hinv393 h64 h_v281 h_v420 as ⟨v421, s394, hinv394, h_v421⟩ growing hG carrying h_v38 h_v113 h_v174 dropping h_v281 h_v420 hinv393 s393 v281 v420
  store_step with Store.apply_mk_rep s394 v174 v421 _ _ hinv394 h64 h_v174 h_v421 as ⟨v422, s395, hinv395, h_v422⟩ growing hG carrying h_v38 h_v113 dropping h_v174 h_v421 hinv394 s394 v174 v421
  store_step with Store.apply_mk_rep s395 v113 v422 _ _ hinv395 h64 h_v113 h_v422 as ⟨v423, s396, hinv396, h_v423⟩ growing hG carrying h_v38 dropping h_v113 h_v422 hinv395 s395 v113 v422
  store_step with Store.apply_mk_rep s396 v38 v423 _ _ hinv396 h64 h_v38 h_v423 as ⟨v424, s397, hinv397, h_v424⟩ growing hG carrying dropping h_v38 h_v423 hinv396 s396 v38 v423
  case_done hinv397 hG with h_v424 in EoCases.__eo_prog_bv_smod_eliminate.case_0 using hn_a0 hn_a1 hn_a2 hn_a3 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v16 hn_v17 hn_v19 hn_v20 hn_v23 hn_v24 hn_v26 hn_v27 hn_v30 hn_v31

/-- logos's `__eo_prog_bv_smod_eliminate` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fbv_2dsmod_2deliminate.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) (hw_a4 : Valid.valid x_a4) (hw_a5 : Valid.valid x_a5) :
    __eo_prog_bv_smod_eliminate x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_bv_smod_eliminate.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_bv_smod_eliminate
  unfold EoCases.__eo_prog_bv_smod_eliminate.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fbv_2dsmod_2deliminate_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) :
    body_eo__24eo_5fprog_5fbv_2dsmod_2deliminate s a0 a1 a2 a3 a4 a5 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_smod_eliminate x_a0 x_a1 x_a2 x_a3 x_a4 x_a5)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fbv_2dsmod_2deliminate.rust_eq x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3) (by valid_tac hinv h_a4) (by valid_tac hinv h_a5)]
  unfold body_eo__24eo_5fprog_5fbv_2dsmod_2deliminate
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  stuck_check h_a3 : x_a3 as hn_a3 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fbv_2dsmod_2deliminate_spec n ih s a0 a1 a2 a3 a4 a5 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 hn_a0 hn_a1 hn_a2 hn_a3
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 using hn_a0 hn_a1 hn_a2 hn_a3
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hn_a3 hc0 in EoCases.__eo_prog_bv_smod_eliminate.case_0

theorem eo__24eo_5fprog_5fbv_2dsmod_2deliminate_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fbv_2dsmod_2deliminate.Spec n := by
  intro s a0 a1 a2 a3 a4 a5 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5
  unfold eo__24eo_5fprog_5fbv_2dsmod_2deliminate
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fbv_2dsmod_2deliminate s1 a0 a1 a2 a3 a4 a5) (fun s' t => Represents.rep s' t (__eo_prog_bv_smod_eliminate x_a0 x_a1 x_a2 x_a3 x_a4 x_a5))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fbv_2dsmod_2deliminate_spec m (ih m hm) s1 a0 a1 a2 a3 a4 a5 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn) (by congr_one h_a4 hn) (by congr_one h_a5 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

end pathos_compiled_checker
