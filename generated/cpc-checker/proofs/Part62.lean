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

set_option maxHeartbeats 20000000 in
theorem case_0_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d2_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 a6 a7 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _) (x_a7 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) (h_a6 : Represents.rep s a6 x_a6) (h_a7 : Represents.rep s a7 x_a7) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) (hn_a4 : x_a4 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d2 s a0 a1 a2 a3 a4 a5 a6 a7 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_bv_sign_extend_ult_const_2.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_bv_sign_extend_ult_const_2.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d2
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a5 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_bv_sign_extend_ult_const_2.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_sign_extend_ult_const_2.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_sign_extend_ult_const_2.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a6 h_a7 h_v4 h_v6 h_v7 dropping h_a5 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_2.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_2.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_2.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo_bvult.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a6 h_a7 h_v4 h_v11 h_v13 h_v14 dropping h_v10 h_v6 h_v7 h_v8 he_v15 hinv1 e_v15 s1 v10 v6 v7 v8
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_2.case_0
  pat_unapply h_v14 as ⟨v17, v18, x_v17, x_v18, h_v17, h_v18, hn_v17, hn_v18⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_2.case_0
  pat_unapply h_v17 as ⟨v20, v21, x_v20, x_v21, h_v20, h_v21, hn_v20, hn_v21⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_2.case_0
  step as ⟨e_v22, he_v22⟩
  store_step with CtorSpec.eo_bvshl.construct s2 e_v22 (by rw [he_v22]; exact empty_args) hinv2 h64 as ⟨v22, s3, hinv3, h_v22⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a6 h_a7 h_v4 h_v11 h_v18 h_v20 h_v21 dropping h_v13 h_v14 h_v15 h_v17 he_v22 hinv2 e_v22 s2 v13 v14 v15 v17
  pat_same v20 v22 with h_v20 h_v22 using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_2.case_0
  pat_unapply h_v21 as ⟨v24, v25, x_v24, x_v25, h_v24, h_v25, hn_v24, hn_v25⟩ using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_2.case_0
  pat_destruct CtorSpec.eo_int_5fto_5fbv.destruct h_v24 as ⟨v27, x_v27, h_v27⟩ else hinv3 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_2.case_0
  obtain hn_v27 := CtorSpec.eo_int_5fto_5fbv.fields_ne_stuck hinv3 h_v24
  pat_same v27 a3 with h_v27 h_a3 using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_2.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s3 1#u32 (1) (by scalar_tac) hinv3 h64 as ⟨v28, s4, hinv4, h_v28⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a6 h_a7 h_v4 h_v11 h_v18 h_v25 dropping h_v20 h_v21 h_v22 h_v24 h_v27 hinv3 s3 v20 v21 v22 v24 v27
  pat_same v25 v28 with h_v25 h_v28 using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_2.case_0
  pat_unapply h_v18 as ⟨v30, v31, x_v30, x_v31, h_v30, h_v31, hn_v30, hn_v31⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_2.case_0
  pat_destruct CtorSpec.eo_int_5fto_5fbv.destruct h_v30 as ⟨v33, x_v33, h_v33⟩ else hinv4 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_2.case_0
  obtain hn_v33 := CtorSpec.eo_int_5fto_5fbv.fields_ne_stuck hinv4 h_v30
  pat_same v33 a3 with h_v33 h_a3 using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_2.case_0
  pat_unapply h_v31 as ⟨v35, v36, x_v35, x_v36, h_v35, h_v36, hn_v35, hn_v36⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_2.case_0
  pat_unapply h_v35 as ⟨v38, v39, x_v38, x_v39, h_v38, h_v39, hn_v38, hn_v39⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_2.case_0
  step as ⟨e_v40, he_v40⟩
  store_step with CtorSpec.eo__2d.construct s4 e_v40 (by rw [he_v40]; exact empty_args) hinv4 h64 as ⟨v40, s5, hinv5, h_v40⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a6 h_a7 h_v4 h_v11 h_v36 h_v38 h_v39 dropping h_v18 h_v25 h_v28 h_v30 h_v31 h_v33 h_v35 he_v40 hinv4 e_v40 s4 v18 v25 v28 v30 v31 v33 v35
  pat_same v38 v40 with h_v38 h_v40 using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_2.case_0
  pat_unapply h_v39 as ⟨v42, v43, x_v42, x_v43, h_v42, h_v43, hn_v42, hn_v43⟩ using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_2.case_0
  step as ⟨e_v44, he_v44⟩
  store_step with CtorSpec.eo__40bvsize.construct s5 e_v44 (by rw [he_v44]; exact empty_args) hinv5 h64 as ⟨v44, s6, hinv6, h_v44⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a6 h_a7 h_v4 h_v11 h_v36 h_v42 h_v43 dropping h_v38 h_v39 h_v40 he_v44 hinv5 e_v44 s5 v38 v39 v40
  pat_same v42 v44 with h_v42 h_v44 using hinv6 else hinv6 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_2.case_0
  pat_same v43 a0 with h_v43 h_a0 using hinv6 else hinv6 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_2.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s6 1#u32 (1) (by scalar_tac) hinv6 h64 as ⟨v45, s7, hinv7, h_v45⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a6 h_a7 h_v4 h_v11 h_v36 dropping h_v42 h_v43 h_v44 hinv6 s6 v42 v43 v44
  pat_same v36 v45 with h_v36 h_v45 using hinv7 else hinv7 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_2.case_0
  pat_unapply h_v11 as ⟨v47, v48, x_v47, x_v48, h_v47, h_v48, hn_v47, hn_v48⟩ using hinv7 else hinv7 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_2.case_0
  pat_destruct CtorSpec.eo_int_5fto_5fbv.destruct h_v47 as ⟨v50, x_v50, h_v50⟩ else hinv7 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_2.case_0
  obtain hn_v50 := CtorSpec.eo_int_5fto_5fbv.fields_ne_stuck hinv7 h_v47
  pat_same v50 a3 with h_v50 h_a3 using hinv7 else hinv7 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_2.case_0
  pat_same v48 a2 with h_v48 h_a2 using hinv7 else hinv7 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_2.case_0
  store_step with Store.literal_boolean_spec s7 true hinv7 h64 as ⟨v51, s8, hinv8, h_v51⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a6 h_a7 h_v4 dropping h_v11 h_v36 h_v45 h_v47 h_v48 h_v50 hinv7 s7 v11 v36 v45 v47 v48 v50
  pat_same v4 v51 with h_v4 h_v51 using hinv8 else hinv8 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_2.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a6 as ⟨v53, x_v53, h_v53⟩ else hinv8 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_2.case_0
  pat_unapply h_v53 as ⟨v55, v56, x_v55, x_v56, h_v55, h_v56, hn_v55, hn_v56⟩ using hinv8 else hinv8 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_2.case_0
  pat_unapply h_v55 as ⟨v58, v59, x_v58, x_v59, h_v58, h_v59, hn_v58, hn_v59⟩ using hinv8 else hinv8 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_2.case_0
  step as ⟨e_v60, he_v60⟩
  store_step with CtorSpec.eo__3d.construct s8 e_v60 (by rw [he_v60]; exact empty_args) hinv8 h64 as ⟨v60, s9, hinv9, h_v60⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a7 h_v56 h_v58 h_v59 dropping h_a6 h_v4 h_v51 h_v53 h_v55 he_v60 hinv8 e_v60 s8 v4 v51 v53 v55
  pat_same v58 v60 with h_v58 h_v60 using hinv9 else hinv9 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_2.case_0
  pat_unapply h_v59 as ⟨v62, v63, x_v62, x_v63, h_v62, h_v63, hn_v62, hn_v63⟩ using hinv9 else hinv9 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_2.case_0
  pat_unapply h_v62 as ⟨v65, v66, x_v65, x_v66, h_v65, h_v66, hn_v65, hn_v66⟩ using hinv9 else hinv9 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_2.case_0
  step as ⟨e_v67, he_v67⟩
  store_step with CtorSpec.eo_bvule.construct s9 e_v67 (by rw [he_v67]; exact empty_args) hinv9 h64 as ⟨v67, s10, hinv10, h_v67⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a7 h_v56 h_v63 h_v65 h_v66 dropping h_v58 h_v59 h_v60 h_v62 he_v67 hinv9 e_v67 s9 v58 v59 v60 v62
  pat_same v65 v67 with h_v65 h_v67 using hinv10 else hinv10 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_2.case_0
  pat_unapply h_v66 as ⟨v69, v70, x_v69, x_v70, h_v69, h_v70, hn_v69, hn_v70⟩ using hinv10 else hinv10 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_2.case_0
  pat_destruct CtorSpec.eo_int_5fto_5fbv.destruct h_v69 as ⟨v72, x_v72, h_v72⟩ else hinv10 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_2.case_0
  obtain hn_v72 := CtorSpec.eo_int_5fto_5fbv.fields_ne_stuck hinv10 h_v69
  pat_same v72 a3 with h_v72 h_a3 using hinv10 else hinv10 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_2.case_0
  pat_same v70 a2 with h_v70 h_a2 using hinv10 else hinv10 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_2.case_0
  pat_unapply h_v63 as ⟨v74, v75, x_v74, x_v75, h_v74, h_v75, hn_v74, hn_v75⟩ using hinv10 else hinv10 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_2.case_0
  pat_unapply h_v74 as ⟨v77, v78, x_v77, x_v78, h_v77, h_v78, hn_v77, hn_v78⟩ using hinv10 else hinv10 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_2.case_0
  step as ⟨e_v79, he_v79⟩
  store_step with CtorSpec.eo_bvshl.construct s10 e_v79 (by rw [he_v79]; exact empty_args) hinv10 h64 as ⟨v79, s11, hinv11, h_v79⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a7 h_v56 h_v75 h_v77 h_v78 dropping h_v63 h_v65 h_v66 h_v67 h_v69 h_v70 h_v72 h_v74 he_v79 hinv10 e_v79 s10 v63 v65 v66 v67 v69 v70 v72 v74
  pat_same v77 v79 with h_v77 h_v79 using hinv11 else hinv11 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_2.case_0
  pat_unapply h_v78 as ⟨v81, v82, x_v81, x_v82, h_v81, h_v82, hn_v81, hn_v82⟩ using hinv11 else hinv11 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_2.case_0
  step as ⟨e_v83, he_v83⟩
  store_step with CtorSpec.eo_bvnot.construct s11 e_v83 (by rw [he_v83]; exact empty_args) hinv11 h64 as ⟨v83, s12, hinv12, h_v83⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a7 h_v56 h_v75 h_v81 h_v82 dropping h_v77 h_v78 h_v79 he_v83 hinv11 e_v83 s11 v77 v78 v79
  pat_same v81 v83 with h_v81 h_v83 using hinv12 else hinv12 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_2.case_0
  pat_unapply h_v82 as ⟨v85, v86, x_v85, x_v86, h_v85, h_v86, hn_v85, hn_v86⟩ using hinv12 else hinv12 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_2.case_0
  pat_destruct CtorSpec.eo_int_5fto_5fbv.destruct h_v85 as ⟨v88, x_v88, h_v88⟩ else hinv12 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_2.case_0
  obtain hn_v88 := CtorSpec.eo_int_5fto_5fbv.fields_ne_stuck hinv12 h_v85
  pat_same v88 a3 with h_v88 h_a3 using hinv12 else hinv12 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_2.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s12 0#u32 (0) (by scalar_tac) hinv12 h64 as ⟨v89, s13, hinv13, h_v89⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a7 h_v56 h_v75 h_v86 dropping h_v81 h_v82 h_v83 h_v85 h_v88 hinv12 s12 v81 v82 v83 v85 v88
  pat_same v86 v89 with h_v86 h_v89 using hinv13 else hinv13 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_2.case_0
  pat_unapply h_v75 as ⟨v91, v92, x_v91, x_v92, h_v91, h_v92, hn_v91, hn_v92⟩ using hinv13 else hinv13 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_2.case_0
  pat_destruct CtorSpec.eo_int_5fto_5fbv.destruct h_v91 as ⟨v94, x_v94, h_v94⟩ else hinv13 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_2.case_0
  obtain hn_v94 := CtorSpec.eo_int_5fto_5fbv.fields_ne_stuck hinv13 h_v91
  pat_same v94 a3 with h_v94 h_a3 using hinv13 else hinv13 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_2.case_0
  pat_unapply h_v92 as ⟨v96, v97, x_v96, x_v97, h_v96, h_v97, hn_v96, hn_v97⟩ using hinv13 else hinv13 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_2.case_0
  pat_unapply h_v96 as ⟨v99, v100, x_v99, x_v100, h_v99, h_v100, hn_v99, hn_v100⟩ using hinv13 else hinv13 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_2.case_0
  step as ⟨e_v101, he_v101⟩
  store_step with CtorSpec.eo__2d.construct s13 e_v101 (by rw [he_v101]; exact empty_args) hinv13 h64 as ⟨v101, s14, hinv14, h_v101⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a7 h_v56 h_v97 h_v99 h_v100 dropping h_v75 h_v86 h_v89 h_v91 h_v92 h_v94 h_v96 he_v101 hinv13 e_v101 s13 v75 v86 v89 v91 v92 v94 v96
  pat_same v99 v101 with h_v99 h_v101 using hinv14 else hinv14 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_2.case_0
  pat_unapply h_v100 as ⟨v103, v104, x_v103, x_v104, h_v103, h_v104, hn_v103, hn_v104⟩ using hinv14 else hinv14 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_2.case_0
  step as ⟨e_v105, he_v105⟩
  store_step with CtorSpec.eo__40bvsize.construct s14 e_v105 (by rw [he_v105]; exact empty_args) hinv14 h64 as ⟨v105, s15, hinv15, h_v105⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a7 h_v56 h_v97 h_v103 h_v104 dropping h_v100 h_v101 h_v99 he_v105 hinv14 e_v105 s14 v100 v101 v99
  pat_same v103 v105 with h_v103 h_v105 using hinv15 else hinv15 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_2.case_0
  pat_same v104 a0 with h_v104 h_a0 using hinv15 else hinv15 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_2.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s15 1#u32 (1) (by scalar_tac) hinv15 h64 as ⟨v106, s16, hinv16, h_v106⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a7 h_v56 h_v97 dropping h_v103 h_v104 h_v105 hinv15 s15 v103 v104 v105
  pat_same v97 v106 with h_v97 h_v106 using hinv16 else hinv16 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_2.case_0
  store_step with Store.literal_boolean_spec s16 true hinv16 h64 as ⟨v107, s17, hinv17, h_v107⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a7 h_v56 dropping h_v106 h_v97 hinv16 s16 v106 v97
  pat_same v56 v107 with h_v56 h_v107 using hinv17 else hinv17 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_2.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a7 as ⟨v109, x_v109, h_v109⟩ else hinv17 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_2.case_0
  pat_unapply h_v109 as ⟨v111, v112, x_v111, x_v112, h_v111, h_v112, hn_v111, hn_v112⟩ using hinv17 else hinv17 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_2.case_0
  pat_unapply h_v111 as ⟨v114, v115, x_v114, x_v115, h_v114, h_v115, hn_v114, hn_v115⟩ using hinv17 else hinv17 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_2.case_0
  step as ⟨e_v116, he_v116⟩
  store_step with CtorSpec.eo__3d.construct s17 e_v116 (by rw [he_v116]; exact empty_args) hinv17 h64 as ⟨v116, s18, hinv18, h_v116⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v112 h_v114 h_v115 dropping h_a7 h_v107 h_v109 h_v111 h_v56 he_v116 hinv17 e_v116 s17 v107 v109 v111 v56
  pat_same v114 v116 with h_v114 h_v116 using hinv18 else hinv18 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_2.case_0
  pat_same v115 a4 with h_v115 h_a4 using hinv18 else hinv18 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_2.case_0
  pat_unapply h_v112 as ⟨v118, v119, x_v118, x_v119, h_v118, h_v119, hn_v118, hn_v119⟩ using hinv18 else hinv18 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_2.case_0
  pat_unapply h_v118 as ⟨v121, v122, x_v121, x_v122, h_v121, h_v122, hn_v121, hn_v122⟩ using hinv18 else hinv18 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_2.case_0
  step as ⟨e_v123, he_v123⟩
  store_step with CtorSpec.eo__2d.construct s18 e_v123 (by rw [he_v123]; exact empty_args) hinv18 h64 as ⟨v123, s19, hinv19, h_v123⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v119 h_v121 h_v122 dropping h_v112 h_v114 h_v115 h_v116 h_v118 he_v123 hinv18 e_v123 s18 v112 v114 v115 v116 v118
  pat_same v121 v123 with h_v121 h_v123 using hinv19 else hinv19 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_2.case_0
  pat_unapply h_v122 as ⟨v125, v126, x_v125, x_v126, h_v125, h_v126, hn_v125, hn_v126⟩ using hinv19 else hinv19 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_2.case_0
  step as ⟨e_v127, he_v127⟩
  store_step with CtorSpec.eo__40bvsize.construct s19 e_v127 (by rw [he_v127]; exact empty_args) hinv19 h64 as ⟨v127, s20, hinv20, h_v127⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v119 h_v125 h_v126 dropping h_v121 h_v122 h_v123 he_v127 hinv19 e_v127 s19 v121 v122 v123
  pat_same v125 v127 with h_v125 h_v127 using hinv20 else hinv20 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_2.case_0
  pat_same v126 a0 with h_v126 h_a0 using hinv20 else hinv20 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_2.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s20 1#u32 (1) (by scalar_tac) hinv20 h64 as ⟨v128, s21, hinv21, h_v128⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v119 dropping h_v125 h_v126 h_v127 hinv20 s20 v125 v126 v127
  pat_same v119 v128 with h_v119 h_v128 using hinv21 else hinv21 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_2.case_0
  step as ⟨e_v129, he_v129⟩
  store_step with CtorSpec.eo__3d.construct s21 e_v129 (by rw [he_v129]; exact empty_args) hinv21 h64 as ⟨v129, s22, hinv22, h_v129⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 dropping h_v119 h_v128 he_v129 hinv21 e_v129 s21 v119 v128
  step as ⟨e_v130, he_v130⟩
  store_step with CtorSpec.eo_bvult.construct s22 e_v130 (by rw [he_v130]; exact empty_args) hinv22 h64 as ⟨v130, s23, hinv23, h_v130⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v129 dropping he_v130 hinv22 e_v130 s22
  step as ⟨e_v131, he_v131⟩
  store_step with CtorSpec.eo_sign_5fextend.construct s23 e_v131 (by rw [he_v131]; rfl) h_a1 hinv23 h64 as ⟨v131, s24, hinv24, h_v131⟩ growing hG carrying h_a0 h_a2 h_a3 h_a4 h_v129 h_v130 dropping h_a1 he_v131 hinv23 e_v131 s23
  store_step with Store.apply_rep s24 v131 a0 _ _ hinv24 h64 h_v131 h_a0 (by ns_tac) (by ns_tac) as ⟨v132, s25, hinv25, h_v132⟩ growing hG carrying h_a0 h_a2 h_a3 h_a4 h_v129 h_v130 dropping h_v131 hinv24 s24 v131
  store_step with Store.apply_rep s25 v130 v132 _ _ hinv25 h64 h_v130 h_v132 (by ns_tac) (by ns_tac) as ⟨v133, s26, hinv26, h_v133⟩ growing hG carrying h_a0 h_a2 h_a3 h_a4 h_v129 dropping h_v130 h_v132 hinv25 s25 v130 v132
  step as ⟨e_v134, he_v134⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s26 e_v134 (by rw [he_v134]; rfl) h_a3 hinv26 h64 as ⟨v134, s27, hinv27, h_v134⟩ growing hG carrying h_a0 h_a2 h_a4 h_v129 h_v133 dropping h_a3 he_v134 hinv26 e_v134 s26
  store_step with Store.apply_rep s27 v134 a2 _ _ hinv27 h64 h_v134 h_a2 (by ns_tac) (by ns_tac) as ⟨v135, s28, hinv28, h_v135⟩ growing hG carrying h_a0 h_a4 h_v129 h_v133 dropping h_a2 h_v134 hinv27 s27 v134
  store_step with Store.apply_rep s28 v133 v135 _ _ hinv28 h64 h_v133 h_v135 (by ns_tac) (by ns_tac) as ⟨v136, s29, hinv29, h_v136⟩ growing hG carrying h_a0 h_a4 h_v129 dropping h_v133 h_v135 hinv28 s28 v133 v135
  store_step with Store.apply_rep s29 v129 v136 _ _ hinv29 h64 h_v129 h_v136 (by ns_tac) (by ns_tac) as ⟨v137, s30, hinv30, h_v137⟩ growing hG carrying h_a0 h_a4 dropping h_v129 h_v136 hinv29 s29 v129 v136
  step as ⟨e_v138, he_v138⟩
  store_step with CtorSpec.eo__3d.construct s30 e_v138 (by rw [he_v138]; exact empty_args) hinv30 h64 as ⟨v138, s31, hinv31, h_v138⟩ growing hG carrying h_a0 h_a4 h_v137 dropping he_v138 hinv30 e_v138 s30
  step as ⟨e_v139, he_v139⟩
  store_step with CtorSpec.eo_extract.construct s31 e_v139 (by rw [he_v139]; rfl) h_a4 h_a4 hinv31 h64 as ⟨v139, s32, hinv32, h_v139⟩ growing hG carrying h_a0 h_v137 h_v138 dropping h_a4 he_v139 hinv31 e_v139 s31
  store_step with Store.apply_rep s32 v139 a0 _ _ hinv32 h64 h_v139 h_a0 (by ns_tac) (by ns_tac) as ⟨v140, s33, hinv33, h_v140⟩ growing hG carrying h_v137 h_v138 dropping h_a0 h_v139 hinv32 s32 v139
  store_step with Store.apply_rep s33 v138 v140 _ _ hinv33 h64 h_v138 h_v140 (by ns_tac) (by ns_tac) as ⟨v141, s34, hinv34, h_v141⟩ growing hG carrying h_v137 dropping h_v138 h_v140 hinv33 s33 v138 v140
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s34 1#u32 (1) (by scalar_tac) hinv34 h64 as ⟨v142, s35, hinv35, h_v142⟩ growing hG carrying h_v137 h_v141 dropping hinv34 s34
  step as ⟨e_v143, he_v143⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s35 e_v143 (by rw [he_v143]; rfl) h_v142 hinv35 h64 as ⟨v143, s36, hinv36, h_v143⟩ growing hG carrying h_v137 h_v141 dropping h_v142 he_v143 hinv35 e_v143 s35 v142
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s36 0#u32 (0) (by scalar_tac) hinv36 h64 as ⟨v144, s37, hinv37, h_v144⟩ growing hG carrying h_v137 h_v141 h_v143 dropping hinv36 s36
  store_step with Store.apply_rep s37 v143 v144 _ _ hinv37 h64 h_v143 h_v144 (by ns_tac) (by ns_tac) as ⟨v145, s38, hinv38, h_v145⟩ growing hG carrying h_v137 h_v141 dropping h_v143 h_v144 hinv37 s37 v143 v144
  store_step with Store.apply_rep s38 v141 v145 _ _ hinv38 h64 h_v141 h_v145 (by ns_tac) (by ns_tac) as ⟨v146, s39, hinv39, h_v146⟩ growing hG carrying h_v137 dropping h_v141 h_v145 hinv38 s38 v141 v145
  store_step with Store.apply_rep s39 v137 v146 _ _ hinv39 h64 h_v137 h_v146 (by ns_tac) (by ns_tac) as ⟨v147, s40, hinv40, h_v147⟩ growing hG carrying dropping h_v137 h_v146 hinv39 s39 v137 v146
  case_done hinv40 hG with h_v147 in EoCases.__eo_prog_bv_sign_extend_ult_const_2.case_0 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v13 hn_v14 hn_v17 hn_v18 hn_v20 hn_v21 hn_v24 hn_v25 hn_v27 hn_v30 hn_v31 hn_v33 hn_v35 hn_v36 hn_v38 hn_v39 hn_v42 hn_v43 hn_v47 hn_v48 hn_v50 hn_v55 hn_v56 hn_v58 hn_v59 hn_v62 hn_v63 hn_v65 hn_v66 hn_v69 hn_v70 hn_v72 hn_v74 hn_v75 hn_v77 hn_v78 hn_v81 hn_v82 hn_v85 hn_v86 hn_v88 hn_v91 hn_v92 hn_v94 hn_v96 hn_v97 hn_v99 hn_v100 hn_v103 hn_v104 hn_v111 hn_v112 hn_v114 hn_v115 hn_v118 hn_v119 hn_v121 hn_v122 hn_v125 hn_v126

set_option maxHeartbeats 20000000 in
/-- logos's `__eo_prog_bv_sign_extend_ult_const_2` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d2.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _) (x_a7 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) (hw_a4 : Valid.valid x_a4) (hw_a5 : Valid.valid x_a5) (hw_a6 : Valid.valid x_a6) (hw_a7 : Valid.valid x_a7) :
    __eo_prog_bv_sign_extend_ult_const_2 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else if x_a4 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_bv_sign_extend_ult_const_2.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_bv_sign_extend_ult_const_2
  unfold EoCases.__eo_prog_bv_sign_extend_ult_const_2.case_0
  logos_eq

set_option maxHeartbeats 20000000 in
theorem body_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d2_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 a6 a7 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _) (x_a7 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) (h_a6 : Represents.rep s a6 x_a6) (h_a7 : Represents.rep s a7 x_a7) :
    body_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d2 s a0 a1 a2 a3 a4 a5 a6 a7 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_sign_extend_ult_const_2 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d2.rust_eq x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3) (by valid_tac hinv h_a4) (by valid_tac hinv h_a5) (by valid_tac hinv h_a6) (by valid_tac hinv h_a7)]
  unfold body_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d2
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  stuck_check h_a3 : x_a3 as hn_a3 else hinv hG
  stuck_check h_a4 : x_a4 as hn_a4 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d2_spec n ih s a0 a1 a2 a3 a4 a5 a6 a7 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 hn_a0 hn_a1 hn_a2 hn_a3 hn_a4
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hc0 in EoCases.__eo_prog_bv_sign_extend_ult_const_2.case_0

set_option maxHeartbeats 20000000 in
theorem eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d2_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d2.Spec n := by
  intro s a0 a1 a2 a3 a4 a5 a6 a7 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7
  unfold eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d2
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d2 s1 a0 a1 a2 a3 a4 a5 a6 a7) (fun s' t => Represents.rep s' t (__eo_prog_bv_sign_extend_ult_const_2 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d2_spec m (ih m hm) s1 a0 a1 a2 a3 a4 a5 a6 a7 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn) (by congr_one h_a4 hn) (by congr_one h_a5 hn) (by congr_one h_a6 hn) (by congr_one h_a7 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

end pathos_compiled_checker
