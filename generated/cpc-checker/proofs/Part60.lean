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

set_option maxHeartbeats 4000000 in
theorem case_0_eo__24eo_5fprog_5fbv_2dsign_2dextend_2deq_2dconst_2d2_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _) (x_a7 : _) (x_a8 : _) (x_a9 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) (h_a6 : Represents.rep s a6 x_a6) (h_a7 : Represents.rep s a7 x_a7) (h_a8 : Represents.rep s a8 x_a8) (h_a9 : Represents.rep s a9 x_a9) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) (hn_a4 : x_a4 ≠ Eo.Term.Stuck) (hn_a5 : x_a5 ≠ Eo.Term.Stuck) (hn_a6 : x_a6 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fbv_2dsign_2dextend_2deq_2dconst_2d2 s a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_bv_sign_extend_eq_const_2.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 x_a9 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_bv_sign_extend_eq_const_2.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 x_a9 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fbv_2dsign_2dextend_2deq_2dconst_2d2
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a7 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_bv_sign_extend_eq_const_2.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_sign_extend_eq_const_2.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_sign_extend_eq_const_2.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a8 h_a9 h_v4 h_v6 h_v7 dropping h_a7 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_sign_extend_eq_const_2.case_0
  pat_same v7 a4 with h_v7 h_a4 using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_sign_extend_eq_const_2.case_0
  pat_unapply h_v4 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_sign_extend_eq_const_2.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_sign_extend_eq_const_2.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__2b.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a8 h_a9 h_v11 h_v13 h_v14 dropping h_v10 h_v4 h_v6 h_v7 h_v8 he_v15 hinv1 e_v15 s1 v10 v4 v6 v7 v8
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_sign_extend_eq_const_2.case_0
  pat_same v14 a1 with h_v14 h_a1 using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_sign_extend_eq_const_2.case_0
  pat_unapply h_v11 as ⟨v17, v18, x_v17, x_v18, h_v17, h_v18, hn_v17, hn_v18⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_sign_extend_eq_const_2.case_0
  pat_unapply h_v17 as ⟨v20, v21, x_v20, x_v21, h_v20, h_v21, hn_v20, hn_v21⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_sign_extend_eq_const_2.case_0
  step as ⟨e_v22, he_v22⟩
  store_step with CtorSpec.eo__2b.construct s2 e_v22 (by rw [he_v22]; exact empty_args) hinv2 h64 as ⟨v22, s3, hinv3, h_v22⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a8 h_a9 h_v18 h_v20 h_v21 dropping h_v11 h_v13 h_v14 h_v15 h_v17 he_v22 hinv2 e_v22 s2 v11 v13 v14 v15 v17
  pat_same v20 v22 with h_v20 h_v22 using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_sign_extend_eq_const_2.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s3 1#u32 (1) (by scalar_tac) hinv3 h64 as ⟨v23, s4, hinv4, h_v23⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a8 h_a9 h_v18 h_v21 dropping h_v20 h_v22 hinv3 s3 v20 v22
  pat_same v21 v23 with h_v21 h_v23 using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_sign_extend_eq_const_2.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s4 0#u32 (0) (by scalar_tac) hinv4 h64 as ⟨v24, s5, hinv5, h_v24⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a8 h_a9 h_v18 dropping h_v21 h_v23 hinv4 s4 v21 v23
  pat_same v18 v24 with h_v18 h_v24 using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_sign_extend_eq_const_2.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a8 as ⟨v26, x_v26, h_v26⟩ else hinv5 hG in EoCases.__eo_prog_bv_sign_extend_eq_const_2.case_0
  pat_unapply h_v26 as ⟨v28, v29, x_v28, x_v29, h_v28, h_v29, hn_v28, hn_v29⟩ using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_sign_extend_eq_const_2.case_0
  pat_unapply h_v28 as ⟨v31, v32, x_v31, x_v32, h_v31, h_v32, hn_v31, hn_v32⟩ using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_sign_extend_eq_const_2.case_0
  step as ⟨e_v33, he_v33⟩
  store_step with CtorSpec.eo__3d.construct s5 e_v33 (by rw [he_v33]; exact empty_args) hinv5 h64 as ⟨v33, s6, hinv6, h_v33⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a9 h_v29 h_v31 h_v32 dropping h_a8 h_v18 h_v24 h_v26 h_v28 he_v33 hinv5 e_v33 s5 v18 v24 v26 v28
  pat_same v31 v33 with h_v31 h_v33 using hinv6 else hinv6 hG in EoCases.__eo_prog_bv_sign_extend_eq_const_2.case_0
  pat_same v32 a5 with h_v32 h_a5 using hinv6 else hinv6 hG in EoCases.__eo_prog_bv_sign_extend_eq_const_2.case_0
  pat_unapply h_v29 as ⟨v35, v36, x_v35, x_v36, h_v35, h_v36, hn_v35, hn_v36⟩ using hinv6 else hinv6 hG in EoCases.__eo_prog_bv_sign_extend_eq_const_2.case_0
  pat_unapply h_v35 as ⟨v38, v39, x_v38, x_v39, h_v38, h_v39, hn_v38, hn_v39⟩ using hinv6 else hinv6 hG in EoCases.__eo_prog_bv_sign_extend_eq_const_2.case_0
  step as ⟨e_v40, he_v40⟩
  store_step with CtorSpec.eo__2d.construct s6 e_v40 (by rw [he_v40]; exact empty_args) hinv6 h64 as ⟨v40, s7, hinv7, h_v40⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a9 h_v36 h_v38 h_v39 dropping h_v29 h_v31 h_v32 h_v33 h_v35 he_v40 hinv6 e_v40 s6 v29 v31 v32 v33 v35
  pat_same v38 v40 with h_v38 h_v40 using hinv7 else hinv7 hG in EoCases.__eo_prog_bv_sign_extend_eq_const_2.case_0
  pat_unapply h_v39 as ⟨v42, v43, x_v42, x_v43, h_v42, h_v43, hn_v42, hn_v43⟩ using hinv7 else hinv7 hG in EoCases.__eo_prog_bv_sign_extend_eq_const_2.case_0
  step as ⟨e_v44, he_v44⟩
  store_step with CtorSpec.eo__40bvsize.construct s7 e_v44 (by rw [he_v44]; exact empty_args) hinv7 h64 as ⟨v44, s8, hinv8, h_v44⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a9 h_v36 h_v42 h_v43 dropping h_v38 h_v39 h_v40 he_v44 hinv7 e_v44 s7 v38 v39 v40
  pat_same v42 v44 with h_v42 h_v44 using hinv8 else hinv8 hG in EoCases.__eo_prog_bv_sign_extend_eq_const_2.case_0
  pat_same v43 a0 with h_v43 h_a0 using hinv8 else hinv8 hG in EoCases.__eo_prog_bv_sign_extend_eq_const_2.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s8 1#u32 (1) (by scalar_tac) hinv8 h64 as ⟨v45, s9, hinv9, h_v45⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a9 h_v36 dropping h_v42 h_v43 h_v44 hinv8 s8 v42 v43 v44
  pat_same v36 v45 with h_v36 h_v45 using hinv9 else hinv9 hG in EoCases.__eo_prog_bv_sign_extend_eq_const_2.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a9 as ⟨v47, x_v47, h_v47⟩ else hinv9 hG in EoCases.__eo_prog_bv_sign_extend_eq_const_2.case_0
  pat_unapply h_v47 as ⟨v49, v50, x_v49, x_v50, h_v49, h_v50, hn_v49, hn_v50⟩ using hinv9 else hinv9 hG in EoCases.__eo_prog_bv_sign_extend_eq_const_2.case_0
  pat_unapply h_v49 as ⟨v52, v53, x_v52, x_v53, h_v52, h_v53, hn_v52, hn_v53⟩ using hinv9 else hinv9 hG in EoCases.__eo_prog_bv_sign_extend_eq_const_2.case_0
  step as ⟨e_v54, he_v54⟩
  store_step with CtorSpec.eo__3d.construct s9 e_v54 (by rw [he_v54]; exact empty_args) hinv9 h64 as ⟨v54, s10, hinv10, h_v54⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v50 h_v52 h_v53 dropping h_a9 h_v36 h_v45 h_v47 h_v49 he_v54 hinv9 e_v54 s9 v36 v45 v47 v49
  pat_same v52 v54 with h_v52 h_v54 using hinv10 else hinv10 hG in EoCases.__eo_prog_bv_sign_extend_eq_const_2.case_0
  pat_same v53 a6 with h_v53 h_a6 using hinv10 else hinv10 hG in EoCases.__eo_prog_bv_sign_extend_eq_const_2.case_0
  pat_unapply h_v50 as ⟨v56, v57, x_v56, x_v57, h_v56, h_v57, hn_v56, hn_v57⟩ using hinv10 else hinv10 hG in EoCases.__eo_prog_bv_sign_extend_eq_const_2.case_0
  pat_unapply h_v56 as ⟨v59, v60, x_v59, x_v60, h_v59, h_v60, hn_v59, hn_v60⟩ using hinv10 else hinv10 hG in EoCases.__eo_prog_bv_sign_extend_eq_const_2.case_0
  step as ⟨e_v61, he_v61⟩
  store_step with CtorSpec.eo__2d.construct s10 e_v61 (by rw [he_v61]; exact empty_args) hinv10 h64 as ⟨v61, s11, hinv11, h_v61⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v57 h_v59 h_v60 dropping h_v50 h_v52 h_v53 h_v54 h_v56 he_v61 hinv10 e_v61 s10 v50 v52 v53 v54 v56
  pat_same v59 v61 with h_v59 h_v61 using hinv11 else hinv11 hG in EoCases.__eo_prog_bv_sign_extend_eq_const_2.case_0
  pat_same v60 a3 with h_v60 h_a3 using hinv11 else hinv11 hG in EoCases.__eo_prog_bv_sign_extend_eq_const_2.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s11 1#u32 (1) (by scalar_tac) hinv11 h64 as ⟨v62, s12, hinv12, h_v62⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v57 dropping h_v59 h_v60 h_v61 hinv11 s11 v59 v60 v61
  pat_same v57 v62 with h_v57 h_v62 using hinv12 else hinv12 hG in EoCases.__eo_prog_bv_sign_extend_eq_const_2.case_0
  step as ⟨e_v63, he_v63⟩
  store_step with CtorSpec.eo__3d.construct s12 e_v63 (by rw [he_v63]; exact empty_args) hinv12 h64 as ⟨v63, s13, hinv13, h_v63⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 dropping h_v57 h_v62 he_v63 hinv12 e_v63 s12 v57 v62
  step as ⟨e_v64, he_v64⟩
  store_step with CtorSpec.eo__3d.construct s13 e_v64 (by rw [he_v64]; exact empty_args) hinv13 h64 as ⟨v64, s14, hinv14, h_v64⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v63 dropping he_v64 hinv13 e_v64 s13
  step as ⟨e_v65, he_v65⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s14 e_v65 (by rw [he_v65]; rfl) h_a3 hinv14 h64 as ⟨v65, s15, hinv15, h_v65⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v63 h_v64 dropping he_v65 hinv14 e_v65 s14
  store_step with Store.apply_rep s15 v65 a2 _ _ hinv15 h64 h_v65 h_a2 (by ns_tac) (by ns_tac) as ⟨v66, s16, hinv16, h_v66⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v63 h_v64 dropping h_v65 hinv15 s15 v65
  store_step with Store.apply_rep s16 v64 v66 _ _ hinv16 h64 h_v64 h_v66 (by ns_tac) (by ns_tac) as ⟨v67, s17, hinv17, h_v67⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v63 dropping h_v64 h_v66 hinv16 s16 v64 v66
  step as ⟨e_v68, he_v68⟩
  store_step with CtorSpec.eo_sign_5fextend.construct s17 e_v68 (by rw [he_v68]; rfl) h_a1 hinv17 h64 as ⟨v68, s18, hinv18, h_v68⟩ growing hG carrying h_a0 h_a2 h_a3 h_a4 h_a5 h_a6 h_v63 h_v67 dropping h_a1 he_v68 hinv17 e_v68 s17
  store_step with Store.apply_rep s18 v68 a0 _ _ hinv18 h64 h_v68 h_a0 (by ns_tac) (by ns_tac) as ⟨v69, s19, hinv19, h_v69⟩ growing hG carrying h_a0 h_a2 h_a3 h_a4 h_a5 h_a6 h_v63 h_v67 dropping h_v68 hinv18 s18 v68
  store_step with Store.apply_rep s19 v67 v69 _ _ hinv19 h64 h_v67 h_v69 (by ns_tac) (by ns_tac) as ⟨v70, s20, hinv20, h_v70⟩ growing hG carrying h_a0 h_a2 h_a3 h_a4 h_a5 h_a6 h_v63 dropping h_v67 h_v69 hinv19 s19 v67 v69
  store_step with Store.apply_rep s20 v63 v70 _ _ hinv20 h64 h_v63 h_v70 (by ns_tac) (by ns_tac) as ⟨v71, s21, hinv21, h_v71⟩ growing hG carrying h_a0 h_a2 h_a3 h_a4 h_a5 h_a6 dropping h_v63 h_v70 hinv20 s20 v63 v70
  step as ⟨e_v72, he_v72⟩
  store_step with CtorSpec.eo_and.construct s21 e_v72 (by rw [he_v72]; exact empty_args) hinv21 h64 as ⟨v72, s22, hinv22, h_v72⟩ growing hG carrying h_a0 h_a2 h_a3 h_a4 h_a5 h_a6 h_v71 dropping he_v72 hinv21 e_v72 s21
  step as ⟨e_v73, he_v73⟩
  store_step with CtorSpec.eo_or.construct s22 e_v73 (by rw [he_v73]; exact empty_args) hinv22 h64 as ⟨v73, s23, hinv23, h_v73⟩ growing hG carrying h_a0 h_a2 h_a3 h_a4 h_a5 h_a6 h_v71 h_v72 dropping he_v73 hinv22 e_v73 s22
  step as ⟨e_v74, he_v74⟩
  store_step with CtorSpec.eo__3d.construct s23 e_v74 (by rw [he_v74]; exact empty_args) hinv23 h64 as ⟨v74, s24, hinv24, h_v74⟩ growing hG carrying h_a0 h_a2 h_a3 h_a4 h_a5 h_a6 h_v71 h_v72 h_v73 dropping he_v74 hinv23 e_v74 s23
  step as ⟨e_v75, he_v75⟩
  store_step with CtorSpec.eo_extract.construct s24 e_v75 (by rw [he_v75]; rfl) h_a6 h_a5 hinv24 h64 as ⟨v75, s25, hinv25, h_v75⟩ growing hG carrying h_a0 h_a2 h_a3 h_a4 h_a5 h_a6 h_v71 h_v72 h_v73 h_v74 dropping he_v75 hinv24 e_v75 s24
  step as ⟨e_v76, he_v76⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s25 e_v76 (by rw [he_v76]; rfl) h_a3 hinv25 h64 as ⟨v76, s26, hinv26, h_v76⟩ growing hG carrying h_a0 h_a2 h_a3 h_a4 h_a5 h_a6 h_v71 h_v72 h_v73 h_v74 h_v75 dropping he_v76 hinv25 e_v76 s25
  store_step with Store.apply_rep s26 v76 a2 _ _ hinv26 h64 h_v76 h_a2 (by ns_tac) (by ns_tac) as ⟨v77, s27, hinv27, h_v77⟩ growing hG carrying h_a0 h_a2 h_a3 h_a4 h_a5 h_a6 h_v71 h_v72 h_v73 h_v74 h_v75 dropping h_v76 hinv26 s26 v76
  store_step with Store.apply_rep s27 v75 v77 _ _ hinv27 h64 h_v75 h_v77 (by ns_tac) (by ns_tac) as ⟨v78, s28, hinv28, h_v78⟩ growing hG carrying h_a0 h_a2 h_a3 h_a4 h_a5 h_a6 h_v71 h_v72 h_v73 h_v74 dropping h_v75 h_v77 hinv27 s27 v75 v77
  store_step with Store.apply_rep s28 v74 v78 _ _ hinv28 h64 h_v74 h_v78 (by ns_tac) (by ns_tac) as ⟨v79, s29, hinv29, h_v79⟩ growing hG carrying h_a0 h_a2 h_a3 h_a4 h_a5 h_a6 h_v71 h_v72 h_v73 dropping h_v74 h_v78 hinv28 s28 v74 v78
  step as ⟨e_v80, he_v80⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s29 e_v80 (by rw [he_v80]; rfl) h_a4 hinv29 h64 as ⟨v80, s30, hinv30, h_v80⟩ growing hG carrying h_a0 h_a2 h_a3 h_a4 h_a5 h_a6 h_v71 h_v72 h_v73 h_v79 dropping he_v80 hinv29 e_v80 s29
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s30 0#u32 (0) (by scalar_tac) hinv30 h64 as ⟨v81, s31, hinv31, h_v81⟩ growing hG carrying h_a0 h_a2 h_a3 h_a4 h_a5 h_a6 h_v71 h_v72 h_v73 h_v79 h_v80 dropping hinv30 s30
  store_step with Store.apply_rep s31 v80 v81 _ _ hinv31 h64 h_v80 h_v81 (by ns_tac) (by ns_tac) as ⟨v82, s32, hinv32, h_v82⟩ growing hG carrying h_a0 h_a2 h_a3 h_a4 h_a5 h_a6 h_v71 h_v72 h_v73 h_v79 dropping h_v80 h_v81 hinv31 s31 v80 v81
  store_step with Store.apply_rep s32 v79 v82 _ _ hinv32 h64 h_v79 h_v82 (by ns_tac) (by ns_tac) as ⟨v83, s33, hinv33, h_v83⟩ growing hG carrying h_a0 h_a2 h_a3 h_a4 h_a5 h_a6 h_v71 h_v72 h_v73 dropping h_v79 h_v82 hinv32 s32 v79 v82
  store_step with Store.apply_rep s33 v73 v83 _ _ hinv33 h64 h_v73 h_v83 (by ns_tac) (by ns_tac) as ⟨v84, s34, hinv34, h_v84⟩ growing hG carrying h_a0 h_a2 h_a3 h_a4 h_a5 h_a6 h_v71 h_v72 dropping h_v73 h_v83 hinv33 s33 v73 v83
  step as ⟨e_v85, he_v85⟩
  store_step with CtorSpec.eo_or.construct s34 e_v85 (by rw [he_v85]; exact empty_args) hinv34 h64 as ⟨v85, s35, hinv35, h_v85⟩ growing hG carrying h_a0 h_a2 h_a3 h_a4 h_a5 h_a6 h_v71 h_v72 h_v84 dropping he_v85 hinv34 e_v85 s34
  step as ⟨e_v86, he_v86⟩
  store_step with CtorSpec.eo__3d.construct s35 e_v86 (by rw [he_v86]; exact empty_args) hinv35 h64 as ⟨v86, s36, hinv36, h_v86⟩ growing hG carrying h_a0 h_a2 h_a3 h_a4 h_a5 h_a6 h_v71 h_v72 h_v84 h_v85 dropping he_v86 hinv35 e_v86 s35
  step as ⟨e_v87, he_v87⟩
  store_step with CtorSpec.eo_extract.construct s36 e_v87 (by rw [he_v87]; rfl) h_a6 h_a5 hinv36 h64 as ⟨v87, s37, hinv37, h_v87⟩ growing hG carrying h_a0 h_a2 h_a3 h_a4 h_a5 h_v71 h_v72 h_v84 h_v85 h_v86 dropping h_a6 he_v87 hinv36 e_v87 s36
  step as ⟨e_v88, he_v88⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s37 e_v88 (by rw [he_v88]; rfl) h_a3 hinv37 h64 as ⟨v88, s38, hinv38, h_v88⟩ growing hG carrying h_a0 h_a2 h_a3 h_a4 h_a5 h_v71 h_v72 h_v84 h_v85 h_v86 h_v87 dropping he_v88 hinv37 e_v88 s37
  store_step with Store.apply_rep s38 v88 a2 _ _ hinv38 h64 h_v88 h_a2 (by ns_tac) (by ns_tac) as ⟨v89, s39, hinv39, h_v89⟩ growing hG carrying h_a0 h_a2 h_a3 h_a4 h_a5 h_v71 h_v72 h_v84 h_v85 h_v86 h_v87 dropping h_v88 hinv38 s38 v88
  store_step with Store.apply_rep s39 v87 v89 _ _ hinv39 h64 h_v87 h_v89 (by ns_tac) (by ns_tac) as ⟨v90, s40, hinv40, h_v90⟩ growing hG carrying h_a0 h_a2 h_a3 h_a4 h_a5 h_v71 h_v72 h_v84 h_v85 h_v86 dropping h_v87 h_v89 hinv39 s39 v87 v89
  store_step with Store.apply_rep s40 v86 v90 _ _ hinv40 h64 h_v86 h_v90 (by ns_tac) (by ns_tac) as ⟨v91, s41, hinv41, h_v91⟩ growing hG carrying h_a0 h_a2 h_a3 h_a4 h_a5 h_v71 h_v72 h_v84 h_v85 dropping h_v86 h_v90 hinv40 s40 v86 v90
  step as ⟨e_v92, he_v92⟩
  store_step with CtorSpec.eo_bvnot.construct s41 e_v92 (by rw [he_v92]; exact empty_args) hinv41 h64 as ⟨v92, s42, hinv42, h_v92⟩ growing hG carrying h_a0 h_a2 h_a3 h_a4 h_a5 h_v71 h_v72 h_v84 h_v85 h_v91 dropping he_v92 hinv41 e_v92 s41
  step as ⟨e_v93, he_v93⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s42 e_v93 (by rw [he_v93]; rfl) h_a4 hinv42 h64 as ⟨v93, s43, hinv43, h_v93⟩ growing hG carrying h_a0 h_a2 h_a3 h_a5 h_v71 h_v72 h_v84 h_v85 h_v91 h_v92 dropping h_a4 he_v93 hinv42 e_v93 s42
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s43 0#u32 (0) (by scalar_tac) hinv43 h64 as ⟨v94, s44, hinv44, h_v94⟩ growing hG carrying h_a0 h_a2 h_a3 h_a5 h_v71 h_v72 h_v84 h_v85 h_v91 h_v92 h_v93 dropping hinv43 s43
  store_step with Store.apply_rep s44 v93 v94 _ _ hinv44 h64 h_v93 h_v94 (by ns_tac) (by ns_tac) as ⟨v95, s45, hinv45, h_v95⟩ growing hG carrying h_a0 h_a2 h_a3 h_a5 h_v71 h_v72 h_v84 h_v85 h_v91 h_v92 dropping h_v93 h_v94 hinv44 s44 v93 v94
  store_step with Store.apply_rep s45 v92 v95 _ _ hinv45 h64 h_v92 h_v95 (by ns_tac) (by ns_tac) as ⟨v96, s46, hinv46, h_v96⟩ growing hG carrying h_a0 h_a2 h_a3 h_a5 h_v71 h_v72 h_v84 h_v85 h_v91 dropping h_v92 h_v95 hinv45 s45 v92 v95
  store_step with Store.apply_rep s46 v91 v96 _ _ hinv46 h64 h_v91 h_v96 (by ns_tac) (by ns_tac) as ⟨v97, s47, hinv47, h_v97⟩ growing hG carrying h_a0 h_a2 h_a3 h_a5 h_v71 h_v72 h_v84 h_v85 dropping h_v91 h_v96 hinv46 s46 v91 v96
  store_step with Store.apply_rep s47 v85 v97 _ _ hinv47 h64 h_v85 h_v97 (by ns_tac) (by ns_tac) as ⟨v98, s48, hinv48, h_v98⟩ growing hG carrying h_a0 h_a2 h_a3 h_a5 h_v71 h_v72 h_v84 dropping h_v85 h_v97 hinv47 s47 v85 v97
  store_step with Store.literal_boolean_spec s48 false hinv48 h64 as ⟨v99, s49, hinv49, h_v99⟩ growing hG carrying h_a0 h_a2 h_a3 h_a5 h_v71 h_v72 h_v84 h_v98 dropping hinv48 s48
  store_step with Store.apply_rep s49 v98 v99 _ _ hinv49 h64 h_v98 h_v99 (by ns_tac) (by ns_tac) as ⟨v100, s50, hinv50, h_v100⟩ growing hG carrying h_a0 h_a2 h_a3 h_a5 h_v71 h_v72 h_v84 dropping h_v98 h_v99 hinv49 s49 v98 v99
  store_step with Store.apply_rep s50 v84 v100 _ _ hinv50 h64 h_v84 h_v100 (by ns_tac) (by ns_tac) as ⟨v101, s51, hinv51, h_v101⟩ growing hG carrying h_a0 h_a2 h_a3 h_a5 h_v71 h_v72 dropping h_v100 h_v84 hinv50 s50 v100 v84
  store_step with Store.apply_rep s51 v72 v101 _ _ hinv51 h64 h_v72 h_v101 (by ns_tac) (by ns_tac) as ⟨v102, s52, hinv52, h_v102⟩ growing hG carrying h_a0 h_a2 h_a3 h_a5 h_v71 dropping h_v101 h_v72 hinv51 s51 v101 v72
  step as ⟨e_v103, he_v103⟩
  store_step with CtorSpec.eo_and.construct s52 e_v103 (by rw [he_v103]; exact empty_args) hinv52 h64 as ⟨v103, s53, hinv53, h_v103⟩ growing hG carrying h_a0 h_a2 h_a3 h_a5 h_v71 h_v102 dropping he_v103 hinv52 e_v103 s52
  step as ⟨e_v104, he_v104⟩
  store_step with CtorSpec.eo__3d.construct s53 e_v104 (by rw [he_v104]; exact empty_args) hinv53 h64 as ⟨v104, s54, hinv54, h_v104⟩ growing hG carrying h_a0 h_a2 h_a3 h_a5 h_v71 h_v102 h_v103 dropping he_v104 hinv53 e_v104 s53
  store_step with Store.apply_rep s54 v104 a0 _ _ hinv54 h64 h_v104 h_a0 (by ns_tac) (by ns_tac) as ⟨v105, s55, hinv55, h_v105⟩ growing hG carrying h_a2 h_a3 h_a5 h_v71 h_v102 h_v103 dropping h_a0 h_v104 hinv54 s54 v104
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s55 0#u32 (0) (by scalar_tac) hinv55 h64 as ⟨v106, s56, hinv56, h_v106⟩ growing hG carrying h_a2 h_a3 h_a5 h_v71 h_v102 h_v103 h_v105 dropping hinv55 s55
  step as ⟨e_v107, he_v107⟩
  store_step with CtorSpec.eo_extract.construct s56 e_v107 (by rw [he_v107]; rfl) h_a5 h_v106 hinv56 h64 as ⟨v107, s57, hinv57, h_v107⟩ growing hG carrying h_a2 h_a3 h_v71 h_v102 h_v103 h_v105 dropping h_a5 h_v106 he_v107 hinv56 e_v107 s56 v106
  step as ⟨e_v108, he_v108⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s57 e_v108 (by rw [he_v108]; rfl) h_a3 hinv57 h64 as ⟨v108, s58, hinv58, h_v108⟩ growing hG carrying h_a2 h_v71 h_v102 h_v103 h_v105 h_v107 dropping h_a3 he_v108 hinv57 e_v108 s57
  store_step with Store.apply_rep s58 v108 a2 _ _ hinv58 h64 h_v108 h_a2 (by ns_tac) (by ns_tac) as ⟨v109, s59, hinv59, h_v109⟩ growing hG carrying h_v71 h_v102 h_v103 h_v105 h_v107 dropping h_a2 h_v108 hinv58 s58 v108
  store_step with Store.apply_rep s59 v107 v109 _ _ hinv59 h64 h_v107 h_v109 (by ns_tac) (by ns_tac) as ⟨v110, s60, hinv60, h_v110⟩ growing hG carrying h_v71 h_v102 h_v103 h_v105 dropping h_v107 h_v109 hinv59 s59 v107 v109
  store_step with Store.apply_rep s60 v105 v110 _ _ hinv60 h64 h_v105 h_v110 (by ns_tac) (by ns_tac) as ⟨v111, s61, hinv61, h_v111⟩ growing hG carrying h_v71 h_v102 h_v103 dropping h_v105 h_v110 hinv60 s60 v105 v110
  store_step with Store.apply_rep s61 v103 v111 _ _ hinv61 h64 h_v103 h_v111 (by ns_tac) (by ns_tac) as ⟨v112, s62, hinv62, h_v112⟩ growing hG carrying h_v71 h_v102 dropping h_v103 h_v111 hinv61 s61 v103 v111
  store_step with Store.literal_boolean_spec s62 true hinv62 h64 as ⟨v113, s63, hinv63, h_v113⟩ growing hG carrying h_v71 h_v102 h_v112 dropping hinv62 s62
  store_step with Store.apply_rep s63 v112 v113 _ _ hinv63 h64 h_v112 h_v113 (by ns_tac) (by ns_tac) as ⟨v114, s64, hinv64, h_v114⟩ growing hG carrying h_v71 h_v102 dropping h_v112 h_v113 hinv63 s63 v112 v113
  store_step with Store.apply_rep s64 v102 v114 _ _ hinv64 h64 h_v102 h_v114 (by ns_tac) (by ns_tac) as ⟨v115, s65, hinv65, h_v115⟩ growing hG carrying h_v71 dropping h_v102 h_v114 hinv64 s64 v102 v114
  store_step with Store.apply_rep s65 v71 v115 _ _ hinv65 h64 h_v71 h_v115 (by ns_tac) (by ns_tac) as ⟨v116, s66, hinv66, h_v116⟩ growing hG carrying dropping h_v115 h_v71 hinv65 s65 v115 v71
  case_done hinv66 hG with h_v116 in EoCases.__eo_prog_bv_sign_extend_eq_const_2.case_0 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_a5 hn_a6 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v13 hn_v14 hn_v17 hn_v18 hn_v20 hn_v21 hn_v28 hn_v29 hn_v31 hn_v32 hn_v35 hn_v36 hn_v38 hn_v39 hn_v42 hn_v43 hn_v49 hn_v50 hn_v52 hn_v53 hn_v56 hn_v57 hn_v59 hn_v60

set_option maxHeartbeats 4000000 in
/-- logos's `__eo_prog_bv_sign_extend_eq_const_2` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fbv_2dsign_2dextend_2deq_2dconst_2d2.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _) (x_a7 : _) (x_a8 : _) (x_a9 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) (hw_a4 : Valid.valid x_a4) (hw_a5 : Valid.valid x_a5) (hw_a6 : Valid.valid x_a6) (hw_a7 : Valid.valid x_a7) (hw_a8 : Valid.valid x_a8) (hw_a9 : Valid.valid x_a9) :
    __eo_prog_bv_sign_extend_eq_const_2 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 x_a9 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else if x_a4 = Eo.Term.Stuck then HasStuck.stuck else if x_a5 = Eo.Term.Stuck then HasStuck.stuck else if x_a6 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_bv_sign_extend_eq_const_2.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 x_a9] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_bv_sign_extend_eq_const_2
  unfold EoCases.__eo_prog_bv_sign_extend_eq_const_2.case_0
  logos_eq

set_option maxHeartbeats 4000000 in
theorem body_eo__24eo_5fprog_5fbv_2dsign_2dextend_2deq_2dconst_2d2_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _) (x_a7 : _) (x_a8 : _) (x_a9 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) (h_a6 : Represents.rep s a6 x_a6) (h_a7 : Represents.rep s a7 x_a7) (h_a8 : Represents.rep s a8 x_a8) (h_a9 : Represents.rep s a9 x_a9) :
    body_eo__24eo_5fprog_5fbv_2dsign_2dextend_2deq_2dconst_2d2 s a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_sign_extend_eq_const_2 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 x_a9)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fbv_2dsign_2dextend_2deq_2dconst_2d2.rust_eq x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 x_a9 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3) (by valid_tac hinv h_a4) (by valid_tac hinv h_a5) (by valid_tac hinv h_a6) (by valid_tac hinv h_a7) (by valid_tac hinv h_a8) (by valid_tac hinv h_a9)]
  unfold body_eo__24eo_5fprog_5fbv_2dsign_2dextend_2deq_2dconst_2d2
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  stuck_check h_a3 : x_a3 as hn_a3 else hinv hG
  stuck_check h_a4 : x_a4 as hn_a4 else hinv hG
  stuck_check h_a5 : x_a5 as hn_a5 else hinv hG
  stuck_check h_a6 : x_a6 as hn_a6 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fbv_2dsign_2dextend_2deq_2dconst_2d2_spec n ih s a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 x_a9 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 h_a9 hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_a5 hn_a6
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 h_a9 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_a5 hn_a6
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_a5 hn_a6 hc0 in EoCases.__eo_prog_bv_sign_extend_eq_const_2.case_0

set_option maxHeartbeats 4000000 in
theorem eo__24eo_5fprog_5fbv_2dsign_2dextend_2deq_2dconst_2d2_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fbv_2dsign_2dextend_2deq_2dconst_2d2.Spec n := by
  intro s a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 x_a9 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 h_a9
  unfold eo__24eo_5fprog_5fbv_2dsign_2dextend_2deq_2dconst_2d2
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fbv_2dsign_2dextend_2deq_2dconst_2d2 s1 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9) (fun s' t => Represents.rep s' t (__eo_prog_bv_sign_extend_eq_const_2 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 x_a9))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fbv_2dsign_2dextend_2deq_2dconst_2d2_spec m (ih m hm) s1 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 x_a9 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn) (by congr_one h_a4 hn) (by congr_one h_a5 hn) (by congr_one h_a6 hn) (by congr_one h_a7 hn) (by congr_one h_a8 hn) (by congr_one h_a9 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

end pathos_compiled_checker
