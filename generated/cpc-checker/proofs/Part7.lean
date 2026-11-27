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

theorem case_0_eo__24eo_5fprog_5fbv_2dextract_2dsign_2dextend_2d3_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 a6 a7 a8 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _) (x_a7 : _) (x_a8 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) (h_a6 : Represents.rep s a6 x_a6) (h_a7 : Represents.rep s a7 x_a7) (h_a8 : Represents.rep s a8 x_a8) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) (hn_a4 : x_a4 ≠ Eo.Term.Stuck) (hn_a5 : x_a5 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fbv_2dextract_2dsign_2dextend_2d3 s a0 a1 a2 a3 a4 a5 a6 a7 a8 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_bv_extract_sign_extend_3.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_bv_extract_sign_extend_3.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fbv_2dextract_2dsign_2dextend_2d3
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a6 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_bv_extract_sign_extend_3.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_extract_sign_extend_3.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_extract_sign_extend_3.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a7 h_a8 h_v4 h_v6 h_v7 dropping h_a6 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_extract_sign_extend_3.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_extract_sign_extend_3.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_extract_sign_extend_3.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__3e_3d.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a7 h_a8 h_v4 h_v11 h_v13 h_v14 dropping h_v10 h_v6 h_v7 h_v8 he_v15 hinv1 e_v15 s1 v10 v6 v7 v8
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_extract_sign_extend_3.case_0
  pat_same v14 a1 with h_v14 h_a1 using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_extract_sign_extend_3.case_0
  pat_unapply h_v11 as ⟨v17, v18, x_v17, x_v18, h_v17, h_v18, hn_v17, hn_v18⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_extract_sign_extend_3.case_0
  step as ⟨e_v19, he_v19⟩
  store_step with CtorSpec.eo__40bvsize.construct s2 e_v19 (by rw [he_v19]; exact empty_args) hinv2 h64 as ⟨v19, s3, hinv3, h_v19⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a7 h_a8 h_v4 h_v17 h_v18 dropping h_v11 h_v13 h_v14 h_v15 he_v19 hinv2 e_v19 s2 v11 v13 v14 v15
  pat_same v17 v19 with h_v17 h_v19 using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_extract_sign_extend_3.case_0
  pat_same v18 a0 with h_v18 h_a0 using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_extract_sign_extend_3.case_0
  store_step with Store.literal_boolean_spec s3 true hinv3 h64 as ⟨v20, s4, hinv4, h_v20⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a7 h_a8 h_v4 dropping h_v17 h_v18 h_v19 hinv3 s3 v17 v18 v19
  pat_same v4 v20 with h_v4 h_v20 using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_extract_sign_extend_3.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a7 as ⟨v22, x_v22, h_v22⟩ else hinv4 hG in EoCases.__eo_prog_bv_extract_sign_extend_3.case_0
  pat_unapply h_v22 as ⟨v24, v25, x_v24, x_v25, h_v24, h_v25, hn_v24, hn_v25⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_extract_sign_extend_3.case_0
  pat_unapply h_v24 as ⟨v27, v28, x_v27, x_v28, h_v27, h_v28, hn_v27, hn_v28⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_extract_sign_extend_3.case_0
  step as ⟨e_v29, he_v29⟩
  store_step with CtorSpec.eo__3d.construct s4 e_v29 (by rw [he_v29]; exact empty_args) hinv4 h64 as ⟨v29, s5, hinv5, h_v29⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a8 h_v25 h_v27 h_v28 dropping h_a7 h_v20 h_v22 h_v24 h_v4 he_v29 hinv4 e_v29 s4 v20 v22 v24 v4
  pat_same v27 v29 with h_v27 h_v29 using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_extract_sign_extend_3.case_0
  pat_same v28 a4 with h_v28 h_a4 using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_extract_sign_extend_3.case_0
  pat_unapply h_v25 as ⟨v31, v32, x_v31, x_v32, h_v31, h_v32, hn_v31, hn_v32⟩ using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_extract_sign_extend_3.case_0
  pat_unapply h_v31 as ⟨v34, v35, x_v34, x_v35, h_v34, h_v35, hn_v34, hn_v35⟩ using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_extract_sign_extend_3.case_0
  step as ⟨e_v36, he_v36⟩
  store_step with CtorSpec.eo__2b.construct s5 e_v36 (by rw [he_v36]; exact empty_args) hinv5 h64 as ⟨v36, s6, hinv6, h_v36⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a8 h_v32 h_v34 h_v35 dropping h_v25 h_v27 h_v28 h_v29 h_v31 he_v36 hinv5 e_v36 s5 v25 v27 v28 v29 v31
  pat_same v34 v36 with h_v34 h_v36 using hinv6 else hinv6 hG in EoCases.__eo_prog_bv_extract_sign_extend_3.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s6 1#u32 (1) (by scalar_tac) hinv6 h64 as ⟨v37, s7, hinv7, h_v37⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a8 h_v32 h_v35 dropping h_v34 h_v36 hinv6 s6 v34 v36
  pat_same v35 v37 with h_v35 h_v37 using hinv7 else hinv7 hG in EoCases.__eo_prog_bv_extract_sign_extend_3.case_0
  pat_unapply h_v32 as ⟨v39, v40, x_v39, x_v40, h_v39, h_v40, hn_v39, hn_v40⟩ using hinv7 else hinv7 hG in EoCases.__eo_prog_bv_extract_sign_extend_3.case_0
  pat_unapply h_v39 as ⟨v42, v43, x_v42, x_v43, h_v42, h_v43, hn_v42, hn_v43⟩ using hinv7 else hinv7 hG in EoCases.__eo_prog_bv_extract_sign_extend_3.case_0
  step as ⟨e_v44, he_v44⟩
  store_step with CtorSpec.eo__2b.construct s7 e_v44 (by rw [he_v44]; exact empty_args) hinv7 h64 as ⟨v44, s8, hinv8, h_v44⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a8 h_v40 h_v42 h_v43 dropping h_v32 h_v35 h_v37 h_v39 he_v44 hinv7 e_v44 s7 v32 v35 v37 v39
  pat_same v42 v44 with h_v42 h_v44 using hinv8 else hinv8 hG in EoCases.__eo_prog_bv_extract_sign_extend_3.case_0
  pat_unapply h_v43 as ⟨v46, v47, x_v46, x_v47, h_v46, h_v47, hn_v46, hn_v47⟩ using hinv8 else hinv8 hG in EoCases.__eo_prog_bv_extract_sign_extend_3.case_0
  pat_unapply h_v46 as ⟨v49, v50, x_v49, x_v50, h_v49, h_v50, hn_v49, hn_v50⟩ using hinv8 else hinv8 hG in EoCases.__eo_prog_bv_extract_sign_extend_3.case_0
  step as ⟨e_v51, he_v51⟩
  store_step with CtorSpec.eo__2d.construct s8 e_v51 (by rw [he_v51]; exact empty_args) hinv8 h64 as ⟨v51, s9, hinv9, h_v51⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a8 h_v40 h_v47 h_v49 h_v50 dropping h_v42 h_v43 h_v44 h_v46 he_v51 hinv8 e_v51 s8 v42 v43 v44 v46
  pat_same v49 v51 with h_v49 h_v51 using hinv9 else hinv9 hG in EoCases.__eo_prog_bv_extract_sign_extend_3.case_0
  pat_same v50 a2 with h_v50 h_a2 using hinv9 else hinv9 hG in EoCases.__eo_prog_bv_extract_sign_extend_3.case_0
  pat_same v47 a1 with h_v47 h_a1 using hinv9 else hinv9 hG in EoCases.__eo_prog_bv_extract_sign_extend_3.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s9 0#u32 (0) (by scalar_tac) hinv9 h64 as ⟨v52, s10, hinv10, h_v52⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a8 h_v40 dropping h_v47 h_v49 h_v50 h_v51 hinv9 s9 v47 v49 v50 v51
  pat_same v40 v52 with h_v40 h_v52 using hinv10 else hinv10 hG in EoCases.__eo_prog_bv_extract_sign_extend_3.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a8 as ⟨v54, x_v54, h_v54⟩ else hinv10 hG in EoCases.__eo_prog_bv_extract_sign_extend_3.case_0
  pat_unapply h_v54 as ⟨v56, v57, x_v56, x_v57, h_v56, h_v57, hn_v56, hn_v57⟩ using hinv10 else hinv10 hG in EoCases.__eo_prog_bv_extract_sign_extend_3.case_0
  pat_unapply h_v56 as ⟨v59, v60, x_v59, x_v60, h_v59, h_v60, hn_v59, hn_v60⟩ using hinv10 else hinv10 hG in EoCases.__eo_prog_bv_extract_sign_extend_3.case_0
  step as ⟨e_v61, he_v61⟩
  store_step with CtorSpec.eo__3d.construct s10 e_v61 (by rw [he_v61]; exact empty_args) hinv10 h64 as ⟨v61, s11, hinv11, h_v61⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v57 h_v59 h_v60 dropping h_a8 h_v40 h_v52 h_v54 h_v56 he_v61 hinv10 e_v61 s10 v40 v52 v54 v56
  pat_same v59 v61 with h_v59 h_v61 using hinv11 else hinv11 hG in EoCases.__eo_prog_bv_extract_sign_extend_3.case_0
  pat_same v60 a5 with h_v60 h_a5 using hinv11 else hinv11 hG in EoCases.__eo_prog_bv_extract_sign_extend_3.case_0
  pat_unapply h_v57 as ⟨v63, v64, x_v63, x_v64, h_v63, h_v64, hn_v63, hn_v64⟩ using hinv11 else hinv11 hG in EoCases.__eo_prog_bv_extract_sign_extend_3.case_0
  pat_unapply h_v63 as ⟨v66, v67, x_v66, x_v67, h_v66, h_v67, hn_v66, hn_v67⟩ using hinv11 else hinv11 hG in EoCases.__eo_prog_bv_extract_sign_extend_3.case_0
  step as ⟨e_v68, he_v68⟩
  store_step with CtorSpec.eo__2d.construct s11 e_v68 (by rw [he_v68]; exact empty_args) hinv11 h64 as ⟨v68, s12, hinv12, h_v68⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v64 h_v66 h_v67 dropping h_v57 h_v59 h_v60 h_v61 h_v63 he_v68 hinv11 e_v68 s11 v57 v59 v60 v61 v63
  pat_same v66 v68 with h_v66 h_v68 using hinv12 else hinv12 hG in EoCases.__eo_prog_bv_extract_sign_extend_3.case_0
  pat_unapply h_v67 as ⟨v70, v71, x_v70, x_v71, h_v70, h_v71, hn_v70, hn_v71⟩ using hinv12 else hinv12 hG in EoCases.__eo_prog_bv_extract_sign_extend_3.case_0
  step as ⟨e_v72, he_v72⟩
  store_step with CtorSpec.eo__40bvsize.construct s12 e_v72 (by rw [he_v72]; exact empty_args) hinv12 h64 as ⟨v72, s13, hinv13, h_v72⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v64 h_v70 h_v71 dropping h_v66 h_v67 h_v68 he_v72 hinv12 e_v72 s12 v66 v67 v68
  pat_same v70 v72 with h_v70 h_v72 using hinv13 else hinv13 hG in EoCases.__eo_prog_bv_extract_sign_extend_3.case_0
  pat_same v71 a0 with h_v71 h_a0 using hinv13 else hinv13 hG in EoCases.__eo_prog_bv_extract_sign_extend_3.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s13 1#u32 (1) (by scalar_tac) hinv13 h64 as ⟨v73, s14, hinv14, h_v73⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v64 dropping h_v70 h_v71 h_v72 hinv13 s13 v70 v71 v72
  pat_same v64 v73 with h_v64 h_v73 using hinv14 else hinv14 hG in EoCases.__eo_prog_bv_extract_sign_extend_3.case_0
  step as ⟨e_v74, he_v74⟩
  store_step with CtorSpec.eo__3d.construct s14 e_v74 (by rw [he_v74]; exact empty_args) hinv14 h64 as ⟨v74, s15, hinv15, h_v74⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 dropping h_v64 h_v73 he_v74 hinv14 e_v74 s14 v64 v73
  step as ⟨e_v75, he_v75⟩
  store_step with CtorSpec.eo_extract.construct s15 e_v75 (by rw [he_v75]; rfl) h_a2 h_a1 hinv15 h64 as ⟨v75, s16, hinv16, h_v75⟩ growing hG carrying h_a0 h_a3 h_a4 h_a5 h_v74 dropping h_a1 h_a2 he_v75 hinv15 e_v75 s15
  step as ⟨e_v76, he_v76⟩
  store_step with CtorSpec.eo_sign_5fextend.construct s16 e_v76 (by rw [he_v76]; rfl) h_a3 hinv16 h64 as ⟨v76, s17, hinv17, h_v76⟩ growing hG carrying h_a0 h_a4 h_a5 h_v74 h_v75 dropping h_a3 he_v76 hinv16 e_v76 s16
  store_step with Store.apply_rep s17 v76 a0 _ _ hinv17 h64 h_v76 h_a0 (by ns_tac) (by ns_tac) as ⟨v77, s18, hinv18, h_v77⟩ growing hG carrying h_a0 h_a4 h_a5 h_v74 h_v75 dropping h_v76 hinv17 s17 v76
  store_step with Store.apply_rep s18 v75 v77 _ _ hinv18 h64 h_v75 h_v77 (by ns_tac) (by ns_tac) as ⟨v78, s19, hinv19, h_v78⟩ growing hG carrying h_a0 h_a4 h_a5 h_v74 dropping h_v75 h_v77 hinv18 s18 v75 v77
  store_step with Store.apply_rep s19 v74 v78 _ _ hinv19 h64 h_v74 h_v78 (by ns_tac) (by ns_tac) as ⟨v79, s20, hinv20, h_v79⟩ growing hG carrying h_a0 h_a4 h_a5 dropping h_v74 h_v78 hinv19 s19 v74 v78
  step as ⟨e_v80, he_v80⟩
  store_step with CtorSpec.eo_repeat.construct s20 e_v80 (by rw [he_v80]; rfl) h_a4 hinv20 h64 as ⟨v80, s21, hinv21, h_v80⟩ growing hG carrying h_a0 h_a5 h_v79 dropping h_a4 he_v80 hinv20 e_v80 s20
  step as ⟨e_v81, he_v81⟩
  store_step with CtorSpec.eo_extract.construct s21 e_v81 (by rw [he_v81]; rfl) h_a5 h_a5 hinv21 h64 as ⟨v81, s22, hinv22, h_v81⟩ growing hG carrying h_a0 h_v79 h_v80 dropping h_a5 he_v81 hinv21 e_v81 s21
  store_step with Store.apply_rep s22 v81 a0 _ _ hinv22 h64 h_v81 h_a0 (by ns_tac) (by ns_tac) as ⟨v82, s23, hinv23, h_v82⟩ growing hG carrying h_v79 h_v80 dropping h_a0 h_v81 hinv22 s22 v81
  store_step with Store.apply_rep s23 v80 v82 _ _ hinv23 h64 h_v80 h_v82 (by ns_tac) (by ns_tac) as ⟨v83, s24, hinv24, h_v83⟩ growing hG carrying h_v79 dropping h_v80 h_v82 hinv23 s23 v80 v82
  store_step with Store.apply_rep s24 v79 v83 _ _ hinv24 h64 h_v79 h_v83 (by ns_tac) (by ns_tac) as ⟨v84, s25, hinv25, h_v84⟩ growing hG carrying dropping h_v79 h_v83 hinv24 s24 v79 v83
  case_done hinv25 hG with h_v84 in EoCases.__eo_prog_bv_extract_sign_extend_3.case_0 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_a5 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v13 hn_v14 hn_v17 hn_v18 hn_v24 hn_v25 hn_v27 hn_v28 hn_v31 hn_v32 hn_v34 hn_v35 hn_v39 hn_v40 hn_v42 hn_v43 hn_v46 hn_v47 hn_v49 hn_v50 hn_v56 hn_v57 hn_v59 hn_v60 hn_v63 hn_v64 hn_v66 hn_v67 hn_v70 hn_v71

/-- logos's `__eo_prog_bv_extract_sign_extend_3` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fbv_2dextract_2dsign_2dextend_2d3.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _) (x_a7 : _) (x_a8 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) (hw_a4 : Valid.valid x_a4) (hw_a5 : Valid.valid x_a5) (hw_a6 : Valid.valid x_a6) (hw_a7 : Valid.valid x_a7) (hw_a8 : Valid.valid x_a8) :
    __eo_prog_bv_extract_sign_extend_3 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else if x_a4 = Eo.Term.Stuck then HasStuck.stuck else if x_a5 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_bv_extract_sign_extend_3.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_bv_extract_sign_extend_3
  unfold EoCases.__eo_prog_bv_extract_sign_extend_3.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fbv_2dextract_2dsign_2dextend_2d3_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 a6 a7 a8 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _) (x_a7 : _) (x_a8 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) (h_a6 : Represents.rep s a6 x_a6) (h_a7 : Represents.rep s a7 x_a7) (h_a8 : Represents.rep s a8 x_a8) :
    body_eo__24eo_5fprog_5fbv_2dextract_2dsign_2dextend_2d3 s a0 a1 a2 a3 a4 a5 a6 a7 a8 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_extract_sign_extend_3 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fbv_2dextract_2dsign_2dextend_2d3.rust_eq x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3) (by valid_tac hinv h_a4) (by valid_tac hinv h_a5) (by valid_tac hinv h_a6) (by valid_tac hinv h_a7) (by valid_tac hinv h_a8)]
  unfold body_eo__24eo_5fprog_5fbv_2dextract_2dsign_2dextend_2d3
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  stuck_check h_a3 : x_a3 as hn_a3 else hinv hG
  stuck_check h_a4 : x_a4 as hn_a4 else hinv hG
  stuck_check h_a5 : x_a5 as hn_a5 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fbv_2dextract_2dsign_2dextend_2d3_spec n ih s a0 a1 a2 a3 a4 a5 a6 a7 a8 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_a5
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_a5
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_a5 hc0 in EoCases.__eo_prog_bv_extract_sign_extend_3.case_0

theorem eo__24eo_5fprog_5fbv_2dextract_2dsign_2dextend_2d3_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fbv_2dextract_2dsign_2dextend_2d3.Spec n := by
  intro s a0 a1 a2 a3 a4 a5 a6 a7 a8 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8
  unfold eo__24eo_5fprog_5fbv_2dextract_2dsign_2dextend_2d3
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fbv_2dextract_2dsign_2dextend_2d3 s1 a0 a1 a2 a3 a4 a5 a6 a7 a8) (fun s' t => Represents.rep s' t (__eo_prog_bv_extract_sign_extend_3 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fbv_2dextract_2dsign_2dextend_2d3_spec m (ih m hm) s1 a0 a1 a2 a3 a4 a5 a6 a7 a8 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn) (by congr_one h_a4 hn) (by congr_one h_a5 hn) (by congr_one h_a6 hn) (by congr_one h_a7 hn) (by congr_one h_a8 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fbv_2dextract_2dwhole_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fbv_2dextract_2dwhole s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_bv_extract_whole.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_bv_extract_whole.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fbv_2dextract_2dwhole
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a2 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_bv_extract_whole.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_extract_whole.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_extract_whole.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_v4 h_v6 h_v7 dropping h_a2 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_extract_whole.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_extract_whole.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_extract_whole.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__3e_3d.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_a1 h_v4 h_v11 h_v13 h_v14 dropping h_v10 h_v6 h_v7 h_v8 he_v15 hinv1 e_v15 s1 v10 v6 v7 v8
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_extract_whole.case_0
  pat_same v14 a1 with h_v14 h_a1 using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_extract_whole.case_0
  pat_unapply h_v11 as ⟨v17, v18, x_v17, x_v18, h_v17, h_v18, hn_v17, hn_v18⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_extract_whole.case_0
  pat_unapply h_v17 as ⟨v20, v21, x_v20, x_v21, h_v20, h_v21, hn_v20, hn_v21⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_extract_whole.case_0
  step as ⟨e_v22, he_v22⟩
  store_step with CtorSpec.eo__2d.construct s2 e_v22 (by rw [he_v22]; exact empty_args) hinv2 h64 as ⟨v22, s3, hinv3, h_v22⟩ growing hG carrying h_a0 h_a1 h_v4 h_v18 h_v20 h_v21 dropping h_v11 h_v13 h_v14 h_v15 h_v17 he_v22 hinv2 e_v22 s2 v11 v13 v14 v15 v17
  pat_same v20 v22 with h_v20 h_v22 using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_extract_whole.case_0
  pat_unapply h_v21 as ⟨v24, v25, x_v24, x_v25, h_v24, h_v25, hn_v24, hn_v25⟩ using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_extract_whole.case_0
  step as ⟨e_v26, he_v26⟩
  store_step with CtorSpec.eo__40bvsize.construct s3 e_v26 (by rw [he_v26]; exact empty_args) hinv3 h64 as ⟨v26, s4, hinv4, h_v26⟩ growing hG carrying h_a0 h_a1 h_v4 h_v18 h_v24 h_v25 dropping h_v20 h_v21 h_v22 he_v26 hinv3 e_v26 s3 v20 v21 v22
  pat_same v24 v26 with h_v24 h_v26 using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_extract_whole.case_0
  pat_same v25 a0 with h_v25 h_a0 using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_extract_whole.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s4 1#u32 (1) (by scalar_tac) hinv4 h64 as ⟨v27, s5, hinv5, h_v27⟩ growing hG carrying h_a0 h_a1 h_v4 h_v18 dropping h_v24 h_v25 h_v26 hinv4 s4 v24 v25 v26
  pat_same v18 v27 with h_v18 h_v27 using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_extract_whole.case_0
  store_step with Store.literal_boolean_spec s5 true hinv5 h64 as ⟨v28, s6, hinv6, h_v28⟩ growing hG carrying h_a0 h_a1 h_v4 dropping h_v18 h_v27 hinv5 s5 v18 v27
  pat_same v4 v28 with h_v4 h_v28 using hinv6 else hinv6 hG in EoCases.__eo_prog_bv_extract_whole.case_0
  step as ⟨e_v29, he_v29⟩
  store_step with CtorSpec.eo__3d.construct s6 e_v29 (by rw [he_v29]; exact empty_args) hinv6 h64 as ⟨v29, s7, hinv7, h_v29⟩ growing hG carrying h_a0 h_a1 dropping h_v28 h_v4 he_v29 hinv6 e_v29 s6 v28 v4
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s7 0#u32 (0) (by scalar_tac) hinv7 h64 as ⟨v30, s8, hinv8, h_v30⟩ growing hG carrying h_a0 h_a1 h_v29 dropping hinv7 s7
  step as ⟨e_v31, he_v31⟩
  store_step with CtorSpec.eo_extract.construct s8 e_v31 (by rw [he_v31]; rfl) h_a1 h_v30 hinv8 h64 as ⟨v31, s9, hinv9, h_v31⟩ growing hG carrying h_a0 h_v29 dropping h_a1 h_v30 he_v31 hinv8 e_v31 s8 v30
  store_step with Store.apply_rep s9 v31 a0 _ _ hinv9 h64 h_v31 h_a0 (by ns_tac) (by ns_tac) as ⟨v32, s10, hinv10, h_v32⟩ growing hG carrying h_a0 h_v29 dropping h_v31 hinv9 s9 v31
  store_step with Store.apply_rep s10 v29 v32 _ _ hinv10 h64 h_v29 h_v32 (by ns_tac) (by ns_tac) as ⟨v33, s11, hinv11, h_v33⟩ growing hG carrying h_a0 dropping h_v29 h_v32 hinv10 s10 v29 v32
  store_step with Store.apply_rep s11 v33 a0 _ _ hinv11 h64 h_v33 h_a0 (by ns_tac) (by ns_tac) as ⟨v34, s12, hinv12, h_v34⟩ growing hG carrying dropping h_a0 h_v33 hinv11 s11 v33
  case_done hinv12 hG with h_v34 in EoCases.__eo_prog_bv_extract_whole.case_0 using hn_a0 hn_a1 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v13 hn_v14 hn_v17 hn_v18 hn_v20 hn_v21 hn_v24 hn_v25

/-- logos's `__eo_prog_bv_extract_whole` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fbv_2dextract_2dwhole.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __eo_prog_bv_extract_whole x_a0 x_a1 x_a2 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_bv_extract_whole.case_0 x_a0 x_a1 x_a2] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_bv_extract_whole
  unfold EoCases.__eo_prog_bv_extract_whole.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fbv_2dextract_2dwhole_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24eo_5fprog_5fbv_2dextract_2dwhole s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_extract_whole x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fbv_2dextract_2dwhole.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24eo_5fprog_5fbv_2dextract_2dwhole
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fbv_2dextract_2dwhole_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_bv_extract_whole.case_0

theorem eo__24eo_5fprog_5fbv_2dextract_2dwhole_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fbv_2dextract_2dwhole.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24eo_5fprog_5fbv_2dextract_2dwhole
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fbv_2dextract_2dwhole s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__eo_prog_bv_extract_whole x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fbv_2dextract_2dwhole_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fbv_2dite_2dconst_2dchildren_2d1_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fbv_2dite_2dconst_2dchildren_2d1 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_bv_ite_const_children_1.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_bv_ite_const_children_1.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fbv_2dite_2dconst_2dchildren_2d1
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 dropping he_v0 e_v0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_bvite.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0 dropping he_v1 hinv1 e_v1 s1
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_v0 dropping h_v1 hinv2 s2 v1
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s3 1#u32 (1) (by scalar_tac) hinv3 h64 as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_v0 h_v2 dropping hinv3 s3
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s4 e_v4 (by rw [he_v4]; rfl) h_v3 hinv4 h64 as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_v0 h_v2 dropping h_v3 he_v4 hinv4 e_v4 s4 v3
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s5 0#u32 (0) (by scalar_tac) hinv5 h64 as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_v0 h_v2 h_v4 dropping hinv5 s5
  store_step with Store.apply_rep s6 v4 v5 _ _ hinv6 h64 h_v4 h_v5 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_v0 h_v2 dropping h_v4 h_v5 hinv6 s6 v4 v5
  store_step with Store.apply_rep s7 v2 v6 _ _ hinv7 h64 h_v2 h_v6 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_v0 dropping h_v2 h_v6 hinv7 s7 v2 v6
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s8 1#u32 (1) (by scalar_tac) hinv8 h64 as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_v0 h_v7 dropping hinv8 s8
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s9 e_v9 (by rw [he_v9]; rfl) h_v8 hinv9 h64 as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a0 h_v0 h_v7 dropping h_v8 he_v9 hinv9 e_v9 s9 v8
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s10 1#u32 (1) (by scalar_tac) hinv10 h64 as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_a0 h_v0 h_v7 h_v9 dropping hinv10 s10
  store_step with Store.apply_rep s11 v9 v10 _ _ hinv11 h64 h_v9 h_v10 (by ns_tac) (by ns_tac) as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_a0 h_v0 h_v7 dropping h_v10 h_v9 hinv11 s11 v10 v9
  store_step with Store.apply_rep s12 v7 v11 _ _ hinv12 h64 h_v7 h_v11 (by ns_tac) (by ns_tac) as ⟨v12, s13, hinv13, h_v12⟩ growing hG carrying h_a0 h_v0 dropping h_v11 h_v7 hinv12 s12 v11 v7
  store_step with Store.apply_rep s13 v0 v12 _ _ hinv13 h64 h_v0 h_v12 (by ns_tac) (by ns_tac) as ⟨v13, s14, hinv14, h_v13⟩ growing hG carrying h_a0 dropping h_v0 h_v12 hinv13 s13 v0 v12
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo_bvnot.construct s14 e_v14 (by rw [he_v14]; exact empty_args) hinv14 h64 as ⟨v14, s15, hinv15, h_v14⟩ growing hG carrying h_a0 h_v13 dropping he_v14 hinv14 e_v14 s14
  store_step with Store.apply_rep s15 v14 a0 _ _ hinv15 h64 h_v14 h_a0 (by ns_tac) (by ns_tac) as ⟨v15, s16, hinv16, h_v15⟩ growing hG carrying h_v13 dropping h_a0 h_v14 hinv15 s15 v14
  store_step with Store.apply_rep s16 v13 v15 _ _ hinv16 h64 h_v13 h_v15 (by ns_tac) (by ns_tac) as ⟨v16, s17, hinv17, h_v16⟩ growing hG carrying dropping h_v13 h_v15 hinv16 s16 v13 v15
  case_done hinv17 hG with h_v16 in EoCases.__eo_prog_bv_ite_const_children_1.case_0 using hn_a0

/-- logos's `__eo_prog_bv_ite_const_children_1` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fbv_2dite_2dconst_2dchildren_2d1.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_bv_ite_const_children_1 x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_bv_ite_const_children_1.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_bv_ite_const_children_1
  unfold EoCases.__eo_prog_bv_ite_const_children_1.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fbv_2dite_2dconst_2dchildren_2d1_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fbv_2dite_2dconst_2dchildren_2d1 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_ite_const_children_1 x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fbv_2dite_2dconst_2dchildren_2d1.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fbv_2dite_2dconst_2dchildren_2d1
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fbv_2dite_2dconst_2dchildren_2d1_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_bv_ite_const_children_1.case_0

theorem eo__24eo_5fprog_5fbv_2dite_2dconst_2dchildren_2d1_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fbv_2dite_2dconst_2dchildren_2d1.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fbv_2dite_2dconst_2dchildren_2d1
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fbv_2dite_2dconst_2dchildren_2d1 s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_bv_ite_const_children_1 x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fbv_2dite_2dconst_2dchildren_2d1_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fbv_2dite_2dconst_2dchildren_2d2_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fbv_2dite_2dconst_2dchildren_2d2 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_bv_ite_const_children_2.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_bv_ite_const_children_2.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fbv_2dite_2dconst_2dchildren_2d2
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 dropping he_v0 e_v0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_bvite.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0 dropping he_v1 hinv1 e_v1 s1
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_v0 dropping h_v1 hinv2 s2 v1
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s3 1#u32 (1) (by scalar_tac) hinv3 h64 as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_v0 h_v2 dropping hinv3 s3
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s4 e_v4 (by rw [he_v4]; rfl) h_v3 hinv4 h64 as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_v0 h_v2 dropping h_v3 he_v4 hinv4 e_v4 s4 v3
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s5 1#u32 (1) (by scalar_tac) hinv5 h64 as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_v0 h_v2 h_v4 dropping hinv5 s5
  store_step with Store.apply_rep s6 v4 v5 _ _ hinv6 h64 h_v4 h_v5 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_v0 h_v2 dropping h_v4 h_v5 hinv6 s6 v4 v5
  store_step with Store.apply_rep s7 v2 v6 _ _ hinv7 h64 h_v2 h_v6 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_v0 dropping h_v2 h_v6 hinv7 s7 v2 v6
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s8 1#u32 (1) (by scalar_tac) hinv8 h64 as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_v0 h_v7 dropping hinv8 s8
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s9 e_v9 (by rw [he_v9]; rfl) h_v8 hinv9 h64 as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a0 h_v0 h_v7 dropping h_v8 he_v9 hinv9 e_v9 s9 v8
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s10 0#u32 (0) (by scalar_tac) hinv10 h64 as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_a0 h_v0 h_v7 h_v9 dropping hinv10 s10
  store_step with Store.apply_rep s11 v9 v10 _ _ hinv11 h64 h_v9 h_v10 (by ns_tac) (by ns_tac) as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_a0 h_v0 h_v7 dropping h_v10 h_v9 hinv11 s11 v10 v9
  store_step with Store.apply_rep s12 v7 v11 _ _ hinv12 h64 h_v7 h_v11 (by ns_tac) (by ns_tac) as ⟨v12, s13, hinv13, h_v12⟩ growing hG carrying h_a0 h_v0 dropping h_v11 h_v7 hinv12 s12 v11 v7
  store_step with Store.apply_rep s13 v0 v12 _ _ hinv13 h64 h_v0 h_v12 (by ns_tac) (by ns_tac) as ⟨v13, s14, hinv14, h_v13⟩ growing hG carrying h_a0 dropping h_v0 h_v12 hinv13 s13 v0 v12
  store_step with Store.apply_rep s14 v13 a0 _ _ hinv14 h64 h_v13 h_a0 (by ns_tac) (by ns_tac) as ⟨v14, s15, hinv15, h_v14⟩ growing hG carrying dropping h_a0 h_v13 hinv14 s14 v13
  case_done hinv15 hG with h_v14 in EoCases.__eo_prog_bv_ite_const_children_2.case_0 using hn_a0

/-- logos's `__eo_prog_bv_ite_const_children_2` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fbv_2dite_2dconst_2dchildren_2d2.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_bv_ite_const_children_2 x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_bv_ite_const_children_2.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_bv_ite_const_children_2
  unfold EoCases.__eo_prog_bv_ite_const_children_2.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fbv_2dite_2dconst_2dchildren_2d2_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fbv_2dite_2dconst_2dchildren_2d2 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_ite_const_children_2 x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fbv_2dite_2dconst_2dchildren_2d2.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fbv_2dite_2dconst_2dchildren_2d2
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fbv_2dite_2dconst_2dchildren_2d2_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_bv_ite_const_children_2.case_0

theorem eo__24eo_5fprog_5fbv_2dite_2dconst_2dchildren_2d2_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fbv_2dite_2dconst_2dchildren_2d2.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fbv_2dite_2dconst_2dchildren_2d2
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fbv_2dite_2dconst_2dchildren_2d2 s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_bv_ite_const_children_2 x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fbv_2dite_2dconst_2dchildren_2d2_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fbv_2dite_2dconst_2dcond_2d1_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fbv_2dite_2dconst_2dcond_2d1 s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_bv_ite_const_cond_1.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_bv_ite_const_cond_1.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fbv_2dite_2dconst_2dcond_2d1
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 dropping he_v0 e_v0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_bvite.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0 dropping he_v1 hinv1 e_v1 s1
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s2 1#u32 (1) (by scalar_tac) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 dropping hinv2 s2
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s3 e_v3 (by rw [he_v3]; rfl) h_v2 hinv3 h64 as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 dropping h_v2 he_v3 hinv3 e_v3 s3 v2
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s4 1#u32 (1) (by scalar_tac) hinv4 h64 as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v3 dropping hinv4 s4
  store_step with Store.apply_rep s5 v3 v4 _ _ hinv5 h64 h_v3 h_v4 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 dropping h_v3 h_v4 hinv5 s5 v3 v4
  store_step with Store.apply_rep s6 v1 v5 _ _ hinv6 h64 h_v1 h_v5 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_v0 dropping h_v1 h_v5 hinv6 s6 v1 v5
  store_step with Store.apply_rep s7 v6 a0 _ _ hinv7 h64 h_v6 h_a0 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_v0 dropping h_v6 hinv7 s7 v6
  store_step with Store.apply_rep s8 v7 a1 _ _ hinv8 h64 h_v7 h_a1 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_v0 dropping h_a1 h_v7 hinv8 s8 v7
  store_step with Store.apply_rep s9 v0 v8 _ _ hinv9 h64 h_v0 h_v8 (by ns_tac) (by ns_tac) as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a0 dropping h_v0 h_v8 hinv9 s9 v0 v8
  store_step with Store.apply_rep s10 v9 a0 _ _ hinv10 h64 h_v9 h_a0 (by ns_tac) (by ns_tac) as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying dropping h_a0 h_v9 hinv10 s10 v9
  case_done hinv11 hG with h_v10 in EoCases.__eo_prog_bv_ite_const_cond_1.case_0 using hn_a0 hn_a1

/-- logos's `__eo_prog_bv_ite_const_cond_1` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fbv_2dite_2dconst_2dcond_2d1.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_bv_ite_const_cond_1 x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_bv_ite_const_cond_1.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_bv_ite_const_cond_1
  unfold EoCases.__eo_prog_bv_ite_const_cond_1.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fbv_2dite_2dconst_2dcond_2d1_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5fbv_2dite_2dconst_2dcond_2d1 s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_ite_const_cond_1 x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fbv_2dite_2dconst_2dcond_2d1.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5fbv_2dite_2dconst_2dcond_2d1
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fbv_2dite_2dconst_2dcond_2d1_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_bv_ite_const_cond_1.case_0

theorem eo__24eo_5fprog_5fbv_2dite_2dconst_2dcond_2d1_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fbv_2dite_2dconst_2dcond_2d1.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5fbv_2dite_2dconst_2dcond_2d1
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fbv_2dite_2dconst_2dcond_2d1 s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_bv_ite_const_cond_1 x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fbv_2dite_2dconst_2dcond_2d1_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fbv_2dite_2dconst_2dcond_2d2_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fbv_2dite_2dconst_2dcond_2d2 s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_bv_ite_const_cond_2.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_bv_ite_const_cond_2.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fbv_2dite_2dconst_2dcond_2d2
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 dropping he_v0 e_v0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_bvite.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0 dropping he_v1 hinv1 e_v1 s1
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s2 1#u32 (1) (by scalar_tac) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 dropping hinv2 s2
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s3 e_v3 (by rw [he_v3]; rfl) h_v2 hinv3 h64 as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 dropping h_v2 he_v3 hinv3 e_v3 s3 v2
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s4 0#u32 (0) (by scalar_tac) hinv4 h64 as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v3 dropping hinv4 s4
  store_step with Store.apply_rep s5 v3 v4 _ _ hinv5 h64 h_v3 h_v4 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 dropping h_v3 h_v4 hinv5 s5 v3 v4
  store_step with Store.apply_rep s6 v1 v5 _ _ hinv6 h64 h_v1 h_v5 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_v0 dropping h_v1 h_v5 hinv6 s6 v1 v5
  store_step with Store.apply_rep s7 v6 a0 _ _ hinv7 h64 h_v6 h_a0 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a1 h_v0 dropping h_a0 h_v6 hinv7 s7 v6
  store_step with Store.apply_rep s8 v7 a1 _ _ hinv8 h64 h_v7 h_a1 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a1 h_v0 dropping h_v7 hinv8 s8 v7
  store_step with Store.apply_rep s9 v0 v8 _ _ hinv9 h64 h_v0 h_v8 (by ns_tac) (by ns_tac) as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a1 dropping h_v0 h_v8 hinv9 s9 v0 v8
  store_step with Store.apply_rep s10 v9 a1 _ _ hinv10 h64 h_v9 h_a1 (by ns_tac) (by ns_tac) as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying dropping h_a1 h_v9 hinv10 s10 v9
  case_done hinv11 hG with h_v10 in EoCases.__eo_prog_bv_ite_const_cond_2.case_0 using hn_a0 hn_a1

/-- logos's `__eo_prog_bv_ite_const_cond_2` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fbv_2dite_2dconst_2dcond_2d2.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_bv_ite_const_cond_2 x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_bv_ite_const_cond_2.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_bv_ite_const_cond_2
  unfold EoCases.__eo_prog_bv_ite_const_cond_2.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fbv_2dite_2dconst_2dcond_2d2_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5fbv_2dite_2dconst_2dcond_2d2 s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_ite_const_cond_2 x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fbv_2dite_2dconst_2dcond_2d2.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5fbv_2dite_2dconst_2dcond_2d2
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fbv_2dite_2dconst_2dcond_2d2_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_bv_ite_const_cond_2.case_0

theorem eo__24eo_5fprog_5fbv_2dite_2dconst_2dcond_2d2_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fbv_2dite_2dconst_2dcond_2d2.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5fbv_2dite_2dconst_2dcond_2d2
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fbv_2dite_2dconst_2dcond_2d2 s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_bv_ite_const_cond_2 x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fbv_2dite_2dconst_2dcond_2d2_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fbv_2dite_2dequal_2dchildren_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fbv_2dite_2dequal_2dchildren s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_bv_ite_equal_children.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_bv_ite_equal_children.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fbv_2dite_2dequal_2dchildren
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 dropping he_v0 e_v0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_bvite.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0 dropping he_v1 hinv1 e_v1 s1
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a1 h_v0 dropping h_a0 h_v1 hinv2 s2 v1
  store_step with Store.apply_rep s3 v2 a1 _ _ hinv3 h64 h_v2 h_a1 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a1 h_v0 dropping h_v2 hinv3 s3 v2
  store_step with Store.apply_rep s4 v3 a1 _ _ hinv4 h64 h_v3 h_a1 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a1 h_v0 dropping h_v3 hinv4 s4 v3
  store_step with Store.apply_rep s5 v0 v4 _ _ hinv5 h64 h_v0 h_v4 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a1 dropping h_v0 h_v4 hinv5 s5 v0 v4
  store_step with Store.apply_rep s6 v5 a1 _ _ hinv6 h64 h_v5 h_a1 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying dropping h_a1 h_v5 hinv6 s6 v5
  case_done hinv7 hG with h_v6 in EoCases.__eo_prog_bv_ite_equal_children.case_0 using hn_a0 hn_a1

/-- logos's `__eo_prog_bv_ite_equal_children` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fbv_2dite_2dequal_2dchildren.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_bv_ite_equal_children x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_bv_ite_equal_children.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_bv_ite_equal_children
  unfold EoCases.__eo_prog_bv_ite_equal_children.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fbv_2dite_2dequal_2dchildren_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5fbv_2dite_2dequal_2dchildren s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_ite_equal_children x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fbv_2dite_2dequal_2dchildren.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5fbv_2dite_2dequal_2dchildren
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fbv_2dite_2dequal_2dchildren_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_bv_ite_equal_children.case_0

theorem eo__24eo_5fprog_5fbv_2dite_2dequal_2dchildren_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fbv_2dite_2dequal_2dchildren.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5fbv_2dite_2dequal_2dchildren
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fbv_2dite_2dequal_2dchildren s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_bv_ite_equal_children x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fbv_2dite_2dequal_2dchildren_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fbv_2dite_2dequal_2dcond_2d1_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fbv_2dite_2dequal_2dcond_2d1 s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_bv_ite_equal_cond_1.case_0 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_bv_ite_equal_cond_1.case_0 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fbv_2dite_2dequal_2dcond_2d1
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 dropping he_v0 e_v0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_bvite.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 dropping he_v1 hinv1 e_v1 s1
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 dropping h_v1 hinv2 s2 v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_bvite.construct s3 e_v3 (by rw [he_v3]; exact empty_args) hinv3 h64 as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v2 dropping he_v3 hinv3 e_v3 s3
  store_step with Store.apply_rep s4 v3 a0 _ _ hinv4 h64 h_v3 h_a0 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v2 dropping h_v3 hinv4 s4 v3
  store_step with Store.apply_rep s5 v4 a1 _ _ hinv5 h64 h_v4 h_a1 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v2 dropping h_v4 hinv5 s5 v4
  store_step with Store.apply_rep s6 v5 a2 _ _ hinv6 h64 h_v5 h_a2 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_a3 h_v0 h_v2 dropping h_a2 h_v5 hinv6 s6 v5
  store_step with Store.apply_rep s7 v2 v6 _ _ hinv7 h64 h_v2 h_v6 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_a3 h_v0 dropping h_v2 h_v6 hinv7 s7 v2 v6
  store_step with Store.apply_rep s8 v7 a3 _ _ hinv8 h64 h_v7 h_a3 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_a1 h_a3 h_v0 dropping h_v7 hinv8 s8 v7
  store_step with Store.apply_rep s9 v0 v8 _ _ hinv9 h64 h_v0 h_v8 (by ns_tac) (by ns_tac) as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a0 h_a1 h_a3 dropping h_v0 h_v8 hinv9 s9 v0 v8
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo_bvite.construct s10 e_v10 (by rw [he_v10]; exact empty_args) hinv10 h64 as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_a0 h_a1 h_a3 h_v9 dropping he_v10 hinv10 e_v10 s10
  store_step with Store.apply_rep s11 v10 a0 _ _ hinv11 h64 h_v10 h_a0 (by ns_tac) (by ns_tac) as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_a1 h_a3 h_v9 dropping h_a0 h_v10 hinv11 s11 v10
  store_step with Store.apply_rep s12 v11 a1 _ _ hinv12 h64 h_v11 h_a1 (by ns_tac) (by ns_tac) as ⟨v12, s13, hinv13, h_v12⟩ growing hG carrying h_a3 h_v9 dropping h_a1 h_v11 hinv12 s12 v11
  store_step with Store.apply_rep s13 v12 a3 _ _ hinv13 h64 h_v12 h_a3 (by ns_tac) (by ns_tac) as ⟨v13, s14, hinv14, h_v13⟩ growing hG carrying h_v9 dropping h_a3 h_v12 hinv13 s13 v12
  store_step with Store.apply_rep s14 v9 v13 _ _ hinv14 h64 h_v9 h_v13 (by ns_tac) (by ns_tac) as ⟨v14, s15, hinv15, h_v14⟩ growing hG carrying dropping h_v13 h_v9 hinv14 s14 v13 v9
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
  unfold case_0_eo__24eo_5fprog_5fbv_2dite_2dequal_2dcond_2d2
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 dropping he_v0 e_v0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_bvite.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 dropping he_v1 hinv1 e_v1 s1
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 dropping h_v1 hinv2 s2 v1
  store_step with Store.apply_rep s3 v2 a1 _ _ hinv3 h64 h_v2 h_a1 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 dropping h_v2 hinv3 s3 v2
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo_bvite.construct s4 e_v4 (by rw [he_v4]; exact empty_args) hinv4 h64 as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v3 dropping he_v4 hinv4 e_v4 s4
  store_step with Store.apply_rep s5 v4 a0 _ _ hinv5 h64 h_v4 h_a0 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v3 dropping h_v4 hinv5 s5 v4
  store_step with Store.apply_rep s6 v5 a2 _ _ hinv6 h64 h_v5 h_a2 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_a3 h_v0 h_v3 dropping h_a2 h_v5 hinv6 s6 v5
  store_step with Store.apply_rep s7 v6 a3 _ _ hinv7 h64 h_v6 h_a3 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_a3 h_v0 h_v3 dropping h_v6 hinv7 s7 v6
  store_step with Store.apply_rep s8 v3 v7 _ _ hinv8 h64 h_v3 h_v7 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_a1 h_a3 h_v0 dropping h_v3 h_v7 hinv8 s8 v3 v7
  store_step with Store.apply_rep s9 v0 v8 _ _ hinv9 h64 h_v0 h_v8 (by ns_tac) (by ns_tac) as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a0 h_a1 h_a3 dropping h_v0 h_v8 hinv9 s9 v0 v8
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo_bvite.construct s10 e_v10 (by rw [he_v10]; exact empty_args) hinv10 h64 as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_a0 h_a1 h_a3 h_v9 dropping he_v10 hinv10 e_v10 s10
  store_step with Store.apply_rep s11 v10 a0 _ _ hinv11 h64 h_v10 h_a0 (by ns_tac) (by ns_tac) as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_a1 h_a3 h_v9 dropping h_a0 h_v10 hinv11 s11 v10
  store_step with Store.apply_rep s12 v11 a1 _ _ hinv12 h64 h_v11 h_a1 (by ns_tac) (by ns_tac) as ⟨v12, s13, hinv13, h_v12⟩ growing hG carrying h_a3 h_v9 dropping h_a1 h_v11 hinv12 s12 v11
  store_step with Store.apply_rep s13 v12 a3 _ _ hinv13 h64 h_v12 h_a3 (by ns_tac) (by ns_tac) as ⟨v13, s14, hinv14, h_v13⟩ growing hG carrying h_v9 dropping h_a3 h_v12 hinv13 s13 v12
  store_step with Store.apply_rep s14 v9 v13 _ _ hinv14 h64 h_v9 h_v13 (by ns_tac) (by ns_tac) as ⟨v14, s15, hinv15, h_v14⟩ growing hG carrying dropping h_v13 h_v9 hinv14 s14 v13 v9
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
  unfold case_0_eo__24eo_5fprog_5fbv_2dite_2dequal_2dcond_2d3
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 dropping he_v0 e_v0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_bvite.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v0 dropping he_v1 hinv1 e_v1 s1
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v0 dropping h_v1 hinv2 s2 v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_bvite.construct s3 e_v3 (by rw [he_v3]; exact empty_args) hinv3 h64 as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v0 h_v2 dropping he_v3 hinv3 e_v3 s3
  store_step with Store.apply_rep s4 v3 a0 _ _ hinv4 h64 h_v3 h_a0 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v0 h_v2 dropping h_v3 hinv4 s4 v3
  store_step with Store.apply_rep s5 v4 a1 _ _ hinv5 h64 h_v4 h_a1 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v0 h_v2 dropping h_v4 hinv5 s5 v4
  store_step with Store.apply_rep s6 v5 a2 _ _ hinv6 h64 h_v5 h_a2 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_a3 h_a4 h_v0 h_v2 dropping h_a2 h_v5 hinv6 s6 v5
  store_step with Store.apply_rep s7 v2 v6 _ _ hinv7 h64 h_v2 h_v6 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_a3 h_a4 h_v0 dropping h_v2 h_v6 hinv7 s7 v2 v6
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo_bvite.construct s8 e_v8 (by rw [he_v8]; exact empty_args) hinv8 h64 as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_a1 h_a3 h_a4 h_v0 h_v7 dropping he_v8 hinv8 e_v8 s8
  store_step with Store.apply_rep s9 v8 a0 _ _ hinv9 h64 h_v8 h_a0 (by ns_tac) (by ns_tac) as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a0 h_a1 h_a3 h_a4 h_v0 h_v7 dropping h_v8 hinv9 s9 v8
  store_step with Store.apply_rep s10 v9 a3 _ _ hinv10 h64 h_v9 h_a3 (by ns_tac) (by ns_tac) as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_a0 h_a1 h_a4 h_v0 h_v7 dropping h_a3 h_v9 hinv10 s10 v9
  store_step with Store.apply_rep s11 v10 a4 _ _ hinv11 h64 h_v10 h_a4 (by ns_tac) (by ns_tac) as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_a0 h_a1 h_a4 h_v0 h_v7 dropping h_v10 hinv11 s11 v10
  store_step with Store.apply_rep s12 v7 v11 _ _ hinv12 h64 h_v7 h_v11 (by ns_tac) (by ns_tac) as ⟨v12, s13, hinv13, h_v12⟩ growing hG carrying h_a0 h_a1 h_a4 h_v0 dropping h_v11 h_v7 hinv12 s12 v11 v7
  store_step with Store.apply_rep s13 v0 v12 _ _ hinv13 h64 h_v0 h_v12 (by ns_tac) (by ns_tac) as ⟨v13, s14, hinv14, h_v13⟩ growing hG carrying h_a0 h_a1 h_a4 dropping h_v0 h_v12 hinv13 s13 v0 v12
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo_bvite.construct s14 e_v14 (by rw [he_v14]; exact empty_args) hinv14 h64 as ⟨v14, s15, hinv15, h_v14⟩ growing hG carrying h_a0 h_a1 h_a4 h_v13 dropping he_v14 hinv14 e_v14 s14
  store_step with Store.apply_rep s15 v14 a0 _ _ hinv15 h64 h_v14 h_a0 (by ns_tac) (by ns_tac) as ⟨v15, s16, hinv16, h_v15⟩ growing hG carrying h_a1 h_a4 h_v13 dropping h_a0 h_v14 hinv15 s15 v14
  store_step with Store.apply_rep s16 v15 a1 _ _ hinv16 h64 h_v15 h_a1 (by ns_tac) (by ns_tac) as ⟨v16, s17, hinv17, h_v16⟩ growing hG carrying h_a4 h_v13 dropping h_a1 h_v15 hinv16 s16 v15
  store_step with Store.apply_rep s17 v16 a4 _ _ hinv17 h64 h_v16 h_a4 (by ns_tac) (by ns_tac) as ⟨v17, s18, hinv18, h_v17⟩ growing hG carrying h_v13 dropping h_a4 h_v16 hinv17 s17 v16
  store_step with Store.apply_rep s18 v13 v17 _ _ hinv18 h64 h_v13 h_v17 (by ns_tac) (by ns_tac) as ⟨v18, s19, hinv19, h_v18⟩ growing hG carrying dropping h_v13 h_v17 hinv18 s18 v13 v17
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
  unfold case_0_eo__24eo_5fprog_5fbv_2dite_2dmerge_2delse_2delse
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 dropping he_v0 e_v0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_bvite.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 dropping he_v1 hinv1 e_v1 s1
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 dropping h_v1 hinv2 s2 v1
  store_step with Store.apply_rep s3 v2 a3 _ _ hinv3 h64 h_v2 h_a3 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 dropping h_v2 hinv3 s3 v2
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo_bvite.construct s4 e_v4 (by rw [he_v4]; exact empty_args) hinv4 h64 as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v3 dropping he_v4 hinv4 e_v4 s4
  store_step with Store.apply_rep s5 v4 a1 _ _ hinv5 h64 h_v4 h_a1 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v3 dropping h_v4 hinv5 s5 v4
  store_step with Store.apply_rep s6 v5 a2 _ _ hinv6 h64 h_v5 h_a2 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v3 dropping h_v5 hinv6 s6 v5
  store_step with Store.apply_rep s7 v6 a3 _ _ hinv7 h64 h_v6 h_a3 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v3 dropping h_v6 hinv7 s7 v6
  store_step with Store.apply_rep s8 v3 v7 _ _ hinv8 h64 h_v3 h_v7 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 dropping h_v3 h_v7 hinv8 s8 v3 v7
  store_step with Store.apply_rep s9 v0 v8 _ _ hinv9 h64 h_v0 h_v8 (by ns_tac) (by ns_tac) as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 dropping h_v0 h_v8 hinv9 s9 v0 v8
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo_bvite.construct s10 e_v10 (by rw [he_v10]; exact empty_args) hinv10 h64 as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v9 dropping he_v10 hinv10 e_v10 s10
  step as ⟨e_v11, he_v11⟩
  store_step with CtorSpec.eo_bvand.construct s11 e_v11 (by rw [he_v11]; exact empty_args) hinv11 h64 as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v9 h_v10 dropping he_v11 hinv11 e_v11 s11
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo_bvnot.construct s12 e_v12 (by rw [he_v12]; exact empty_args) hinv12 h64 as ⟨v12, s13, hinv13, h_v12⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v9 h_v10 h_v11 dropping he_v12 hinv12 e_v12 s12
  store_step with Store.apply_rep s13 v12 a0 _ _ hinv13 h64 h_v12 h_a0 (by ns_tac) (by ns_tac) as ⟨v13, s14, hinv14, h_v13⟩ growing hG carrying h_a1 h_a2 h_a3 h_v9 h_v10 h_v11 dropping h_a0 h_v12 hinv13 s13 v12
  store_step with Store.apply_rep s14 v11 v13 _ _ hinv14 h64 h_v11 h_v13 (by ns_tac) (by ns_tac) as ⟨v14, s15, hinv15, h_v14⟩ growing hG carrying h_a1 h_a2 h_a3 h_v9 h_v10 dropping h_v11 h_v13 hinv14 s14 v11 v13
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo_bvand.construct s15 e_v15 (by rw [he_v15]; exact empty_args) hinv15 h64 as ⟨v15, s16, hinv16, h_v15⟩ growing hG carrying h_a1 h_a2 h_a3 h_v9 h_v10 h_v14 dropping he_v15 hinv15 e_v15 s15
  store_step with Store.apply_rep s16 v15 a1 _ _ hinv16 h64 h_v15 h_a1 (by ns_tac) (by ns_tac) as ⟨v16, s17, hinv17, h_v16⟩ growing hG carrying h_a2 h_a3 h_v9 h_v10 h_v14 dropping h_a1 h_v15 hinv16 s16 v15
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s17 1#u32 1#u32 (1) (1) rfl rfl (by unfold Tree.okBv; norm_num) hinv17 h64 as ⟨v17, s18, hinv18, h_v17⟩ growing hG carrying h_a2 h_a3 h_v9 h_v10 h_v14 h_v16 dropping hinv17 s17
  store_step with Store.apply_rep s18 v16 v17 _ _ hinv18 h64 h_v16 h_v17 (by ns_tac) (by ns_tac) as ⟨v18, s19, hinv19, h_v18⟩ growing hG carrying h_a2 h_a3 h_v9 h_v10 h_v14 dropping h_v16 h_v17 hinv18 s18 v16 v17
  store_step with Store.apply_rep s19 v14 v18 _ _ hinv19 h64 h_v14 h_v18 (by ns_tac) (by ns_tac) as ⟨v19, s20, hinv20, h_v19⟩ growing hG carrying h_a2 h_a3 h_v9 h_v10 dropping h_v14 h_v18 hinv19 s19 v14 v18
  store_step with Store.apply_rep s20 v10 v19 _ _ hinv20 h64 h_v10 h_v19 (by ns_tac) (by ns_tac) as ⟨v20, s21, hinv21, h_v20⟩ growing hG carrying h_a2 h_a3 h_v9 dropping h_v10 h_v19 hinv20 s20 v10 v19
  store_step with Store.apply_rep s21 v20 a2 _ _ hinv21 h64 h_v20 h_a2 (by ns_tac) (by ns_tac) as ⟨v21, s22, hinv22, h_v21⟩ growing hG carrying h_a3 h_v9 dropping h_a2 h_v20 hinv21 s21 v20
  store_step with Store.apply_rep s22 v21 a3 _ _ hinv22 h64 h_v21 h_a3 (by ns_tac) (by ns_tac) as ⟨v22, s23, hinv23, h_v22⟩ growing hG carrying h_v9 dropping h_a3 h_v21 hinv22 s22 v21
  store_step with Store.apply_rep s23 v9 v22 _ _ hinv23 h64 h_v9 h_v22 (by ns_tac) (by ns_tac) as ⟨v23, s24, hinv24, h_v23⟩ growing hG carrying dropping h_v22 h_v9 hinv23 s23 v22 v9
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
  unfold case_0_eo__24eo_5fprog_5fbv_2dite_2dmerge_2delse_2dif
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 dropping he_v0 e_v0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_bvite.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 dropping he_v1 hinv1 e_v1 s1
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 dropping h_v1 hinv2 s2 v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_bvite.construct s3 e_v3 (by rw [he_v3]; exact empty_args) hinv3 h64 as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v2 dropping he_v3 hinv3 e_v3 s3
  store_step with Store.apply_rep s4 v3 a1 _ _ hinv4 h64 h_v3 h_a1 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v2 dropping h_v3 hinv4 s4 v3
  store_step with Store.apply_rep s5 v4 a2 _ _ hinv5 h64 h_v4 h_a2 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v2 dropping h_v4 hinv5 s5 v4
  store_step with Store.apply_rep s6 v5 a3 _ _ hinv6 h64 h_v5 h_a3 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v2 dropping h_v5 hinv6 s6 v5
  store_step with Store.apply_rep s7 v2 v6 _ _ hinv7 h64 h_v2 h_v6 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 dropping h_v2 h_v6 hinv7 s7 v2 v6
  store_step with Store.apply_rep s8 v7 a3 _ _ hinv8 h64 h_v7 h_a3 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 dropping h_v7 hinv8 s8 v7
  store_step with Store.apply_rep s9 v0 v8 _ _ hinv9 h64 h_v0 h_v8 (by ns_tac) (by ns_tac) as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 dropping h_v0 h_v8 hinv9 s9 v0 v8
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo_bvite.construct s10 e_v10 (by rw [he_v10]; exact empty_args) hinv10 h64 as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v9 dropping he_v10 hinv10 e_v10 s10
  step as ⟨e_v11, he_v11⟩
  store_step with CtorSpec.eo_bvand.construct s11 e_v11 (by rw [he_v11]; exact empty_args) hinv11 h64 as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v9 h_v10 dropping he_v11 hinv11 e_v11 s11
  store_step with Store.apply_rep s12 v11 a0 _ _ hinv12 h64 h_v11 h_a0 (by ns_tac) (by ns_tac) as ⟨v12, s13, hinv13, h_v12⟩ growing hG carrying h_a1 h_a2 h_a3 h_v9 h_v10 dropping h_a0 h_v11 hinv12 s12 v11
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo_bvand.construct s13 e_v13 (by rw [he_v13]; exact empty_args) hinv13 h64 as ⟨v13, s14, hinv14, h_v13⟩ growing hG carrying h_a1 h_a2 h_a3 h_v9 h_v10 h_v12 dropping he_v13 hinv13 e_v13 s13
  store_step with Store.apply_rep s14 v13 a1 _ _ hinv14 h64 h_v13 h_a1 (by ns_tac) (by ns_tac) as ⟨v14, s15, hinv15, h_v14⟩ growing hG carrying h_a2 h_a3 h_v9 h_v10 h_v12 dropping h_a1 h_v13 hinv14 s14 v13
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s15 1#u32 1#u32 (1) (1) rfl rfl (by unfold Tree.okBv; norm_num) hinv15 h64 as ⟨v15, s16, hinv16, h_v15⟩ growing hG carrying h_a2 h_a3 h_v9 h_v10 h_v12 h_v14 dropping hinv15 s15
  store_step with Store.apply_rep s16 v14 v15 _ _ hinv16 h64 h_v14 h_v15 (by ns_tac) (by ns_tac) as ⟨v16, s17, hinv17, h_v16⟩ growing hG carrying h_a2 h_a3 h_v9 h_v10 h_v12 dropping h_v14 h_v15 hinv16 s16 v14 v15
  store_step with Store.apply_rep s17 v12 v16 _ _ hinv17 h64 h_v12 h_v16 (by ns_tac) (by ns_tac) as ⟨v17, s18, hinv18, h_v17⟩ growing hG carrying h_a2 h_a3 h_v9 h_v10 dropping h_v12 h_v16 hinv17 s17 v12 v16
  store_step with Store.apply_rep s18 v10 v17 _ _ hinv18 h64 h_v10 h_v17 (by ns_tac) (by ns_tac) as ⟨v18, s19, hinv19, h_v18⟩ growing hG carrying h_a2 h_a3 h_v9 dropping h_v10 h_v17 hinv18 s18 v10 v17
  store_step with Store.apply_rep s19 v18 a2 _ _ hinv19 h64 h_v18 h_a2 (by ns_tac) (by ns_tac) as ⟨v19, s20, hinv20, h_v19⟩ growing hG carrying h_a3 h_v9 dropping h_a2 h_v18 hinv19 s19 v18
  store_step with Store.apply_rep s20 v19 a3 _ _ hinv20 h64 h_v19 h_a3 (by ns_tac) (by ns_tac) as ⟨v20, s21, hinv21, h_v20⟩ growing hG carrying h_v9 dropping h_a3 h_v19 hinv20 s20 v19
  store_step with Store.apply_rep s21 v9 v20 _ _ hinv21 h64 h_v9 h_v20 (by ns_tac) (by ns_tac) as ⟨v21, s22, hinv22, h_v21⟩ growing hG carrying dropping h_v20 h_v9 hinv21 s21 v20 v9
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
  unfold case_0_eo__24eo_5fprog_5fbv_2dite_2dmerge_2dthen_2delse
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 dropping he_v0 e_v0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_bvite.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 dropping he_v1 hinv1 e_v1 s1
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 dropping h_v1 hinv2 s2 v1
  store_step with Store.apply_rep s3 v2 a2 _ _ hinv3 h64 h_v2 h_a2 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 dropping h_v2 hinv3 s3 v2
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo_bvite.construct s4 e_v4 (by rw [he_v4]; exact empty_args) hinv4 h64 as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v3 dropping he_v4 hinv4 e_v4 s4
  store_step with Store.apply_rep s5 v4 a1 _ _ hinv5 h64 h_v4 h_a1 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v3 dropping h_v4 hinv5 s5 v4
  store_step with Store.apply_rep s6 v5 a2 _ _ hinv6 h64 h_v5 h_a2 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v3 dropping h_v5 hinv6 s6 v5
  store_step with Store.apply_rep s7 v6 a3 _ _ hinv7 h64 h_v6 h_a3 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v3 dropping h_v6 hinv7 s7 v6
  store_step with Store.apply_rep s8 v3 v7 _ _ hinv8 h64 h_v3 h_v7 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 dropping h_v3 h_v7 hinv8 s8 v3 v7
  store_step with Store.apply_rep s9 v0 v8 _ _ hinv9 h64 h_v0 h_v8 (by ns_tac) (by ns_tac) as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 dropping h_v0 h_v8 hinv9 s9 v0 v8
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo_bvite.construct s10 e_v10 (by rw [he_v10]; exact empty_args) hinv10 h64 as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v9 dropping he_v10 hinv10 e_v10 s10
  step as ⟨e_v11, he_v11⟩
  store_step with CtorSpec.eo_bvand.construct s11 e_v11 (by rw [he_v11]; exact empty_args) hinv11 h64 as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v9 h_v10 dropping he_v11 hinv11 e_v11 s11
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo_bvnot.construct s12 e_v12 (by rw [he_v12]; exact empty_args) hinv12 h64 as ⟨v12, s13, hinv13, h_v12⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v9 h_v10 h_v11 dropping he_v12 hinv12 e_v12 s12
  store_step with Store.apply_rep s13 v12 a0 _ _ hinv13 h64 h_v12 h_a0 (by ns_tac) (by ns_tac) as ⟨v13, s14, hinv14, h_v13⟩ growing hG carrying h_a1 h_a2 h_a3 h_v9 h_v10 h_v11 dropping h_a0 h_v12 hinv13 s13 v12
  store_step with Store.apply_rep s14 v11 v13 _ _ hinv14 h64 h_v11 h_v13 (by ns_tac) (by ns_tac) as ⟨v14, s15, hinv15, h_v14⟩ growing hG carrying h_a1 h_a2 h_a3 h_v9 h_v10 dropping h_v11 h_v13 hinv14 s14 v11 v13
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo_bvand.construct s15 e_v15 (by rw [he_v15]; exact empty_args) hinv15 h64 as ⟨v15, s16, hinv16, h_v15⟩ growing hG carrying h_a1 h_a2 h_a3 h_v9 h_v10 h_v14 dropping he_v15 hinv15 e_v15 s15
  step as ⟨e_v16, he_v16⟩
  store_step with CtorSpec.eo_bvnot.construct s16 e_v16 (by rw [he_v16]; exact empty_args) hinv16 h64 as ⟨v16, s17, hinv17, h_v16⟩ growing hG carrying h_a1 h_a2 h_a3 h_v9 h_v10 h_v14 h_v15 dropping he_v16 hinv16 e_v16 s16
  store_step with Store.apply_rep s17 v16 a1 _ _ hinv17 h64 h_v16 h_a1 (by ns_tac) (by ns_tac) as ⟨v17, s18, hinv18, h_v17⟩ growing hG carrying h_a2 h_a3 h_v9 h_v10 h_v14 h_v15 dropping h_a1 h_v16 hinv17 s17 v16
  store_step with Store.apply_rep s18 v15 v17 _ _ hinv18 h64 h_v15 h_v17 (by ns_tac) (by ns_tac) as ⟨v18, s19, hinv19, h_v18⟩ growing hG carrying h_a2 h_a3 h_v9 h_v10 h_v14 dropping h_v15 h_v17 hinv18 s18 v15 v17
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s19 1#u32 1#u32 (1) (1) rfl rfl (by unfold Tree.okBv; norm_num) hinv19 h64 as ⟨v19, s20, hinv20, h_v19⟩ growing hG carrying h_a2 h_a3 h_v9 h_v10 h_v14 h_v18 dropping hinv19 s19
  store_step with Store.apply_rep s20 v18 v19 _ _ hinv20 h64 h_v18 h_v19 (by ns_tac) (by ns_tac) as ⟨v20, s21, hinv21, h_v20⟩ growing hG carrying h_a2 h_a3 h_v9 h_v10 h_v14 dropping h_v18 h_v19 hinv20 s20 v18 v19
  store_step with Store.apply_rep s21 v14 v20 _ _ hinv21 h64 h_v14 h_v20 (by ns_tac) (by ns_tac) as ⟨v21, s22, hinv22, h_v21⟩ growing hG carrying h_a2 h_a3 h_v9 h_v10 dropping h_v14 h_v20 hinv21 s21 v14 v20
  store_step with Store.apply_rep s22 v10 v21 _ _ hinv22 h64 h_v10 h_v21 (by ns_tac) (by ns_tac) as ⟨v22, s23, hinv23, h_v22⟩ growing hG carrying h_a2 h_a3 h_v9 dropping h_v10 h_v21 hinv22 s22 v10 v21
  store_step with Store.apply_rep s23 v22 a3 _ _ hinv23 h64 h_v22 h_a3 (by ns_tac) (by ns_tac) as ⟨v23, s24, hinv24, h_v23⟩ growing hG carrying h_a2 h_v9 dropping h_a3 h_v22 hinv23 s23 v22
  store_step with Store.apply_rep s24 v23 a2 _ _ hinv24 h64 h_v23 h_a2 (by ns_tac) (by ns_tac) as ⟨v24, s25, hinv25, h_v24⟩ growing hG carrying h_v9 dropping h_a2 h_v23 hinv24 s24 v23
  store_step with Store.apply_rep s25 v9 v24 _ _ hinv25 h64 h_v9 h_v24 (by ns_tac) (by ns_tac) as ⟨v25, s26, hinv26, h_v25⟩ growing hG carrying dropping h_v24 h_v9 hinv25 s25 v24 v9
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
  unfold case_0_eo__24eo_5fprog_5fbv_2dite_2dmerge_2dthen_2dif
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 dropping he_v0 e_v0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_bvite.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 dropping he_v1 hinv1 e_v1 s1
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 dropping h_v1 hinv2 s2 v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_bvite.construct s3 e_v3 (by rw [he_v3]; exact empty_args) hinv3 h64 as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v2 dropping he_v3 hinv3 e_v3 s3
  store_step with Store.apply_rep s4 v3 a1 _ _ hinv4 h64 h_v3 h_a1 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v2 dropping h_v3 hinv4 s4 v3
  store_step with Store.apply_rep s5 v4 a2 _ _ hinv5 h64 h_v4 h_a2 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v2 dropping h_v4 hinv5 s5 v4
  store_step with Store.apply_rep s6 v5 a3 _ _ hinv6 h64 h_v5 h_a3 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v2 dropping h_v5 hinv6 s6 v5
  store_step with Store.apply_rep s7 v2 v6 _ _ hinv7 h64 h_v2 h_v6 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 dropping h_v2 h_v6 hinv7 s7 v2 v6
  store_step with Store.apply_rep s8 v7 a2 _ _ hinv8 h64 h_v7 h_a2 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 dropping h_v7 hinv8 s8 v7
  store_step with Store.apply_rep s9 v0 v8 _ _ hinv9 h64 h_v0 h_v8 (by ns_tac) (by ns_tac) as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 dropping h_v0 h_v8 hinv9 s9 v0 v8
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo_bvite.construct s10 e_v10 (by rw [he_v10]; exact empty_args) hinv10 h64 as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v9 dropping he_v10 hinv10 e_v10 s10
  step as ⟨e_v11, he_v11⟩
  store_step with CtorSpec.eo_bvand.construct s11 e_v11 (by rw [he_v11]; exact empty_args) hinv11 h64 as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v9 h_v10 dropping he_v11 hinv11 e_v11 s11
  store_step with Store.apply_rep s12 v11 a0 _ _ hinv12 h64 h_v11 h_a0 (by ns_tac) (by ns_tac) as ⟨v12, s13, hinv13, h_v12⟩ growing hG carrying h_a1 h_a2 h_a3 h_v9 h_v10 dropping h_a0 h_v11 hinv12 s12 v11
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo_bvand.construct s13 e_v13 (by rw [he_v13]; exact empty_args) hinv13 h64 as ⟨v13, s14, hinv14, h_v13⟩ growing hG carrying h_a1 h_a2 h_a3 h_v9 h_v10 h_v12 dropping he_v13 hinv13 e_v13 s13
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo_bvnot.construct s14 e_v14 (by rw [he_v14]; exact empty_args) hinv14 h64 as ⟨v14, s15, hinv15, h_v14⟩ growing hG carrying h_a1 h_a2 h_a3 h_v9 h_v10 h_v12 h_v13 dropping he_v14 hinv14 e_v14 s14
  store_step with Store.apply_rep s15 v14 a1 _ _ hinv15 h64 h_v14 h_a1 (by ns_tac) (by ns_tac) as ⟨v15, s16, hinv16, h_v15⟩ growing hG carrying h_a2 h_a3 h_v9 h_v10 h_v12 h_v13 dropping h_a1 h_v14 hinv15 s15 v14
  store_step with Store.apply_rep s16 v13 v15 _ _ hinv16 h64 h_v13 h_v15 (by ns_tac) (by ns_tac) as ⟨v16, s17, hinv17, h_v16⟩ growing hG carrying h_a2 h_a3 h_v9 h_v10 h_v12 dropping h_v13 h_v15 hinv16 s16 v13 v15
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s17 1#u32 1#u32 (1) (1) rfl rfl (by unfold Tree.okBv; norm_num) hinv17 h64 as ⟨v17, s18, hinv18, h_v17⟩ growing hG carrying h_a2 h_a3 h_v9 h_v10 h_v12 h_v16 dropping hinv17 s17
  store_step with Store.apply_rep s18 v16 v17 _ _ hinv18 h64 h_v16 h_v17 (by ns_tac) (by ns_tac) as ⟨v18, s19, hinv19, h_v18⟩ growing hG carrying h_a2 h_a3 h_v9 h_v10 h_v12 dropping h_v16 h_v17 hinv18 s18 v16 v17
  store_step with Store.apply_rep s19 v12 v18 _ _ hinv19 h64 h_v12 h_v18 (by ns_tac) (by ns_tac) as ⟨v19, s20, hinv20, h_v19⟩ growing hG carrying h_a2 h_a3 h_v9 h_v10 dropping h_v12 h_v18 hinv19 s19 v12 v18
  store_step with Store.apply_rep s20 v10 v19 _ _ hinv20 h64 h_v10 h_v19 (by ns_tac) (by ns_tac) as ⟨v20, s21, hinv21, h_v20⟩ growing hG carrying h_a2 h_a3 h_v9 dropping h_v10 h_v19 hinv20 s20 v10 v19
  store_step with Store.apply_rep s21 v20 a3 _ _ hinv21 h64 h_v20 h_a3 (by ns_tac) (by ns_tac) as ⟨v21, s22, hinv22, h_v21⟩ growing hG carrying h_a2 h_v9 dropping h_a3 h_v20 hinv21 s21 v20
  store_step with Store.apply_rep s22 v21 a2 _ _ hinv22 h64 h_v21 h_a2 (by ns_tac) (by ns_tac) as ⟨v22, s23, hinv23, h_v22⟩ growing hG carrying h_v9 dropping h_a2 h_v21 hinv22 s22 v21
  store_step with Store.apply_rep s23 v9 v22 _ _ hinv23 h64 h_v9 h_v22 (by ns_tac) (by ns_tac) as ⟨v23, s24, hinv24, h_v23⟩ growing hG carrying dropping h_v22 h_v9 hinv23 s23 v22 v9
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
  unfold case_0_eo__24eo_5fprog_5fbv_2dite_2dwidth_2done
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 dropping he_v0 e_v0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_ite.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0 dropping he_v1 hinv1 e_v1 s1
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__3d.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_v0 h_v1 dropping he_v2 hinv2 e_v2 s2
  store_step with Store.apply_rep s3 v2 a0 _ _ hinv3 h64 h_v2 h_a0 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_v0 h_v1 dropping h_v2 hinv3 s3 v2
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s4 1#u32 (1) (by scalar_tac) hinv4 h64 as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_v0 h_v1 h_v3 dropping hinv4 s4
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s5 e_v5 (by rw [he_v5]; rfl) h_v4 hinv5 h64 as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_v0 h_v1 h_v3 dropping h_v4 he_v5 hinv5 e_v5 s5 v4
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s6 1#u32 (1) (by scalar_tac) hinv6 h64 as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_v0 h_v1 h_v3 h_v5 dropping hinv6 s6
  store_step with Store.apply_rep s7 v5 v6 _ _ hinv7 h64 h_v5 h_v6 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_v0 h_v1 h_v3 dropping h_v5 h_v6 hinv7 s7 v5 v6
  store_step with Store.apply_rep s8 v3 v7 _ _ hinv8 h64 h_v3 h_v7 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_v0 h_v1 dropping h_v3 h_v7 hinv8 s8 v3 v7
  store_step with Store.apply_rep s9 v1 v8 _ _ hinv9 h64 h_v1 h_v8 (by ns_tac) (by ns_tac) as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a0 h_v0 dropping h_v1 h_v8 hinv9 s9 v1 v8
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s10 1#u32 (1) (by scalar_tac) hinv10 h64 as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_a0 h_v0 h_v9 dropping hinv10 s10
  step as ⟨e_v11, he_v11⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s11 e_v11 (by rw [he_v11]; rfl) h_v10 hinv11 h64 as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_a0 h_v0 h_v9 dropping h_v10 he_v11 hinv11 e_v11 s11 v10
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s12 1#u32 (1) (by scalar_tac) hinv12 h64 as ⟨v12, s13, hinv13, h_v12⟩ growing hG carrying h_a0 h_v0 h_v9 h_v11 dropping hinv12 s12
  store_step with Store.apply_rep s13 v11 v12 _ _ hinv13 h64 h_v11 h_v12 (by ns_tac) (by ns_tac) as ⟨v13, s14, hinv14, h_v13⟩ growing hG carrying h_a0 h_v0 h_v9 dropping h_v11 h_v12 hinv13 s13 v11 v12
  store_step with Store.apply_rep s14 v9 v13 _ _ hinv14 h64 h_v9 h_v13 (by ns_tac) (by ns_tac) as ⟨v14, s15, hinv15, h_v14⟩ growing hG carrying h_a0 h_v0 dropping h_v13 h_v9 hinv14 s14 v13 v9
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s15 1#u32 (1) (by scalar_tac) hinv15 h64 as ⟨v15, s16, hinv16, h_v15⟩ growing hG carrying h_a0 h_v0 h_v14 dropping hinv15 s15
  step as ⟨e_v16, he_v16⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s16 e_v16 (by rw [he_v16]; rfl) h_v15 hinv16 h64 as ⟨v16, s17, hinv17, h_v16⟩ growing hG carrying h_a0 h_v0 h_v14 dropping h_v15 he_v16 hinv16 e_v16 s16 v15
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s17 0#u32 (0) (by scalar_tac) hinv17 h64 as ⟨v17, s18, hinv18, h_v17⟩ growing hG carrying h_a0 h_v0 h_v14 h_v16 dropping hinv17 s17
  store_step with Store.apply_rep s18 v16 v17 _ _ hinv18 h64 h_v16 h_v17 (by ns_tac) (by ns_tac) as ⟨v18, s19, hinv19, h_v18⟩ growing hG carrying h_a0 h_v0 h_v14 dropping h_v16 h_v17 hinv18 s18 v16 v17
  store_step with Store.apply_rep s19 v14 v18 _ _ hinv19 h64 h_v14 h_v18 (by ns_tac) (by ns_tac) as ⟨v19, s20, hinv20, h_v19⟩ growing hG carrying h_a0 h_v0 dropping h_v14 h_v18 hinv19 s19 v14 v18
  store_step with Store.apply_rep s20 v0 v19 _ _ hinv20 h64 h_v0 h_v19 (by ns_tac) (by ns_tac) as ⟨v20, s21, hinv21, h_v20⟩ growing hG carrying h_a0 dropping h_v0 h_v19 hinv20 s20 v0 v19
  store_step with Store.apply_rep s21 v20 a0 _ _ hinv21 h64 h_v20 h_a0 (by ns_tac) (by ns_tac) as ⟨v21, s22, hinv22, h_v21⟩ growing hG carrying dropping h_a0 h_v20 hinv21 s21 v20
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
  unfold case_0_eo__24eo_5fprog_5fbv_2dite_2dwidth_2done_2dnot
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 dropping he_v0 e_v0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_ite.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0 dropping he_v1 hinv1 e_v1 s1
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__3d.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_v0 h_v1 dropping he_v2 hinv2 e_v2 s2
  store_step with Store.apply_rep s3 v2 a0 _ _ hinv3 h64 h_v2 h_a0 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_v0 h_v1 dropping h_v2 hinv3 s3 v2
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s4 1#u32 (1) (by scalar_tac) hinv4 h64 as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_v0 h_v1 h_v3 dropping hinv4 s4
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s5 e_v5 (by rw [he_v5]; rfl) h_v4 hinv5 h64 as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_v0 h_v1 h_v3 dropping h_v4 he_v5 hinv5 e_v5 s5 v4
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s6 0#u32 (0) (by scalar_tac) hinv6 h64 as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_v0 h_v1 h_v3 h_v5 dropping hinv6 s6
  store_step with Store.apply_rep s7 v5 v6 _ _ hinv7 h64 h_v5 h_v6 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_v0 h_v1 h_v3 dropping h_v5 h_v6 hinv7 s7 v5 v6
  store_step with Store.apply_rep s8 v3 v7 _ _ hinv8 h64 h_v3 h_v7 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_v0 h_v1 dropping h_v3 h_v7 hinv8 s8 v3 v7
  store_step with Store.apply_rep s9 v1 v8 _ _ hinv9 h64 h_v1 h_v8 (by ns_tac) (by ns_tac) as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a0 h_v0 dropping h_v1 h_v8 hinv9 s9 v1 v8
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s10 1#u32 (1) (by scalar_tac) hinv10 h64 as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_a0 h_v0 h_v9 dropping hinv10 s10
  step as ⟨e_v11, he_v11⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s11 e_v11 (by rw [he_v11]; rfl) h_v10 hinv11 h64 as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_a0 h_v0 h_v9 dropping h_v10 he_v11 hinv11 e_v11 s11 v10
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s12 1#u32 (1) (by scalar_tac) hinv12 h64 as ⟨v12, s13, hinv13, h_v12⟩ growing hG carrying h_a0 h_v0 h_v9 h_v11 dropping hinv12 s12
  store_step with Store.apply_rep s13 v11 v12 _ _ hinv13 h64 h_v11 h_v12 (by ns_tac) (by ns_tac) as ⟨v13, s14, hinv14, h_v13⟩ growing hG carrying h_a0 h_v0 h_v9 dropping h_v11 h_v12 hinv13 s13 v11 v12
  store_step with Store.apply_rep s14 v9 v13 _ _ hinv14 h64 h_v9 h_v13 (by ns_tac) (by ns_tac) as ⟨v14, s15, hinv15, h_v14⟩ growing hG carrying h_a0 h_v0 dropping h_v13 h_v9 hinv14 s14 v13 v9
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s15 1#u32 (1) (by scalar_tac) hinv15 h64 as ⟨v15, s16, hinv16, h_v15⟩ growing hG carrying h_a0 h_v0 h_v14 dropping hinv15 s15
  step as ⟨e_v16, he_v16⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s16 e_v16 (by rw [he_v16]; rfl) h_v15 hinv16 h64 as ⟨v16, s17, hinv17, h_v16⟩ growing hG carrying h_a0 h_v0 h_v14 dropping h_v15 he_v16 hinv16 e_v16 s16 v15
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s17 0#u32 (0) (by scalar_tac) hinv17 h64 as ⟨v17, s18, hinv18, h_v17⟩ growing hG carrying h_a0 h_v0 h_v14 h_v16 dropping hinv17 s17
  store_step with Store.apply_rep s18 v16 v17 _ _ hinv18 h64 h_v16 h_v17 (by ns_tac) (by ns_tac) as ⟨v18, s19, hinv19, h_v18⟩ growing hG carrying h_a0 h_v0 h_v14 dropping h_v16 h_v17 hinv18 s18 v16 v17
  store_step with Store.apply_rep s19 v14 v18 _ _ hinv19 h64 h_v14 h_v18 (by ns_tac) (by ns_tac) as ⟨v19, s20, hinv20, h_v19⟩ growing hG carrying h_a0 h_v0 dropping h_v14 h_v18 hinv19 s19 v14 v18
  store_step with Store.apply_rep s20 v0 v19 _ _ hinv20 h64 h_v0 h_v19 (by ns_tac) (by ns_tac) as ⟨v20, s21, hinv21, h_v20⟩ growing hG carrying h_a0 dropping h_v0 h_v19 hinv20 s20 v0 v19
  step as ⟨e_v21, he_v21⟩
  store_step with CtorSpec.eo_bvnot.construct s21 e_v21 (by rw [he_v21]; exact empty_args) hinv21 h64 as ⟨v21, s22, hinv22, h_v21⟩ growing hG carrying h_a0 h_v20 dropping he_v21 hinv21 e_v21 s21
  store_step with Store.apply_rep s22 v21 a0 _ _ hinv22 h64 h_v21 h_a0 (by ns_tac) (by ns_tac) as ⟨v22, s23, hinv23, h_v22⟩ growing hG carrying h_v20 dropping h_a0 h_v21 hinv22 s22 v21
  store_step with Store.apply_rep s23 v20 v22 _ _ hinv23 h64 h_v20 h_v22 (by ns_tac) (by ns_tac) as ⟨v23, s24, hinv24, h_v23⟩ growing hG carrying dropping h_v20 h_v22 hinv23 s23 v20 v22
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
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 dropping he_v0 e_v0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_bvlshr.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0 dropping he_v1 hinv1 e_v1 s1
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 dropping h_v1 hinv2 s2 v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s3 e_v3 (by rw [he_v3]; rfl) h_a1 hinv3 h64 as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_v0 h_v2 dropping h_a1 he_v3 hinv3 e_v3 s3
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s4 0#u32 (0) (by scalar_tac) hinv4 h64 as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_v0 h_v2 h_v3 dropping hinv4 s4
  store_step with Store.apply_rep s5 v3 v4 _ _ hinv5 h64 h_v3 h_v4 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_v0 h_v2 dropping h_v3 h_v4 hinv5 s5 v3 v4
  store_step with Store.apply_rep s6 v2 v5 _ _ hinv6 h64 h_v2 h_v5 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_v0 dropping h_v2 h_v5 hinv6 s6 v2 v5
  store_step with Store.apply_rep s7 v0 v6 _ _ hinv7 h64 h_v0 h_v6 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 dropping h_v0 h_v6 hinv7 s7 v0 v6
  store_step with Store.apply_rep s8 v7 a0 _ _ hinv8 h64 h_v7 h_a0 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying dropping h_a0 h_v7 hinv8 s8 v7
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
  unfold case_0_eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d1
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a4 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_bv_lshr_by_const_1.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_lshr_by_const_1.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_lshr_by_const_1.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a5 h_v4 h_v6 h_v7 dropping h_a4 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_lshr_by_const_1.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_lshr_by_const_1.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_lshr_by_const_1.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__3c.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a5 h_v4 h_v11 h_v13 h_v14 dropping h_v10 h_v6 h_v7 h_v8 he_v15 hinv1 e_v15 s1 v10 v6 v7 v8
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_lshr_by_const_1.case_0
  pat_same v14 a1 with h_v14 h_a1 using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_lshr_by_const_1.case_0
  pat_unapply h_v11 as ⟨v17, v18, x_v17, x_v18, h_v17, h_v18, hn_v17, hn_v18⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_lshr_by_const_1.case_0
  step as ⟨e_v19, he_v19⟩
  store_step with CtorSpec.eo__40bvsize.construct s2 e_v19 (by rw [he_v19]; exact empty_args) hinv2 h64 as ⟨v19, s3, hinv3, h_v19⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a5 h_v4 h_v17 h_v18 dropping h_v11 h_v13 h_v14 h_v15 he_v19 hinv2 e_v19 s2 v11 v13 v14 v15
  pat_same v17 v19 with h_v17 h_v19 using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_lshr_by_const_1.case_0
  pat_same v18 a0 with h_v18 h_a0 using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_lshr_by_const_1.case_0
  store_step with Store.literal_boolean_spec s3 true hinv3 h64 as ⟨v20, s4, hinv4, h_v20⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a5 h_v4 dropping h_v17 h_v18 h_v19 hinv3 s3 v17 v18 v19
  pat_same v4 v20 with h_v4 h_v20 using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_lshr_by_const_1.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a5 as ⟨v22, x_v22, h_v22⟩ else hinv4 hG in EoCases.__eo_prog_bv_lshr_by_const_1.case_0
  pat_unapply h_v22 as ⟨v24, v25, x_v24, x_v25, h_v24, h_v25, hn_v24, hn_v25⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_lshr_by_const_1.case_0
  pat_unapply h_v24 as ⟨v27, v28, x_v27, x_v28, h_v27, h_v28, hn_v27, hn_v28⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_lshr_by_const_1.case_0
  step as ⟨e_v29, he_v29⟩
  store_step with CtorSpec.eo__3d.construct s4 e_v29 (by rw [he_v29]; exact empty_args) hinv4 h64 as ⟨v29, s5, hinv5, h_v29⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v25 h_v27 h_v28 dropping h_a5 h_v20 h_v22 h_v24 h_v4 he_v29 hinv4 e_v29 s4 v20 v22 v24 v4
  pat_same v27 v29 with h_v27 h_v29 using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_lshr_by_const_1.case_0
  pat_same v28 a3 with h_v28 h_a3 using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_lshr_by_const_1.case_0
  pat_unapply h_v25 as ⟨v31, v32, x_v31, x_v32, h_v31, h_v32, hn_v31, hn_v32⟩ using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_lshr_by_const_1.case_0
  pat_unapply h_v31 as ⟨v34, v35, x_v34, x_v35, h_v34, h_v35, hn_v34, hn_v35⟩ using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_lshr_by_const_1.case_0
  step as ⟨e_v36, he_v36⟩
  store_step with CtorSpec.eo__2d.construct s5 e_v36 (by rw [he_v36]; exact empty_args) hinv5 h64 as ⟨v36, s6, hinv6, h_v36⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v32 h_v34 h_v35 dropping h_v25 h_v27 h_v28 h_v29 h_v31 he_v36 hinv5 e_v36 s5 v25 v27 v28 v29 v31
  pat_same v34 v36 with h_v34 h_v36 using hinv6 else hinv6 hG in EoCases.__eo_prog_bv_lshr_by_const_1.case_0
  pat_unapply h_v35 as ⟨v38, v39, x_v38, x_v39, h_v38, h_v39, hn_v38, hn_v39⟩ using hinv6 else hinv6 hG in EoCases.__eo_prog_bv_lshr_by_const_1.case_0
  step as ⟨e_v40, he_v40⟩
  store_step with CtorSpec.eo__40bvsize.construct s6 e_v40 (by rw [he_v40]; exact empty_args) hinv6 h64 as ⟨v40, s7, hinv7, h_v40⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v32 h_v38 h_v39 dropping h_v34 h_v35 h_v36 he_v40 hinv6 e_v40 s6 v34 v35 v36
  pat_same v38 v40 with h_v38 h_v40 using hinv7 else hinv7 hG in EoCases.__eo_prog_bv_lshr_by_const_1.case_0
  pat_same v39 a0 with h_v39 h_a0 using hinv7 else hinv7 hG in EoCases.__eo_prog_bv_lshr_by_const_1.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s7 1#u32 (1) (by scalar_tac) hinv7 h64 as ⟨v41, s8, hinv8, h_v41⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v32 dropping h_v38 h_v39 h_v40 hinv7 s7 v38 v39 v40
  pat_same v32 v41 with h_v32 h_v41 using hinv8 else hinv8 hG in EoCases.__eo_prog_bv_lshr_by_const_1.case_0
  step as ⟨e_v42, he_v42⟩
  store_step with CtorSpec.eo__3d.construct s8 e_v42 (by rw [he_v42]; exact empty_args) hinv8 h64 as ⟨v42, s9, hinv9, h_v42⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 dropping h_v32 h_v41 he_v42 hinv8 e_v42 s8 v32 v41
  step as ⟨e_v43, he_v43⟩
  store_step with CtorSpec.eo_bvlshr.construct s9 e_v43 (by rw [he_v43]; exact empty_args) hinv9 h64 as ⟨v43, s10, hinv10, h_v43⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v42 dropping he_v43 hinv9 e_v43 s9
  store_step with Store.apply_rep s10 v43 a0 _ _ hinv10 h64 h_v43 h_a0 (by ns_tac) (by ns_tac) as ⟨v44, s11, hinv11, h_v44⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v42 dropping h_v43 hinv10 s10 v43
  step as ⟨e_v45, he_v45⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s11 e_v45 (by rw [he_v45]; rfl) h_a2 hinv11 h64 as ⟨v45, s12, hinv12, h_v45⟩ growing hG carrying h_a0 h_a1 h_a3 h_v42 h_v44 dropping h_a2 he_v45 hinv11 e_v45 s11
  store_step with Store.apply_rep s12 v45 a1 _ _ hinv12 h64 h_v45 h_a1 (by ns_tac) (by ns_tac) as ⟨v46, s13, hinv13, h_v46⟩ growing hG carrying h_a0 h_a1 h_a3 h_v42 h_v44 dropping h_v45 hinv12 s12 v45
  store_step with Store.apply_rep s13 v44 v46 _ _ hinv13 h64 h_v44 h_v46 (by ns_tac) (by ns_tac) as ⟨v47, s14, hinv14, h_v47⟩ growing hG carrying h_a0 h_a1 h_a3 h_v42 dropping h_v44 h_v46 hinv13 s13 v44 v46
  store_step with Store.apply_rep s14 v42 v47 _ _ hinv14 h64 h_v42 h_v47 (by ns_tac) (by ns_tac) as ⟨v48, s15, hinv15, h_v48⟩ growing hG carrying h_a0 h_a1 h_a3 dropping h_v42 h_v47 hinv14 s14 v42 v47
  step as ⟨e_v49, he_v49⟩
  store_step with CtorSpec.eo_concat.construct s15 e_v49 (by rw [he_v49]; exact empty_args) hinv15 h64 as ⟨v49, s16, hinv16, h_v49⟩ growing hG carrying h_a0 h_a1 h_a3 h_v48 dropping he_v49 hinv15 e_v49 s15
  step as ⟨e_v50, he_v50⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s16 e_v50 (by rw [he_v50]; rfl) h_a1 hinv16 h64 as ⟨v50, s17, hinv17, h_v50⟩ growing hG carrying h_a0 h_a1 h_a3 h_v48 h_v49 dropping he_v50 hinv16 e_v50 s16
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s17 0#u32 (0) (by scalar_tac) hinv17 h64 as ⟨v51, s18, hinv18, h_v51⟩ growing hG carrying h_a0 h_a1 h_a3 h_v48 h_v49 h_v50 dropping hinv17 s17
  store_step with Store.apply_rep s18 v50 v51 _ _ hinv18 h64 h_v50 h_v51 (by ns_tac) (by ns_tac) as ⟨v52, s19, hinv19, h_v52⟩ growing hG carrying h_a0 h_a1 h_a3 h_v48 h_v49 dropping h_v50 h_v51 hinv18 s18 v50 v51
  store_step with Store.apply_rep s19 v49 v52 _ _ hinv19 h64 h_v49 h_v52 (by ns_tac) (by ns_tac) as ⟨v53, s20, hinv20, h_v53⟩ growing hG carrying h_a0 h_a1 h_a3 h_v48 dropping h_v49 h_v52 hinv19 s19 v49 v52
  step as ⟨e_v54, he_v54⟩
  store_step with CtorSpec.eo_concat.construct s20 e_v54 (by rw [he_v54]; exact empty_args) hinv20 h64 as ⟨v54, s21, hinv21, h_v54⟩ growing hG carrying h_a0 h_a1 h_a3 h_v48 h_v53 dropping he_v54 hinv20 e_v54 s20
  step as ⟨e_v55, he_v55⟩
  store_step with CtorSpec.eo_extract.construct s21 e_v55 (by rw [he_v55]; rfl) h_a3 h_a1 hinv21 h64 as ⟨v55, s22, hinv22, h_v55⟩ growing hG carrying h_a0 h_v48 h_v53 h_v54 dropping h_a1 h_a3 he_v55 hinv21 e_v55 s21
  store_step with Store.apply_rep s22 v55 a0 _ _ hinv22 h64 h_v55 h_a0 (by ns_tac) (by ns_tac) as ⟨v56, s23, hinv23, h_v56⟩ growing hG carrying h_v48 h_v53 h_v54 dropping h_a0 h_v55 hinv22 s22 v55
  store_step with Store.apply_rep s23 v54 v56 _ _ hinv23 h64 h_v54 h_v56 (by ns_tac) (by ns_tac) as ⟨v57, s24, hinv24, h_v57⟩ growing hG carrying h_v48 h_v53 dropping h_v54 h_v56 hinv23 s23 v54 v56
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s24 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv24 h64 as ⟨v58, s25, hinv25, h_v58⟩ growing hG carrying h_v48 h_v53 h_v57 dropping hinv24 s24
  store_step with Store.apply_rep s25 v57 v58 _ _ hinv25 h64 h_v57 h_v58 (by ns_tac) (by ns_tac) as ⟨v59, s26, hinv26, h_v59⟩ growing hG carrying h_v48 h_v53 dropping h_v57 h_v58 hinv25 s25 v57 v58
  store_step with Store.apply_rep s26 v53 v59 _ _ hinv26 h64 h_v53 h_v59 (by ns_tac) (by ns_tac) as ⟨v60, s27, hinv27, h_v60⟩ growing hG carrying h_v48 dropping h_v53 h_v59 hinv26 s26 v53 v59
  store_step with Store.apply_rep s27 v48 v60 _ _ hinv27 h64 h_v48 h_v60 (by ns_tac) (by ns_tac) as ⟨v61, s28, hinv28, h_v61⟩ growing hG carrying dropping h_v48 h_v60 hinv27 s27 v48 v60
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
  unfold case_0_eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d2
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a3 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_bv_lshr_by_const_2.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_lshr_by_const_2.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_lshr_by_const_2.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a4 h_v4 h_v6 h_v7 dropping h_a3 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_lshr_by_const_2.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_lshr_by_const_2.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_lshr_by_const_2.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__3e_3d.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_a4 h_v4 h_v11 h_v13 h_v14 dropping h_v10 h_v6 h_v7 h_v8 he_v15 hinv1 e_v15 s1 v10 v6 v7 v8
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_lshr_by_const_2.case_0
  pat_same v14 a1 with h_v14 h_a1 using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_lshr_by_const_2.case_0
  pat_unapply h_v11 as ⟨v17, v18, x_v17, x_v18, h_v17, h_v18, hn_v17, hn_v18⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_lshr_by_const_2.case_0
  step as ⟨e_v19, he_v19⟩
  store_step with CtorSpec.eo__40bvsize.construct s2 e_v19 (by rw [he_v19]; exact empty_args) hinv2 h64 as ⟨v19, s3, hinv3, h_v19⟩ growing hG carrying h_a0 h_a1 h_a2 h_a4 h_v4 h_v17 h_v18 dropping h_v11 h_v13 h_v14 h_v15 he_v19 hinv2 e_v19 s2 v11 v13 v14 v15
  pat_same v17 v19 with h_v17 h_v19 using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_lshr_by_const_2.case_0
  pat_same v18 a0 with h_v18 h_a0 using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_lshr_by_const_2.case_0
  store_step with Store.literal_boolean_spec s3 true hinv3 h64 as ⟨v20, s4, hinv4, h_v20⟩ growing hG carrying h_a0 h_a1 h_a2 h_a4 h_v4 dropping h_v17 h_v18 h_v19 hinv3 s3 v17 v18 v19
  pat_same v4 v20 with h_v4 h_v20 using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_lshr_by_const_2.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a4 as ⟨v22, x_v22, h_v22⟩ else hinv4 hG in EoCases.__eo_prog_bv_lshr_by_const_2.case_0
  pat_unapply h_v22 as ⟨v24, v25, x_v24, x_v25, h_v24, h_v25, hn_v24, hn_v25⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_lshr_by_const_2.case_0
  pat_unapply h_v24 as ⟨v27, v28, x_v27, x_v28, h_v27, h_v28, hn_v27, hn_v28⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_lshr_by_const_2.case_0
  step as ⟨e_v29, he_v29⟩
  store_step with CtorSpec.eo__3d.construct s4 e_v29 (by rw [he_v29]; exact empty_args) hinv4 h64 as ⟨v29, s5, hinv5, h_v29⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v27 h_v28 dropping h_a4 h_v20 h_v22 h_v24 h_v4 he_v29 hinv4 e_v29 s4 v20 v22 v24 v4
  pat_same v27 v29 with h_v27 h_v29 using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_lshr_by_const_2.case_0
  pat_unapply h_v28 as ⟨v31, v32, x_v31, x_v32, h_v31, h_v32, hn_v31, hn_v32⟩ using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_lshr_by_const_2.case_0
  pat_unapply h_v31 as ⟨v34, v35, x_v34, x_v35, h_v34, h_v35, hn_v34, hn_v35⟩ using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_lshr_by_const_2.case_0
  step as ⟨e_v36, he_v36⟩
  store_step with CtorSpec.eo__3c.construct s5 e_v36 (by rw [he_v36]; exact empty_args) hinv5 h64 as ⟨v36, s6, hinv6, h_v36⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v32 h_v34 h_v35 dropping h_v27 h_v28 h_v29 h_v31 he_v36 hinv5 e_v36 s5 v27 v28 v29 v31
  pat_same v34 v36 with h_v34 h_v36 using hinv6 else hinv6 hG in EoCases.__eo_prog_bv_lshr_by_const_2.case_0
  pat_same v35 a1 with h_v35 h_a1 using hinv6 else hinv6 hG in EoCases.__eo_prog_bv_lshr_by_const_2.case_0
  pat_unapply h_v32 as ⟨v38, v39, x_v38, x_v39, h_v38, h_v39, hn_v38, hn_v39⟩ using hinv6 else hinv6 hG in EoCases.__eo_prog_bv_lshr_by_const_2.case_0
  step as ⟨e_v40, he_v40⟩
  store_step with CtorSpec.eo_int_2epow2.construct s6 e_v40 (by rw [he_v40]; exact empty_args) hinv6 h64 as ⟨v40, s7, hinv7, h_v40⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v38 h_v39 dropping h_v32 h_v34 h_v35 h_v36 he_v40 hinv6 e_v40 s6 v32 v34 v35 v36
  pat_same v38 v40 with h_v38 h_v40 using hinv7 else hinv7 hG in EoCases.__eo_prog_bv_lshr_by_const_2.case_0
  pat_unapply h_v39 as ⟨v42, v43, x_v42, x_v43, h_v42, h_v43, hn_v42, hn_v43⟩ using hinv7 else hinv7 hG in EoCases.__eo_prog_bv_lshr_by_const_2.case_0
  step as ⟨e_v44, he_v44⟩
  store_step with CtorSpec.eo__40bvsize.construct s7 e_v44 (by rw [he_v44]; exact empty_args) hinv7 h64 as ⟨v44, s8, hinv8, h_v44⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v42 h_v43 dropping h_v38 h_v39 h_v40 he_v44 hinv7 e_v44 s7 v38 v39 v40
  pat_same v42 v44 with h_v42 h_v44 using hinv8 else hinv8 hG in EoCases.__eo_prog_bv_lshr_by_const_2.case_0
  pat_same v43 a0 with h_v43 h_a0 using hinv8 else hinv8 hG in EoCases.__eo_prog_bv_lshr_by_const_2.case_0
  store_step with Store.literal_boolean_spec s8 true hinv8 h64 as ⟨v45, s9, hinv9, h_v45⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 dropping h_v42 h_v43 h_v44 hinv8 s8 v42 v43 v44
  pat_same v25 v45 with h_v25 h_v45 using hinv9 else hinv9 hG in EoCases.__eo_prog_bv_lshr_by_const_2.case_0
  step as ⟨e_v46, he_v46⟩
  store_step with CtorSpec.eo__3d.construct s9 e_v46 (by rw [he_v46]; exact empty_args) hinv9 h64 as ⟨v46, s10, hinv10, h_v46⟩ growing hG carrying h_a0 h_a1 h_a2 dropping h_v25 h_v45 he_v46 hinv9 e_v46 s9 v25 v45
  step as ⟨e_v47, he_v47⟩
  store_step with CtorSpec.eo_bvlshr.construct s10 e_v47 (by rw [he_v47]; exact empty_args) hinv10 h64 as ⟨v47, s11, hinv11, h_v47⟩ growing hG carrying h_a0 h_a1 h_a2 h_v46 dropping he_v47 hinv10 e_v47 s10
  store_step with Store.apply_rep s11 v47 a0 _ _ hinv11 h64 h_v47 h_a0 (by ns_tac) (by ns_tac) as ⟨v48, s12, hinv12, h_v48⟩ growing hG carrying h_a1 h_a2 h_v46 dropping h_a0 h_v47 hinv11 s11 v47
  step as ⟨e_v49, he_v49⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s12 e_v49 (by rw [he_v49]; rfl) h_a2 hinv12 h64 as ⟨v49, s13, hinv13, h_v49⟩ growing hG carrying h_a1 h_a2 h_v46 h_v48 dropping he_v49 hinv12 e_v49 s12
  store_step with Store.apply_rep s13 v49 a1 _ _ hinv13 h64 h_v49 h_a1 (by ns_tac) (by ns_tac) as ⟨v50, s14, hinv14, h_v50⟩ growing hG carrying h_a2 h_v46 h_v48 dropping h_a1 h_v49 hinv13 s13 v49
  store_step with Store.apply_rep s14 v48 v50 _ _ hinv14 h64 h_v48 h_v50 (by ns_tac) (by ns_tac) as ⟨v51, s15, hinv15, h_v51⟩ growing hG carrying h_a2 h_v46 dropping h_v48 h_v50 hinv14 s14 v48 v50
  store_step with Store.apply_rep s15 v46 v51 _ _ hinv15 h64 h_v46 h_v51 (by ns_tac) (by ns_tac) as ⟨v52, s16, hinv16, h_v52⟩ growing hG carrying h_a2 dropping h_v46 h_v51 hinv15 s15 v46 v51
  step as ⟨e_v53, he_v53⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s16 e_v53 (by rw [he_v53]; rfl) h_a2 hinv16 h64 as ⟨v53, s17, hinv17, h_v53⟩ growing hG carrying h_v52 dropping h_a2 he_v53 hinv16 e_v53 s16
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s17 0#u32 (0) (by scalar_tac) hinv17 h64 as ⟨v54, s18, hinv18, h_v54⟩ growing hG carrying h_v52 h_v53 dropping hinv17 s17
  store_step with Store.apply_rep s18 v53 v54 _ _ hinv18 h64 h_v53 h_v54 (by ns_tac) (by ns_tac) as ⟨v55, s19, hinv19, h_v55⟩ growing hG carrying h_v52 dropping h_v53 h_v54 hinv18 s18 v53 v54
  store_step with Store.apply_rep s19 v52 v55 _ _ hinv19 h64 h_v52 h_v55 (by ns_tac) (by ns_tac) as ⟨v56, s20, hinv20, h_v56⟩ growing hG carrying dropping h_v52 h_v55 hinv19 s19 v52 v55
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
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 dropping he_v0 e_v0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_bvlshr.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0 dropping he_v1 hinv1 e_v1 s1
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
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 dropping he_v0 e_v0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_bvslt.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0 dropping he_v1 hinv1 e_v1 s1
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_v0 dropping h_v1 hinv2 s2 v1
  store_step with Store.apply_rep s3 v2 a0 _ _ hinv3 h64 h_v2 h_a0 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_v0 dropping h_a0 h_v2 hinv3 s3 v2
  store_step with Store.apply_rep s4 v0 v3 _ _ hinv4 h64 h_v0 h_v3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying dropping h_v0 h_v3 hinv4 s4 v0 v3
  store_step with Store.literal_boolean_spec s5 false hinv5 h64 as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_v4 dropping hinv5 s5
  store_step with Store.apply_rep s6 v4 v5 _ _ hinv6 h64 h_v4 h_v5 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying dropping h_v4 h_v5 hinv6 s6 v4 v5
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
  unfold case_0_eo__24eo_5fprog_5fbv_2dmerge_2dsign_2dextend_2d1
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a4 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_bv_merge_sign_extend_1.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_merge_sign_extend_1.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_merge_sign_extend_1.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v4 h_v6 h_v7 dropping h_a4 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_merge_sign_extend_1.case_0
  pat_same v7 a3 with h_v7 h_a3 using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_merge_sign_extend_1.case_0
  pat_unapply h_v4 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_merge_sign_extend_1.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_merge_sign_extend_1.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__2b.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v11 h_v13 h_v14 dropping h_v10 h_v4 h_v6 h_v7 h_v8 he_v15 hinv1 e_v15 s1 v10 v4 v6 v7 v8
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_merge_sign_extend_1.case_0
  pat_same v14 a1 with h_v14 h_a1 using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_merge_sign_extend_1.case_0
  pat_unapply h_v11 as ⟨v17, v18, x_v17, x_v18, h_v17, h_v18, hn_v17, hn_v18⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_merge_sign_extend_1.case_0
  pat_unapply h_v17 as ⟨v20, v21, x_v20, x_v21, h_v20, h_v21, hn_v20, hn_v21⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_merge_sign_extend_1.case_0
  step as ⟨e_v22, he_v22⟩
  store_step with CtorSpec.eo__2b.construct s2 e_v22 (by rw [he_v22]; exact empty_args) hinv2 h64 as ⟨v22, s3, hinv3, h_v22⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v18 h_v20 h_v21 dropping h_v11 h_v13 h_v14 h_v15 h_v17 he_v22 hinv2 e_v22 s2 v11 v13 v14 v15 v17
  pat_same v20 v22 with h_v20 h_v22 using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_merge_sign_extend_1.case_0
  pat_same v21 a2 with h_v21 h_a2 using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_merge_sign_extend_1.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s3 0#u32 (0) (by scalar_tac) hinv3 h64 as ⟨v23, s4, hinv4, h_v23⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v18 dropping h_v20 h_v21 h_v22 hinv3 s3 v20 v21 v22
  pat_same v18 v23 with h_v18 h_v23 using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_merge_sign_extend_1.case_0
  step as ⟨e_v24, he_v24⟩
  store_step with CtorSpec.eo__3d.construct s4 e_v24 (by rw [he_v24]; exact empty_args) hinv4 h64 as ⟨v24, s5, hinv5, h_v24⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 dropping h_v18 h_v23 he_v24 hinv4 e_v24 s4 v18 v23
  step as ⟨e_v25, he_v25⟩
  store_step with CtorSpec.eo_sign_5fextend.construct s5 e_v25 (by rw [he_v25]; rfl) h_a1 hinv5 h64 as ⟨v25, s6, hinv6, h_v25⟩ growing hG carrying h_a0 h_a2 h_a3 h_v24 dropping h_a1 he_v25 hinv5 e_v25 s5
  step as ⟨e_v26, he_v26⟩
  store_step with CtorSpec.eo_sign_5fextend.construct s6 e_v26 (by rw [he_v26]; rfl) h_a2 hinv6 h64 as ⟨v26, s7, hinv7, h_v26⟩ growing hG carrying h_a0 h_a3 h_v24 h_v25 dropping h_a2 he_v26 hinv6 e_v26 s6
  store_step with Store.apply_rep s7 v26 a0 _ _ hinv7 h64 h_v26 h_a0 (by ns_tac) (by ns_tac) as ⟨v27, s8, hinv8, h_v27⟩ growing hG carrying h_a0 h_a3 h_v24 h_v25 dropping h_v26 hinv7 s7 v26
  store_step with Store.apply_rep s8 v25 v27 _ _ hinv8 h64 h_v25 h_v27 (by ns_tac) (by ns_tac) as ⟨v28, s9, hinv9, h_v28⟩ growing hG carrying h_a0 h_a3 h_v24 dropping h_v25 h_v27 hinv8 s8 v25 v27
  store_step with Store.apply_rep s9 v24 v28 _ _ hinv9 h64 h_v24 h_v28 (by ns_tac) (by ns_tac) as ⟨v29, s10, hinv10, h_v29⟩ growing hG carrying h_a0 h_a3 dropping h_v24 h_v28 hinv9 s9 v24 v28
  step as ⟨e_v30, he_v30⟩
  store_step with CtorSpec.eo_sign_5fextend.construct s10 e_v30 (by rw [he_v30]; rfl) h_a3 hinv10 h64 as ⟨v30, s11, hinv11, h_v30⟩ growing hG carrying h_a0 h_v29 dropping h_a3 he_v30 hinv10 e_v30 s10
  store_step with Store.apply_rep s11 v30 a0 _ _ hinv11 h64 h_v30 h_a0 (by ns_tac) (by ns_tac) as ⟨v31, s12, hinv12, h_v31⟩ growing hG carrying h_v29 dropping h_a0 h_v30 hinv11 s11 v30
  store_step with Store.apply_rep s12 v29 v31 _ _ hinv12 h64 h_v29 h_v31 (by ns_tac) (by ns_tac) as ⟨v32, s13, hinv13, h_v32⟩ growing hG carrying dropping h_v29 h_v31 hinv12 s12 v29 v31
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
  unfold case_0_eo__24eo_5fprog_5fbv_2dmerge_2dsign_2dextend_2d2
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a4 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_bv_merge_sign_extend_2.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_merge_sign_extend_2.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_merge_sign_extend_2.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a5 h_v4 h_v6 h_v7 dropping h_a4 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_merge_sign_extend_2.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_merge_sign_extend_2.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_merge_sign_extend_2.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__3e.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a5 h_v4 h_v11 h_v13 h_v14 dropping h_v10 h_v6 h_v7 h_v8 he_v15 hinv1 e_v15 s1 v10 v6 v7 v8
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_merge_sign_extend_2.case_0
  pat_same v14 a2 with h_v14 h_a2 using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_merge_sign_extend_2.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s2 0#u32 (0) (by scalar_tac) hinv2 h64 as ⟨v16, s3, hinv3, h_v16⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a5 h_v4 h_v11 dropping h_v13 h_v14 h_v15 hinv2 s2 v13 v14 v15
  pat_same v11 v16 with h_v11 h_v16 using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_merge_sign_extend_2.case_0
  store_step with Store.literal_boolean_spec s3 true hinv3 h64 as ⟨v17, s4, hinv4, h_v17⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a5 h_v4 dropping h_v11 h_v16 hinv3 s3 v11 v16
  pat_same v4 v17 with h_v4 h_v17 using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_merge_sign_extend_2.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a5 as ⟨v19, x_v19, h_v19⟩ else hinv4 hG in EoCases.__eo_prog_bv_merge_sign_extend_2.case_0
  pat_unapply h_v19 as ⟨v21, v22, x_v21, x_v22, h_v21, h_v22, hn_v21, hn_v22⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_merge_sign_extend_2.case_0
  pat_unapply h_v21 as ⟨v24, v25, x_v24, x_v25, h_v24, h_v25, hn_v24, hn_v25⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_merge_sign_extend_2.case_0
  step as ⟨e_v26, he_v26⟩
  store_step with CtorSpec.eo__3d.construct s4 e_v26 (by rw [he_v26]; exact empty_args) hinv4 h64 as ⟨v26, s5, hinv5, h_v26⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v22 h_v24 h_v25 dropping h_a5 h_v17 h_v19 h_v21 h_v4 he_v26 hinv4 e_v26 s4 v17 v19 v21 v4
  pat_same v24 v26 with h_v24 h_v26 using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_merge_sign_extend_2.case_0
  pat_same v25 a3 with h_v25 h_a3 using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_merge_sign_extend_2.case_0
  pat_unapply h_v22 as ⟨v28, v29, x_v28, x_v29, h_v28, h_v29, hn_v28, hn_v29⟩ using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_merge_sign_extend_2.case_0
  pat_unapply h_v28 as ⟨v31, v32, x_v31, x_v32, h_v31, h_v32, hn_v31, hn_v32⟩ using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_merge_sign_extend_2.case_0
  step as ⟨e_v33, he_v33⟩
  store_step with CtorSpec.eo__2b.construct s5 e_v33 (by rw [he_v33]; exact empty_args) hinv5 h64 as ⟨v33, s6, hinv6, h_v33⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v29 h_v31 h_v32 dropping h_v22 h_v24 h_v25 h_v26 h_v28 he_v33 hinv5 e_v33 s5 v22 v24 v25 v26 v28
  pat_same v31 v33 with h_v31 h_v33 using hinv6 else hinv6 hG in EoCases.__eo_prog_bv_merge_sign_extend_2.case_0
  pat_same v32 a1 with h_v32 h_a1 using hinv6 else hinv6 hG in EoCases.__eo_prog_bv_merge_sign_extend_2.case_0
  pat_unapply h_v29 as ⟨v35, v36, x_v35, x_v36, h_v35, h_v36, hn_v35, hn_v36⟩ using hinv6 else hinv6 hG in EoCases.__eo_prog_bv_merge_sign_extend_2.case_0
  pat_unapply h_v35 as ⟨v38, v39, x_v38, x_v39, h_v38, h_v39, hn_v38, hn_v39⟩ using hinv6 else hinv6 hG in EoCases.__eo_prog_bv_merge_sign_extend_2.case_0
  step as ⟨e_v40, he_v40⟩
  store_step with CtorSpec.eo__2b.construct s6 e_v40 (by rw [he_v40]; exact empty_args) hinv6 h64 as ⟨v40, s7, hinv7, h_v40⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v36 h_v38 h_v39 dropping h_v29 h_v31 h_v32 h_v33 h_v35 he_v40 hinv6 e_v40 s6 v29 v31 v32 v33 v35
  pat_same v38 v40 with h_v38 h_v40 using hinv7 else hinv7 hG in EoCases.__eo_prog_bv_merge_sign_extend_2.case_0
  pat_same v39 a2 with h_v39 h_a2 using hinv7 else hinv7 hG in EoCases.__eo_prog_bv_merge_sign_extend_2.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s7 0#u32 (0) (by scalar_tac) hinv7 h64 as ⟨v41, s8, hinv8, h_v41⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v36 dropping h_v38 h_v39 h_v40 hinv7 s7 v38 v39 v40
  pat_same v36 v41 with h_v36 h_v41 using hinv8 else hinv8 hG in EoCases.__eo_prog_bv_merge_sign_extend_2.case_0
  step as ⟨e_v42, he_v42⟩
  store_step with CtorSpec.eo__3d.construct s8 e_v42 (by rw [he_v42]; exact empty_args) hinv8 h64 as ⟨v42, s9, hinv9, h_v42⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 dropping h_v36 h_v41 he_v42 hinv8 e_v42 s8 v36 v41
  step as ⟨e_v43, he_v43⟩
  store_step with CtorSpec.eo_sign_5fextend.construct s9 e_v43 (by rw [he_v43]; rfl) h_a1 hinv9 h64 as ⟨v43, s10, hinv10, h_v43⟩ growing hG carrying h_a0 h_a2 h_a3 h_v42 dropping h_a1 he_v43 hinv9 e_v43 s9
  step as ⟨e_v44, he_v44⟩
  store_step with CtorSpec.eo_zero_5fextend.construct s10 e_v44 (by rw [he_v44]; rfl) h_a2 hinv10 h64 as ⟨v44, s11, hinv11, h_v44⟩ growing hG carrying h_a0 h_a3 h_v42 h_v43 dropping h_a2 he_v44 hinv10 e_v44 s10
  store_step with Store.apply_rep s11 v44 a0 _ _ hinv11 h64 h_v44 h_a0 (by ns_tac) (by ns_tac) as ⟨v45, s12, hinv12, h_v45⟩ growing hG carrying h_a0 h_a3 h_v42 h_v43 dropping h_v44 hinv11 s11 v44
  store_step with Store.apply_rep s12 v43 v45 _ _ hinv12 h64 h_v43 h_v45 (by ns_tac) (by ns_tac) as ⟨v46, s13, hinv13, h_v46⟩ growing hG carrying h_a0 h_a3 h_v42 dropping h_v43 h_v45 hinv12 s12 v43 v45
  store_step with Store.apply_rep s13 v42 v46 _ _ hinv13 h64 h_v42 h_v46 (by ns_tac) (by ns_tac) as ⟨v47, s14, hinv14, h_v47⟩ growing hG carrying h_a0 h_a3 dropping h_v42 h_v46 hinv13 s13 v42 v46
  step as ⟨e_v48, he_v48⟩
  store_step with CtorSpec.eo_zero_5fextend.construct s14 e_v48 (by rw [he_v48]; rfl) h_a3 hinv14 h64 as ⟨v48, s15, hinv15, h_v48⟩ growing hG carrying h_a0 h_v47 dropping h_a3 he_v48 hinv14 e_v48 s14
  store_step with Store.apply_rep s15 v48 a0 _ _ hinv15 h64 h_v48 h_a0 (by ns_tac) (by ns_tac) as ⟨v49, s16, hinv16, h_v49⟩ growing hG carrying h_v47 dropping h_a0 h_v48 hinv15 s15 v48
  store_step with Store.apply_rep s16 v47 v49 _ _ hinv16 h64 h_v47 h_v49 (by ns_tac) (by ns_tac) as ⟨v50, s17, hinv17, h_v50⟩ growing hG carrying dropping h_v47 h_v49 hinv16 s16 v47 v49
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

theorem case_0_eo__24eo_5fprog_5fbv_2dnand_2deliminate_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fbv_2dnand_2deliminate s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_bv_nand_eliminate.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_bv_nand_eliminate.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fbv_2dnand_2deliminate
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 dropping he_v0 e_v0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_bvnand.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0 dropping he_v1 hinv1 e_v1 s1
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 dropping h_v1 hinv2 s2 v1
  store_step with Store.apply_rep s3 v2 a1 _ _ hinv3 h64 h_v2 h_a1 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_v0 dropping h_v2 hinv3 s3 v2
  store_step with Store.apply_rep s4 v0 v3 _ _ hinv4 h64 h_v0 h_v3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 dropping h_v0 h_v3 hinv4 s4 v0 v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo_bvnot.construct s5 e_v5 (by rw [he_v5]; exact empty_args) hinv5 h64 as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_v4 dropping he_v5 hinv5 e_v5 s5
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_bvand.construct s6 e_v6 (by rw [he_v6]; exact empty_args) hinv6 h64 as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_v4 h_v5 dropping he_v6 hinv6 e_v6 s6
  store_step with Store.apply_rep s7 v6 a0 _ _ hinv7 h64 h_v6 h_a0 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_v4 h_v5 dropping h_v6 hinv7 s7 v6
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo_bvand.construct s8 e_v8 (by rw [he_v8]; exact empty_args) hinv8 h64 as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_a1 h_v4 h_v5 h_v7 dropping he_v8 hinv8 e_v8 s8
  store_step with Store.apply_rep s9 v8 a1 _ _ hinv9 h64 h_v8 h_a1 (by ns_tac) (by ns_tac) as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a0 h_v4 h_v5 h_v7 dropping h_a1 h_v8 hinv9 s9 v8
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo_bvand.construct s10 e_v10 (by rw [he_v10]; exact empty_args) hinv10 h64 as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_a0 h_v4 h_v5 h_v7 h_v9 dropping he_v10 hinv10 e_v10 s10
  store_step with ih.eo__24eo_5ftypeof s11 a0 _ hinv11 h64 (hG.rem hrem) h_a0 as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_v4 h_v5 h_v7 h_v9 h_v10 dropping h_a0 hinv11 s11
  store_step with ih.eo__24eo_5fnil s12 v10 v11 _ _ hinv12 h64 (hG.rem hrem) h_v10 h_v11 as ⟨v12, s13, hinv13, h_v12⟩ growing hG carrying h_v4 h_v5 h_v7 h_v9 dropping h_v10 h_v11 hinv12 s12 v10 v11
  store_step with Store.apply_mk_rep s13 v9 v12 _ _ hinv13 h64 h_v9 h_v12 as ⟨v13, s14, hinv14, h_v13⟩ growing hG carrying h_v4 h_v5 h_v7 dropping h_v12 h_v9 hinv13 s13 v12 v9
  store_step with Store.apply_mk_rep s14 v7 v13 _ _ hinv14 h64 h_v7 h_v13 as ⟨v14, s15, hinv15, h_v14⟩ growing hG carrying h_v4 h_v5 dropping h_v13 h_v7 hinv14 s14 v13 v7
  store_step with Store.apply_mk_rep s15 v5 v14 _ _ hinv15 h64 h_v5 h_v14 as ⟨v15, s16, hinv16, h_v15⟩ growing hG carrying h_v4 dropping h_v14 h_v5 hinv15 s15 v14 v5
  store_step with Store.apply_mk_rep s16 v4 v15 _ _ hinv16 h64 h_v4 h_v15 as ⟨v16, s17, hinv17, h_v16⟩ growing hG carrying dropping h_v15 h_v4 hinv16 s16 v15 v4
  case_done hinv17 hG with h_v16 in EoCases.__eo_prog_bv_nand_eliminate.case_0 using hn_a0 hn_a1

/-- logos's `__eo_prog_bv_nand_eliminate` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fbv_2dnand_2deliminate.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_bv_nand_eliminate x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_bv_nand_eliminate.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_bv_nand_eliminate
  unfold EoCases.__eo_prog_bv_nand_eliminate.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fbv_2dnand_2deliminate_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5fbv_2dnand_2deliminate s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_nand_eliminate x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fbv_2dnand_2deliminate.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5fbv_2dnand_2deliminate
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fbv_2dnand_2deliminate_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_bv_nand_eliminate.case_0

theorem eo__24eo_5fprog_5fbv_2dnand_2deliminate_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fbv_2dnand_2deliminate.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5fbv_2dnand_2deliminate
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fbv_2dnand_2deliminate s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_bv_nand_eliminate x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fbv_2dnand_2deliminate_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
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
  unfold case_0_eo__24eo_5fprog_5fbv_2dnego_2deliminate
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a2 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_bv_nego_eliminate.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_nego_eliminate.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_nego_eliminate.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_v4 h_v6 h_v7 dropping h_a2 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_nego_eliminate.case_0
  pat_same v7 a1 with h_v7 h_a1 using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_nego_eliminate.case_0
  pat_unapply h_v4 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_nego_eliminate.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_nego_eliminate.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__2d.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_a1 h_v11 h_v13 h_v14 dropping h_v10 h_v4 h_v6 h_v7 h_v8 he_v15 hinv1 e_v15 s1 v10 v4 v6 v7 v8
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_nego_eliminate.case_0
  pat_unapply h_v14 as ⟨v17, v18, x_v17, x_v18, h_v17, h_v18, hn_v17, hn_v18⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_nego_eliminate.case_0
  step as ⟨e_v19, he_v19⟩
  store_step with CtorSpec.eo__40bvsize.construct s2 e_v19 (by rw [he_v19]; exact empty_args) hinv2 h64 as ⟨v19, s3, hinv3, h_v19⟩ growing hG carrying h_a0 h_a1 h_v11 h_v17 h_v18 dropping h_v13 h_v14 h_v15 he_v19 hinv2 e_v19 s2 v13 v14 v15
  pat_same v17 v19 with h_v17 h_v19 using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_nego_eliminate.case_0
  pat_same v18 a0 with h_v18 h_a0 using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_nego_eliminate.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s3 1#u32 (1) (by scalar_tac) hinv3 h64 as ⟨v20, s4, hinv4, h_v20⟩ growing hG carrying h_a0 h_a1 h_v11 dropping h_v17 h_v18 h_v19 hinv3 s3 v17 v18 v19
  pat_same v11 v20 with h_v11 h_v20 using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_nego_eliminate.case_0
  step as ⟨e_v21, he_v21⟩
  store_step with CtorSpec.eo__3d.construct s4 e_v21 (by rw [he_v21]; exact empty_args) hinv4 h64 as ⟨v21, s5, hinv5, h_v21⟩ growing hG carrying h_a0 h_a1 dropping h_v11 h_v20 he_v21 hinv4 e_v21 s4 v11 v20
  step as ⟨e_v22, he_v22⟩
  store_step with CtorSpec.eo_bvnego.construct s5 e_v22 (by rw [he_v22]; exact empty_args) hinv5 h64 as ⟨v22, s6, hinv6, h_v22⟩ growing hG carrying h_a0 h_a1 h_v21 dropping he_v22 hinv5 e_v22 s5
  store_step with Store.apply_rep s6 v22 a0 _ _ hinv6 h64 h_v22 h_a0 (by ns_tac) (by ns_tac) as ⟨v23, s7, hinv7, h_v23⟩ growing hG carrying h_a0 h_a1 h_v21 dropping h_v22 hinv6 s6 v22
  store_step with Store.apply_rep s7 v21 v23 _ _ hinv7 h64 h_v21 h_v23 (by ns_tac) (by ns_tac) as ⟨v24, s8, hinv8, h_v24⟩ growing hG carrying h_a0 h_a1 dropping h_v21 h_v23 hinv7 s7 v21 v23
  step as ⟨e_v25, he_v25⟩
  store_step with CtorSpec.eo__3d.construct s8 e_v25 (by rw [he_v25]; exact empty_args) hinv8 h64 as ⟨v25, s9, hinv9, h_v25⟩ growing hG carrying h_a0 h_a1 h_v24 dropping he_v25 hinv8 e_v25 s8
  store_step with Store.apply_rep s9 v25 a0 _ _ hinv9 h64 h_v25 h_a0 (by ns_tac) (by ns_tac) as ⟨v26, s10, hinv10, h_v26⟩ growing hG carrying h_a1 h_v24 dropping h_a0 h_v25 hinv9 s9 v25
  step as ⟨e_v27, he_v27⟩
  store_step with CtorSpec.eo_concat.construct s10 e_v27 (by rw [he_v27]; exact empty_args) hinv10 h64 as ⟨v27, s11, hinv11, h_v27⟩ growing hG carrying h_a1 h_v24 h_v26 dropping he_v27 hinv10 e_v27 s10
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s11 1#u32 (1) (by scalar_tac) hinv11 h64 as ⟨v28, s12, hinv12, h_v28⟩ growing hG carrying h_a1 h_v24 h_v26 h_v27 dropping hinv11 s11
  step as ⟨e_v29, he_v29⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s12 e_v29 (by rw [he_v29]; rfl) h_v28 hinv12 h64 as ⟨v29, s13, hinv13, h_v29⟩ growing hG carrying h_a1 h_v24 h_v26 h_v27 dropping h_v28 he_v29 hinv12 e_v29 s12 v28
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s13 1#u32 (1) (by scalar_tac) hinv13 h64 as ⟨v30, s14, hinv14, h_v30⟩ growing hG carrying h_a1 h_v24 h_v26 h_v27 h_v29 dropping hinv13 s13
  store_step with Store.apply_rep s14 v29 v30 _ _ hinv14 h64 h_v29 h_v30 (by ns_tac) (by ns_tac) as ⟨v31, s15, hinv15, h_v31⟩ growing hG carrying h_a1 h_v24 h_v26 h_v27 dropping h_v29 h_v30 hinv14 s14 v29 v30
  store_step with Store.apply_rep s15 v27 v31 _ _ hinv15 h64 h_v27 h_v31 (by ns_tac) (by ns_tac) as ⟨v32, s16, hinv16, h_v32⟩ growing hG carrying h_a1 h_v24 h_v26 dropping h_v27 h_v31 hinv15 s15 v27 v31
  step as ⟨e_v33, he_v33⟩
  store_step with CtorSpec.eo_concat.construct s16 e_v33 (by rw [he_v33]; exact empty_args) hinv16 h64 as ⟨v33, s17, hinv17, h_v33⟩ growing hG carrying h_a1 h_v24 h_v26 h_v32 dropping he_v33 hinv16 e_v33 s16
  step as ⟨e_v34, he_v34⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s17 e_v34 (by rw [he_v34]; rfl) h_a1 hinv17 h64 as ⟨v34, s18, hinv18, h_v34⟩ growing hG carrying h_v24 h_v26 h_v32 h_v33 dropping h_a1 he_v34 hinv17 e_v34 s17
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s18 0#u32 (0) (by scalar_tac) hinv18 h64 as ⟨v35, s19, hinv19, h_v35⟩ growing hG carrying h_v24 h_v26 h_v32 h_v33 h_v34 dropping hinv18 s18
  store_step with Store.apply_rep s19 v34 v35 _ _ hinv19 h64 h_v34 h_v35 (by ns_tac) (by ns_tac) as ⟨v36, s20, hinv20, h_v36⟩ growing hG carrying h_v24 h_v26 h_v32 h_v33 dropping h_v34 h_v35 hinv19 s19 v34 v35
  store_step with Store.apply_rep s20 v33 v36 _ _ hinv20 h64 h_v33 h_v36 (by ns_tac) (by ns_tac) as ⟨v37, s21, hinv21, h_v37⟩ growing hG carrying h_v24 h_v26 h_v32 dropping h_v33 h_v36 hinv20 s20 v33 v36
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s21 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv21 h64 as ⟨v38, s22, hinv22, h_v38⟩ growing hG carrying h_v24 h_v26 h_v32 h_v37 dropping hinv21 s21
  store_step with Store.apply_rep s22 v37 v38 _ _ hinv22 h64 h_v37 h_v38 (by ns_tac) (by ns_tac) as ⟨v39, s23, hinv23, h_v39⟩ growing hG carrying h_v24 h_v26 h_v32 dropping h_v37 h_v38 hinv22 s22 v37 v38
  store_step with Store.apply_rep s23 v32 v39 _ _ hinv23 h64 h_v32 h_v39 (by ns_tac) (by ns_tac) as ⟨v40, s24, hinv24, h_v40⟩ growing hG carrying h_v24 h_v26 dropping h_v32 h_v39 hinv23 s23 v32 v39
  store_step with Store.apply_rep s24 v26 v40 _ _ hinv24 h64 h_v26 h_v40 (by ns_tac) (by ns_tac) as ⟨v41, s25, hinv25, h_v41⟩ growing hG carrying h_v24 dropping h_v26 h_v40 hinv24 s24 v26 v40
  store_step with Store.apply_rep s25 v24 v41 _ _ hinv25 h64 h_v24 h_v41 (by ns_tac) (by ns_tac) as ⟨v42, s26, hinv26, h_v42⟩ growing hG carrying dropping h_v24 h_v41 hinv25 s25 v24 v41
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

theorem case_0_eo__24eo_5fprog_5fbv_2dnor_2deliminate_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fbv_2dnor_2deliminate s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_bv_nor_eliminate.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_bv_nor_eliminate.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fbv_2dnor_2deliminate
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 dropping he_v0 e_v0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_bvnor.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0 dropping he_v1 hinv1 e_v1 s1
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 dropping h_v1 hinv2 s2 v1
  store_step with Store.apply_rep s3 v2 a1 _ _ hinv3 h64 h_v2 h_a1 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_v0 dropping h_v2 hinv3 s3 v2
  store_step with Store.apply_rep s4 v0 v3 _ _ hinv4 h64 h_v0 h_v3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 dropping h_v0 h_v3 hinv4 s4 v0 v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo_bvnot.construct s5 e_v5 (by rw [he_v5]; exact empty_args) hinv5 h64 as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_v4 dropping he_v5 hinv5 e_v5 s5
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_bvor.construct s6 e_v6 (by rw [he_v6]; exact empty_args) hinv6 h64 as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_v4 h_v5 dropping he_v6 hinv6 e_v6 s6
  store_step with Store.apply_rep s7 v6 a0 _ _ hinv7 h64 h_v6 h_a0 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_v4 h_v5 dropping h_v6 hinv7 s7 v6
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo_bvor.construct s8 e_v8 (by rw [he_v8]; exact empty_args) hinv8 h64 as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_a1 h_v4 h_v5 h_v7 dropping he_v8 hinv8 e_v8 s8
  store_step with Store.apply_rep s9 v8 a1 _ _ hinv9 h64 h_v8 h_a1 (by ns_tac) (by ns_tac) as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a0 h_v4 h_v5 h_v7 dropping h_a1 h_v8 hinv9 s9 v8
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo_bvor.construct s10 e_v10 (by rw [he_v10]; exact empty_args) hinv10 h64 as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_a0 h_v4 h_v5 h_v7 h_v9 dropping he_v10 hinv10 e_v10 s10
  store_step with ih.eo__24eo_5ftypeof s11 a0 _ hinv11 h64 (hG.rem hrem) h_a0 as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_v4 h_v5 h_v7 h_v9 h_v10 dropping h_a0 hinv11 s11
  store_step with ih.eo__24eo_5fnil s12 v10 v11 _ _ hinv12 h64 (hG.rem hrem) h_v10 h_v11 as ⟨v12, s13, hinv13, h_v12⟩ growing hG carrying h_v4 h_v5 h_v7 h_v9 dropping h_v10 h_v11 hinv12 s12 v10 v11
  store_step with Store.apply_mk_rep s13 v9 v12 _ _ hinv13 h64 h_v9 h_v12 as ⟨v13, s14, hinv14, h_v13⟩ growing hG carrying h_v4 h_v5 h_v7 dropping h_v12 h_v9 hinv13 s13 v12 v9
  store_step with Store.apply_mk_rep s14 v7 v13 _ _ hinv14 h64 h_v7 h_v13 as ⟨v14, s15, hinv15, h_v14⟩ growing hG carrying h_v4 h_v5 dropping h_v13 h_v7 hinv14 s14 v13 v7
  store_step with Store.apply_mk_rep s15 v5 v14 _ _ hinv15 h64 h_v5 h_v14 as ⟨v15, s16, hinv16, h_v15⟩ growing hG carrying h_v4 dropping h_v14 h_v5 hinv15 s15 v14 v5
  store_step with Store.apply_mk_rep s16 v4 v15 _ _ hinv16 h64 h_v4 h_v15 as ⟨v16, s17, hinv17, h_v16⟩ growing hG carrying dropping h_v15 h_v4 hinv16 s16 v15 v4
  case_done hinv17 hG with h_v16 in EoCases.__eo_prog_bv_nor_eliminate.case_0 using hn_a0 hn_a1

/-- logos's `__eo_prog_bv_nor_eliminate` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fbv_2dnor_2deliminate.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_bv_nor_eliminate x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_bv_nor_eliminate.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_bv_nor_eliminate
  unfold EoCases.__eo_prog_bv_nor_eliminate.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fbv_2dnor_2deliminate_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5fbv_2dnor_2deliminate s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_nor_eliminate x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fbv_2dnor_2deliminate.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5fbv_2dnor_2deliminate
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fbv_2dnor_2deliminate_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_bv_nor_eliminate.case_0

theorem eo__24eo_5fprog_5fbv_2dnor_2deliminate_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fbv_2dnor_2deliminate.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5fbv_2dnor_2deliminate
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fbv_2dnor_2deliminate s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_bv_nor_eliminate x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fbv_2dnor_2deliminate_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
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
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 dropping he_v0 e_v0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_bvnot.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0 dropping he_v1 hinv1 e_v1 s1
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo_bvnot.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_v0 h_v1 dropping he_v2 hinv2 e_v2 s2
  store_step with Store.apply_rep s3 v2 a0 _ _ hinv3 h64 h_v2 h_a0 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_v0 h_v1 dropping h_v2 hinv3 s3 v2
  store_step with Store.apply_rep s4 v1 v3 _ _ hinv4 h64 h_v1 h_v3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_v0 dropping h_v1 h_v3 hinv4 s4 v1 v3
  store_step with Store.apply_rep s5 v0 v4 _ _ hinv5 h64 h_v0 h_v4 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 dropping h_v0 h_v4 hinv5 s5 v0 v4
  store_step with Store.apply_rep s6 v5 a0 _ _ hinv6 h64 h_v5 h_a0 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying dropping h_a0 h_v5 hinv6 s6 v5
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
  unfold case_0_eo__24eo_5fprog_5fbv_2dnot_2dneq
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a1 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_bv_not_neq.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_not_neq.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_not_neq.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_v4 h_v6 h_v7 dropping h_a1 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_not_neq.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_not_neq.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_not_neq.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__3e.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_v4 h_v11 h_v13 h_v14 dropping h_v10 h_v6 h_v7 h_v8 he_v15 hinv1 e_v15 s1 v10 v6 v7 v8
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_not_neq.case_0
  pat_unapply h_v14 as ⟨v17, v18, x_v17, x_v18, h_v17, h_v18, hn_v17, hn_v18⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_not_neq.case_0
  step as ⟨e_v19, he_v19⟩
  store_step with CtorSpec.eo__40bvsize.construct s2 e_v19 (by rw [he_v19]; exact empty_args) hinv2 h64 as ⟨v19, s3, hinv3, h_v19⟩ growing hG carrying h_a0 h_v4 h_v11 h_v17 h_v18 dropping h_v13 h_v14 h_v15 he_v19 hinv2 e_v19 s2 v13 v14 v15
  pat_same v17 v19 with h_v17 h_v19 using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_not_neq.case_0
  pat_same v18 a0 with h_v18 h_a0 using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_not_neq.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s3 0#u32 (0) (by scalar_tac) hinv3 h64 as ⟨v20, s4, hinv4, h_v20⟩ growing hG carrying h_a0 h_v4 h_v11 dropping h_v17 h_v18 h_v19 hinv3 s3 v17 v18 v19
  pat_same v11 v20 with h_v11 h_v20 using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_not_neq.case_0
  store_step with Store.literal_boolean_spec s4 true hinv4 h64 as ⟨v21, s5, hinv5, h_v21⟩ growing hG carrying h_a0 h_v4 dropping h_v11 h_v20 hinv4 s4 v11 v20
  pat_same v4 v21 with h_v4 h_v21 using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_not_neq.case_0
  step as ⟨e_v22, he_v22⟩
  store_step with CtorSpec.eo__3d.construct s5 e_v22 (by rw [he_v22]; exact empty_args) hinv5 h64 as ⟨v22, s6, hinv6, h_v22⟩ growing hG carrying h_a0 dropping h_v21 h_v4 he_v22 hinv5 e_v22 s5 v21 v4
  step as ⟨e_v23, he_v23⟩
  store_step with CtorSpec.eo__3d.construct s6 e_v23 (by rw [he_v23]; exact empty_args) hinv6 h64 as ⟨v23, s7, hinv7, h_v23⟩ growing hG carrying h_a0 h_v22 dropping he_v23 hinv6 e_v23 s6
  store_step with Store.apply_rep s7 v23 a0 _ _ hinv7 h64 h_v23 h_a0 (by ns_tac) (by ns_tac) as ⟨v24, s8, hinv8, h_v24⟩ growing hG carrying h_a0 h_v22 dropping h_v23 hinv7 s7 v23
  step as ⟨e_v25, he_v25⟩
  store_step with CtorSpec.eo_bvnot.construct s8 e_v25 (by rw [he_v25]; exact empty_args) hinv8 h64 as ⟨v25, s9, hinv9, h_v25⟩ growing hG carrying h_a0 h_v22 h_v24 dropping he_v25 hinv8 e_v25 s8
  store_step with Store.apply_rep s9 v25 a0 _ _ hinv9 h64 h_v25 h_a0 (by ns_tac) (by ns_tac) as ⟨v26, s10, hinv10, h_v26⟩ growing hG carrying h_v22 h_v24 dropping h_a0 h_v25 hinv9 s9 v25
  store_step with Store.apply_rep s10 v24 v26 _ _ hinv10 h64 h_v24 h_v26 (by ns_tac) (by ns_tac) as ⟨v27, s11, hinv11, h_v27⟩ growing hG carrying h_v22 dropping h_v24 h_v26 hinv10 s10 v24 v26
  store_step with Store.apply_rep s11 v22 v27 _ _ hinv11 h64 h_v22 h_v27 (by ns_tac) (by ns_tac) as ⟨v28, s12, hinv12, h_v28⟩ growing hG carrying dropping h_v22 h_v27 hinv11 s11 v22 v27
  store_step with Store.literal_boolean_spec s12 false hinv12 h64 as ⟨v29, s13, hinv13, h_v29⟩ growing hG carrying h_v28 dropping hinv12 s12
  store_step with Store.apply_rep s13 v28 v29 _ _ hinv13 h64 h_v28 h_v29 (by ns_tac) (by ns_tac) as ⟨v30, s14, hinv14, h_v30⟩ growing hG carrying dropping h_v28 h_v29 hinv13 s13 v28 v29
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
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 dropping he_v0 e_v0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_not.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0 dropping he_v1 hinv1 e_v1 s1
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo_bvult.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 dropping he_v2 hinv2 e_v2 s2
  store_step with Store.apply_rep s3 v2 a0 _ _ hinv3 h64 h_v2 h_a0 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 dropping h_v2 hinv3 s3 v2
  store_step with Store.apply_rep s4 v3 a1 _ _ hinv4 h64 h_v3 h_a1 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 dropping h_v3 hinv4 s4 v3
  store_step with Store.apply_rep s5 v1 v4 _ _ hinv5 h64 h_v1 h_v4 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_v0 dropping h_v1 h_v4 hinv5 s5 v1 v4
  store_step with Store.apply_rep s6 v0 v5 _ _ hinv6 h64 h_v0 h_v5 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 dropping h_v0 h_v5 hinv6 s6 v0 v5
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo_bvule.construct s7 e_v7 (by rw [he_v7]; exact empty_args) hinv7 h64 as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_v6 dropping he_v7 hinv7 e_v7 s7
  store_step with Store.apply_rep s8 v7 a1 _ _ hinv8 h64 h_v7 h_a1 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_v6 dropping h_a1 h_v7 hinv8 s8 v7
  store_step with Store.apply_rep s9 v8 a0 _ _ hinv9 h64 h_v8 h_a0 (by ns_tac) (by ns_tac) as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_v6 dropping h_a0 h_v8 hinv9 s9 v8
  store_step with Store.apply_rep s10 v6 v9 _ _ hinv10 h64 h_v6 h_v9 (by ns_tac) (by ns_tac) as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying dropping h_v6 h_v9 hinv10 s10 v6 v9
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
  unfold case_0_eo__24eo_5fprog_5fbv_2dnot_2dxor
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 dropping he_v0 e_v0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_bvnot.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 dropping he_v1 hinv1 e_v1 s1
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo_bvxor.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 dropping he_v2 hinv2 e_v2 s2
  store_step with Store.apply_rep s3 v2 a0 _ _ hinv3 h64 h_v2 h_a0 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 dropping h_v2 hinv3 s3 v2
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo_bvxor.construct s4 e_v4 (by rw [he_v4]; exact empty_args) hinv4 h64 as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v3 dropping he_v4 hinv4 e_v4 s4
  store_step with Store.apply_rep s5 v4 a1 _ _ hinv5 h64 h_v4 h_a1 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v3 dropping h_v4 hinv5 s5 v4
  store_step with Store.apply_rep s6 v5 a2 _ _ hinv6 h64 h_v5 h_a2 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v3 dropping h_v5 hinv6 s6 v5
  store_step with Store.apply_rep s7 v3 v6 _ _ hinv7 h64 h_v3 h_v6 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 dropping h_v3 h_v6 hinv7 s7 v3 v6
  store_step with Store.apply_rep s8 v1 v7 _ _ hinv8 h64 h_v1 h_v7 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 dropping h_v1 h_v7 hinv8 s8 v1 v7
  store_step with Store.apply_rep s9 v0 v8 _ _ hinv9 h64 h_v0 h_v8 (by ns_tac) (by ns_tac) as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a0 h_a1 h_a2 dropping h_v0 h_v8 hinv9 s9 v0 v8
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo_bvxor.construct s10 e_v10 (by rw [he_v10]; exact empty_args) hinv10 h64 as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_a0 h_a1 h_a2 h_v9 dropping he_v10 hinv10 e_v10 s10
  step as ⟨e_v11, he_v11⟩
  store_step with CtorSpec.eo_bvnot.construct s11 e_v11 (by rw [he_v11]; exact empty_args) hinv11 h64 as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_a0 h_a1 h_a2 h_v9 h_v10 dropping he_v11 hinv11 e_v11 s11
  store_step with Store.apply_rep s12 v11 a0 _ _ hinv12 h64 h_v11 h_a0 (by ns_tac) (by ns_tac) as ⟨v12, s13, hinv13, h_v12⟩ growing hG carrying h_a1 h_a2 h_v9 h_v10 dropping h_a0 h_v11 hinv12 s12 v11
  store_step with Store.apply_rep s13 v10 v12 _ _ hinv13 h64 h_v10 h_v12 (by ns_tac) (by ns_tac) as ⟨v13, s14, hinv14, h_v13⟩ growing hG carrying h_a1 h_a2 h_v9 dropping h_v10 h_v12 hinv13 s13 v10 v12
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo_bvxor.construct s14 e_v14 (by rw [he_v14]; exact empty_args) hinv14 h64 as ⟨v14, s15, hinv15, h_v14⟩ growing hG carrying h_a1 h_a2 h_v9 h_v13 dropping he_v14 hinv14 e_v14 s14
  store_step with Store.apply_rep s15 v14 a1 _ _ hinv15 h64 h_v14 h_a1 (by ns_tac) (by ns_tac) as ⟨v15, s16, hinv16, h_v15⟩ growing hG carrying h_a2 h_v9 h_v13 dropping h_a1 h_v14 hinv15 s15 v14
  store_step with Store.apply_rep s16 v15 a2 _ _ hinv16 h64 h_v15 h_a2 (by ns_tac) (by ns_tac) as ⟨v16, s17, hinv17, h_v16⟩ growing hG carrying h_v9 h_v13 dropping h_a2 h_v15 hinv16 s16 v15
  store_step with Store.apply_rep s17 v13 v16 _ _ hinv17 h64 h_v13 h_v16 (by ns_tac) (by ns_tac) as ⟨v17, s18, hinv18, h_v17⟩ growing hG carrying h_v9 dropping h_v13 h_v16 hinv17 s17 v13 v16
  store_step with Store.apply_rep s18 v9 v17 _ _ hinv18 h64 h_v9 h_v17 (by ns_tac) (by ns_tac) as ⟨v18, s19, hinv19, h_v18⟩ growing hG carrying dropping h_v17 h_v9 hinv18 s18 v17 v9
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
  unfold case_0_eo__24eo_5fprog_5fbv_2dredand_2deliminate
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a2 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_bv_redand_eliminate.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_redand_eliminate.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_redand_eliminate.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_v4 h_v6 h_v7 dropping h_a2 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_redand_eliminate.case_0
  pat_same v7 a1 with h_v7 h_a1 using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_redand_eliminate.case_0
  pat_unapply h_v4 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_redand_eliminate.case_0
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo__40bvsize.construct s1 e_v12 (by rw [he_v12]; exact empty_args) hinv1 h64 as ⟨v12, s2, hinv2, h_v12⟩ growing hG carrying h_a0 h_a1 h_v10 h_v11 dropping h_v4 h_v6 h_v7 h_v8 he_v12 hinv1 e_v12 s1 v4 v6 v7 v8
  pat_same v10 v12 with h_v10 h_v12 using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_redand_eliminate.case_0
  pat_same v11 a0 with h_v11 h_a0 using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_redand_eliminate.case_0
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo__3d.construct s2 e_v13 (by rw [he_v13]; exact empty_args) hinv2 h64 as ⟨v13, s3, hinv3, h_v13⟩ growing hG carrying h_a0 h_a1 dropping h_v10 h_v11 h_v12 he_v13 hinv2 e_v13 s2 v10 v11 v12
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo_bvredand.construct s3 e_v14 (by rw [he_v14]; exact empty_args) hinv3 h64 as ⟨v14, s4, hinv4, h_v14⟩ growing hG carrying h_a0 h_a1 h_v13 dropping he_v14 hinv3 e_v14 s3
  store_step with Store.apply_rep s4 v14 a0 _ _ hinv4 h64 h_v14 h_a0 (by ns_tac) (by ns_tac) as ⟨v15, s5, hinv5, h_v15⟩ growing hG carrying h_a0 h_a1 h_v13 dropping h_v14 hinv4 s4 v14
  store_step with Store.apply_rep s5 v13 v15 _ _ hinv5 h64 h_v13 h_v15 (by ns_tac) (by ns_tac) as ⟨v16, s6, hinv6, h_v16⟩ growing hG carrying h_a0 h_a1 dropping h_v13 h_v15 hinv5 s5 v13 v15
  step as ⟨e_v17, he_v17⟩
  store_step with CtorSpec.eo_bvcomp.construct s6 e_v17 (by rw [he_v17]; exact empty_args) hinv6 h64 as ⟨v17, s7, hinv7, h_v17⟩ growing hG carrying h_a0 h_a1 h_v16 dropping he_v17 hinv6 e_v17 s6
  store_step with Store.apply_rep s7 v17 a0 _ _ hinv7 h64 h_v17 h_a0 (by ns_tac) (by ns_tac) as ⟨v18, s8, hinv8, h_v18⟩ growing hG carrying h_a1 h_v16 dropping h_a0 h_v17 hinv7 s7 v17
  step as ⟨e_v19, he_v19⟩
  store_step with CtorSpec.eo_bvnot.construct s8 e_v19 (by rw [he_v19]; exact empty_args) hinv8 h64 as ⟨v19, s9, hinv9, h_v19⟩ growing hG carrying h_a1 h_v16 h_v18 dropping he_v19 hinv8 e_v19 s8
  step as ⟨e_v20, he_v20⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s9 e_v20 (by rw [he_v20]; rfl) h_a1 hinv9 h64 as ⟨v20, s10, hinv10, h_v20⟩ growing hG carrying h_v16 h_v18 h_v19 dropping h_a1 he_v20 hinv9 e_v20 s9
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s10 0#u32 (0) (by scalar_tac) hinv10 h64 as ⟨v21, s11, hinv11, h_v21⟩ growing hG carrying h_v16 h_v18 h_v19 h_v20 dropping hinv10 s10
  store_step with Store.apply_rep s11 v20 v21 _ _ hinv11 h64 h_v20 h_v21 (by ns_tac) (by ns_tac) as ⟨v22, s12, hinv12, h_v22⟩ growing hG carrying h_v16 h_v18 h_v19 dropping h_v20 h_v21 hinv11 s11 v20 v21
  store_step with Store.apply_rep s12 v19 v22 _ _ hinv12 h64 h_v19 h_v22 (by ns_tac) (by ns_tac) as ⟨v23, s13, hinv13, h_v23⟩ growing hG carrying h_v16 h_v18 dropping h_v19 h_v22 hinv12 s12 v19 v22
  store_step with Store.apply_rep s13 v18 v23 _ _ hinv13 h64 h_v18 h_v23 (by ns_tac) (by ns_tac) as ⟨v24, s14, hinv14, h_v24⟩ growing hG carrying h_v16 dropping h_v18 h_v23 hinv13 s13 v18 v23
  store_step with Store.apply_rep s14 v16 v24 _ _ hinv14 h64 h_v16 h_v24 (by ns_tac) (by ns_tac) as ⟨v25, s15, hinv15, h_v25⟩ growing hG carrying dropping h_v16 h_v24 hinv14 s14 v16 v24
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
  unfold case_0_eo__24eo_5fprog_5fbv_2dredor_2deliminate
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a2 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_bv_redor_eliminate.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_redor_eliminate.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_redor_eliminate.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_v4 h_v6 h_v7 dropping h_a2 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_redor_eliminate.case_0
  pat_same v7 a1 with h_v7 h_a1 using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_redor_eliminate.case_0
  pat_unapply h_v4 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_redor_eliminate.case_0
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo__40bvsize.construct s1 e_v12 (by rw [he_v12]; exact empty_args) hinv1 h64 as ⟨v12, s2, hinv2, h_v12⟩ growing hG carrying h_a0 h_a1 h_v10 h_v11 dropping h_v4 h_v6 h_v7 h_v8 he_v12 hinv1 e_v12 s1 v4 v6 v7 v8
  pat_same v10 v12 with h_v10 h_v12 using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_redor_eliminate.case_0
  pat_same v11 a0 with h_v11 h_a0 using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_redor_eliminate.case_0
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo__3d.construct s2 e_v13 (by rw [he_v13]; exact empty_args) hinv2 h64 as ⟨v13, s3, hinv3, h_v13⟩ growing hG carrying h_a0 h_a1 dropping h_v10 h_v11 h_v12 he_v13 hinv2 e_v13 s2 v10 v11 v12
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo_bvredor.construct s3 e_v14 (by rw [he_v14]; exact empty_args) hinv3 h64 as ⟨v14, s4, hinv4, h_v14⟩ growing hG carrying h_a0 h_a1 h_v13 dropping he_v14 hinv3 e_v14 s3
  store_step with Store.apply_rep s4 v14 a0 _ _ hinv4 h64 h_v14 h_a0 (by ns_tac) (by ns_tac) as ⟨v15, s5, hinv5, h_v15⟩ growing hG carrying h_a0 h_a1 h_v13 dropping h_v14 hinv4 s4 v14
  store_step with Store.apply_rep s5 v13 v15 _ _ hinv5 h64 h_v13 h_v15 (by ns_tac) (by ns_tac) as ⟨v16, s6, hinv6, h_v16⟩ growing hG carrying h_a0 h_a1 dropping h_v13 h_v15 hinv5 s5 v13 v15
  step as ⟨e_v17, he_v17⟩
  store_step with CtorSpec.eo_bvnot.construct s6 e_v17 (by rw [he_v17]; exact empty_args) hinv6 h64 as ⟨v17, s7, hinv7, h_v17⟩ growing hG carrying h_a0 h_a1 h_v16 dropping he_v17 hinv6 e_v17 s6
  step as ⟨e_v18, he_v18⟩
  store_step with CtorSpec.eo_bvcomp.construct s7 e_v18 (by rw [he_v18]; exact empty_args) hinv7 h64 as ⟨v18, s8, hinv8, h_v18⟩ growing hG carrying h_a0 h_a1 h_v16 h_v17 dropping he_v18 hinv7 e_v18 s7
  store_step with Store.apply_rep s8 v18 a0 _ _ hinv8 h64 h_v18 h_a0 (by ns_tac) (by ns_tac) as ⟨v19, s9, hinv9, h_v19⟩ growing hG carrying h_a1 h_v16 h_v17 dropping h_a0 h_v18 hinv8 s8 v18
  step as ⟨e_v20, he_v20⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s9 e_v20 (by rw [he_v20]; rfl) h_a1 hinv9 h64 as ⟨v20, s10, hinv10, h_v20⟩ growing hG carrying h_v16 h_v17 h_v19 dropping h_a1 he_v20 hinv9 e_v20 s9
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s10 0#u32 (0) (by scalar_tac) hinv10 h64 as ⟨v21, s11, hinv11, h_v21⟩ growing hG carrying h_v16 h_v17 h_v19 h_v20 dropping hinv10 s10
  store_step with Store.apply_rep s11 v20 v21 _ _ hinv11 h64 h_v20 h_v21 (by ns_tac) (by ns_tac) as ⟨v22, s12, hinv12, h_v22⟩ growing hG carrying h_v16 h_v17 h_v19 dropping h_v20 h_v21 hinv11 s11 v20 v21
  store_step with Store.apply_rep s12 v19 v22 _ _ hinv12 h64 h_v19 h_v22 (by ns_tac) (by ns_tac) as ⟨v23, s13, hinv13, h_v23⟩ growing hG carrying h_v16 h_v17 dropping h_v19 h_v22 hinv12 s12 v19 v22
  store_step with Store.apply_rep s13 v17 v23 _ _ hinv13 h64 h_v17 h_v23 (by ns_tac) (by ns_tac) as ⟨v24, s14, hinv14, h_v24⟩ growing hG carrying h_v16 dropping h_v17 h_v23 hinv13 s13 v17 v23
  store_step with Store.apply_rep s14 v16 v24 _ _ hinv14 h64 h_v16 h_v24 (by ns_tac) (by ns_tac) as ⟨v25, s15, hinv15, h_v25⟩ growing hG carrying dropping h_v16 h_v24 hinv14 s14 v16 v24
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

theorem case_0_eo__24eo_5fprog_5fbv_2drepeat_2delim_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fbv_2drepeat_2delim s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_bv_repeat_elim.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_bv_repeat_elim.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fbv_2drepeat_2delim
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_repeat_elim.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_repeat_elim.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__3d.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_repeat_elim.case_0
  pat_unapply h_v5 as ⟨v8, v9, x_v8, x_v9, h_v8, h_v9, hn_v8, hn_v9⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_repeat_elim.case_0
  pat_destruct CtorSpec.eo_repeat.destruct h_v8 as ⟨v11, x_v11, h_v11⟩ else hinv1 hG in EoCases.__eo_prog_bv_repeat_elim.case_0
  obtain hn_v11 := CtorSpec.eo_repeat.fields_ne_stuck hinv1 h_v8
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo_concat.construct s1 e_v12 (by rw [he_v12]; exact empty_args) hinv1 h64 as ⟨v12, s2, hinv2, h_v12⟩ growing hG carrying h_v2 h_v9 h_v11 dropping h_v4 h_v5 h_v6 h_v8 he_v12 hinv1 e_v12 s1 v4 v5 v6 v8
  step as ⟨e_v13, he_v13⟩
  store_step with Store.builtin_spec_is_z s2 e_v13 (by rw [he_v13]; rfl) h_v11 hinv2 h64 as ⟨v13, s3, hinv3, h_v13⟩ growing hG carrying h_v2 h_v9 h_v11 h_v12 dropping he_v13 hinv2 e_v13 s2
  step as ⟨e_v14, he_v14⟩
  store_step with Store.builtin_spec_is_neg s3 e_v14 (by rw [he_v14]; rfl) h_v11 hinv3 h64 as ⟨v14, s4, hinv4, h_v14⟩ growing hG carrying h_v2 h_v9 h_v11 h_v12 h_v13 dropping he_v14 hinv3 e_v14 s3
  step as ⟨e_v15, he_v15⟩
  store_step with Store.builtin_spec_not s4 e_v15 (by rw [he_v15]; rfl) h_v14 hinv4 h64 as ⟨v15, s5, hinv5, h_v15⟩ growing hG carrying h_v2 h_v9 h_v11 h_v12 h_v13 dropping h_v14 he_v15 hinv4 e_v15 s4 v14
  step as ⟨e_v16, he_v16⟩
  store_step with Store.builtin_spec_and s5 e_v16 (by rw [he_v16]; rfl) h_v13 h_v15 hinv5 h64 as ⟨v16, s6, hinv6, h_v16⟩ growing hG carrying h_v2 h_v9 h_v11 h_v12 dropping h_v13 h_v15 he_v16 hinv5 e_v16 s5 v13 v15
  have h_ite_v21 := (show if_0_eo__24eo_5fprog_5fbv_2drepeat_2delim s6 v16 v9 v11 ⦃ r s' => s'.Inv ∧ s6.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_0_eo__24eo_5fprog_5fbv_2drepeat_2delim
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s6
    rcases Store.boolean_value_term h_v16 with ⟨hx_17, hbv_17⟩ | ⟨hx_17, hbv_17⟩ | ⟨hx_17, hbv_17⟩
    · ite_branch hbv_17
      step as ⟨e_v17, he_v17⟩
      store_step with CtorSpec.eo_concat.construct s6 e_v17 (by rw [he_v17]; exact empty_args) hinv6 h64 as ⟨v17, s7, hinv7, h_v17⟩ growing hG carrying h_v2 h_v9 h_v11 h_v12 dropping h_v16 he_v17 e_v17 v16
      step as ⟨e_v18, he_v18⟩
      store_step with Store.builtin_spec_list_repeat n ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s7 e_v18 (by rw [he_v18]; rfl) h_v17 h_v9 h_v11 hinv7 h64 (hG.rem hrem) op_not_left_eo_concat as ⟨v18, s8, hinv8, h_v18⟩ growing hG carrying h_v2 h_v9 h_v11 h_v12 dropping h_v17 he_v18 e_v18 v17
      ite_done hinv8 hG with (eo_ite_true_rep _ hx_17 h_v18)
    · ite_branch hbv_17
      step as ⟨e_v19, he_v19⟩
      store_step with CtorSpec.eo_repeat.construct s6 e_v19 (by rw [he_v19]; rfl) h_v11 hinv6 h64 as ⟨v19, s7, hinv7, h_v19⟩ growing hG carrying h_v2 h_v9 h_v11 h_v12 dropping h_v16 he_v19 e_v19 v16
      store_step with Store.apply_rep s7 v19 v9 _ _ hinv7 h64 h_v19 h_v9 (by ns_tac) (by ns_tac) as ⟨v20, s8, hinv8, h_v20⟩ growing hG carrying h_v2 h_v9 h_v11 h_v12 dropping h_v19 v19
      ite_done hinv8 hG with (eo_ite_false_rep _ hx_17 h_v20)
    · ite_branch hbv_17
      ite_stuck hinv6 hG with hx_17)
  store_step with h_ite_v21 as ⟨v21, s7, hinv7, h_v21⟩ growing hG carrying h_v2 h_v9 h_v11 h_v12 dropping h_ite_v21 h_v16 hinv6 s6 v16
  step as ⟨e_v22, he_v22⟩
  store_step with Store.builtin_spec_list_singleton_elim n ih.eo__24eo_5fis_5flist_5fnil s7 e_v22 (by rw [he_v22]; rfl) h_v12 h_v21 hinv7 h64 (hG.rem hrem) op_not_left_eo_concat op_nil_apply_eo_concat as ⟨v22, s8, hinv8, h_v22⟩ growing hG carrying h_v2 h_v9 h_v11 dropping h_v12 h_v21 he_v22 hinv7 e_v22 s7 v12 v21
  have h_req_v28 := (show requires_1_eo__24eo_5fprog_5fbv_2drepeat_2delim s8 v22 v2 v11 v9 ⦃ r s' => s'.Inv ∧ s8.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold requires_1_eo__24eo_5fprog_5fbv_2drepeat_2delim
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s8
    req_same v22 v2 with h_v22 h_v2 using hinv8 hG
    req_stuck h_v22 as hq_v22 using hinv8 hG
    step as ⟨e_v23, he_v23⟩
    store_step with CtorSpec.eo__3d.construct s8 e_v23 (by rw [he_v23]; exact empty_args) hinv8 h64 as ⟨v23, s9, hinv9, h_v23⟩ growing hG carrying h_v2 h_v9 h_v11 dropping h_v22 he_v23 hinv8 e_v23 s8 v22
    step as ⟨e_v24, he_v24⟩
    store_step with CtorSpec.eo_repeat.construct s9 e_v24 (by rw [he_v24]; rfl) h_v11 hinv9 h64 as ⟨v24, s10, hinv10, h_v24⟩ growing hG carrying h_v2 h_v9 h_v23 dropping h_v11 he_v24 hinv9 e_v24 s9 v11
    store_step with Store.apply_rep s10 v24 v9 _ _ hinv10 h64 h_v24 h_v9 (by ns_tac) (by ns_tac) as ⟨v25, s11, hinv11, h_v25⟩ growing hG carrying h_v2 h_v23 dropping h_v24 h_v9 hinv10 s10 v24 v9
    store_step with Store.apply_rep s11 v23 v25 _ _ hinv11 h64 h_v23 h_v25 (by ns_tac) (by ns_tac) as ⟨v26, s12, hinv12, h_v26⟩ growing hG carrying h_v2 dropping h_v23 h_v25 hinv11 s11 v23 v25
    store_step with Store.apply_rep s12 v26 v2 _ _ hinv12 h64 h_v26 h_v2 (by ns_tac) (by ns_tac) as ⟨v27, s13, hinv13, h_v27⟩ growing hG carrying dropping h_v2 h_v26 hinv12 s12 v2 v26
    req_done hinv13 hG with h_v27 using hq_v22)
  store_step with h_req_v28 as ⟨v28, s14, hinv14, h_v28⟩ growing hG carrying dropping h_req_v28 h_v11 h_v2 h_v22 h_v9 hinv8 s8 v11 v2 v22 v9
  case_done hinv14 hG with h_v28 in EoCases.__eo_prog_bv_repeat_elim.case_0 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5 hn_v8 hn_v9 hn_v11

/-- logos's `__eo_prog_bv_repeat_elim` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fbv_2drepeat_2delim.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_bv_repeat_elim x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_bv_repeat_elim.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_bv_repeat_elim
  unfold EoCases.__eo_prog_bv_repeat_elim.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fbv_2drepeat_2delim_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fbv_2drepeat_2delim s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_repeat_elim x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fbv_2drepeat_2delim.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fbv_2drepeat_2delim
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fbv_2drepeat_2delim_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_bv_repeat_elim.case_0

theorem eo__24eo_5fprog_5fbv_2drepeat_2delim_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fbv_2drepeat_2delim.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fbv_2drepeat_2delim
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fbv_2drepeat_2delim s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_bv_repeat_elim x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fbv_2drepeat_2delim_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fbv_2drotate_2dleft_2deliminate_2d1_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 a6 a7 a8 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _) (x_a7 : _) (x_a8 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) (h_a6 : Represents.rep s a6 x_a6) (h_a7 : Represents.rep s a7 x_a7) (h_a8 : Represents.rep s a8 x_a8) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) (hn_a4 : x_a4 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fbv_2drotate_2dleft_2deliminate_2d1 s a0 a1 a2 a3 a4 a5 a6 a7 a8 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_bv_rotate_left_eliminate_1.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_bv_rotate_left_eliminate_1.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fbv_2drotate_2dleft_2deliminate_2d1
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a5 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_bv_rotate_left_eliminate_1.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_rotate_left_eliminate_1.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_rotate_left_eliminate_1.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a6 h_a7 h_a8 h_v4 h_v6 h_v7 dropping h_a5 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_rotate_left_eliminate_1.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_rotate_left_eliminate_1.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_rotate_left_eliminate_1.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__3d.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a6 h_a7 h_a8 h_v4 h_v11 h_v13 h_v14 dropping h_v10 h_v6 h_v7 h_v8 he_v15 hinv1 e_v15 s1 v10 v6 v7 v8
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_rotate_left_eliminate_1.case_0
  pat_unapply h_v14 as ⟨v17, v18, x_v17, x_v18, h_v17, h_v18, hn_v17, hn_v18⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_rotate_left_eliminate_1.case_0
  pat_unapply h_v17 as ⟨v20, v21, x_v20, x_v21, h_v20, h_v21, hn_v20, hn_v21⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_rotate_left_eliminate_1.case_0
  step as ⟨e_v22, he_v22⟩
  store_step with CtorSpec.eo_mod.construct s2 e_v22 (by rw [he_v22]; exact empty_args) hinv2 h64 as ⟨v22, s3, hinv3, h_v22⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a6 h_a7 h_a8 h_v4 h_v11 h_v18 h_v20 h_v21 dropping h_v13 h_v14 h_v15 h_v17 he_v22 hinv2 e_v22 s2 v13 v14 v15 v17
  pat_same v20 v22 with h_v20 h_v22 using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_rotate_left_eliminate_1.case_0
  pat_same v21 a1 with h_v21 h_a1 using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_rotate_left_eliminate_1.case_0
  pat_unapply h_v18 as ⟨v24, v25, x_v24, x_v25, h_v24, h_v25, hn_v24, hn_v25⟩ using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_rotate_left_eliminate_1.case_0
  step as ⟨e_v26, he_v26⟩
  store_step with CtorSpec.eo__40bvsize.construct s3 e_v26 (by rw [he_v26]; exact empty_args) hinv3 h64 as ⟨v26, s4, hinv4, h_v26⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a6 h_a7 h_a8 h_v4 h_v11 h_v24 h_v25 dropping h_v18 h_v20 h_v21 h_v22 he_v26 hinv3 e_v26 s3 v18 v20 v21 v22
  pat_same v24 v26 with h_v24 h_v26 using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_rotate_left_eliminate_1.case_0
  pat_same v25 a0 with h_v25 h_a0 using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_rotate_left_eliminate_1.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s4 0#u32 (0) (by scalar_tac) hinv4 h64 as ⟨v27, s5, hinv5, h_v27⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a6 h_a7 h_a8 h_v4 h_v11 dropping h_v24 h_v25 h_v26 hinv4 s4 v24 v25 v26
  pat_same v11 v27 with h_v11 h_v27 using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_rotate_left_eliminate_1.case_0
  store_step with Store.literal_boolean_spec s5 false hinv5 h64 as ⟨v28, s6, hinv6, h_v28⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a6 h_a7 h_a8 h_v4 dropping h_v11 h_v27 hinv5 s5 v11 v27
  pat_same v4 v28 with h_v4 h_v28 using hinv6 else hinv6 hG in EoCases.__eo_prog_bv_rotate_left_eliminate_1.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a6 as ⟨v30, x_v30, h_v30⟩ else hinv6 hG in EoCases.__eo_prog_bv_rotate_left_eliminate_1.case_0
  pat_unapply h_v30 as ⟨v32, v33, x_v32, x_v33, h_v32, h_v33, hn_v32, hn_v33⟩ using hinv6 else hinv6 hG in EoCases.__eo_prog_bv_rotate_left_eliminate_1.case_0
  pat_unapply h_v32 as ⟨v35, v36, x_v35, x_v36, h_v35, h_v36, hn_v35, hn_v36⟩ using hinv6 else hinv6 hG in EoCases.__eo_prog_bv_rotate_left_eliminate_1.case_0
  step as ⟨e_v37, he_v37⟩
  store_step with CtorSpec.eo__3d.construct s6 e_v37 (by rw [he_v37]; exact empty_args) hinv6 h64 as ⟨v37, s7, hinv7, h_v37⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a7 h_a8 h_v33 h_v35 h_v36 dropping h_a6 h_v28 h_v30 h_v32 h_v4 he_v37 hinv6 e_v37 s6 v28 v30 v32 v4
  pat_same v35 v37 with h_v35 h_v37 using hinv7 else hinv7 hG in EoCases.__eo_prog_bv_rotate_left_eliminate_1.case_0
  pat_same v36 a2 with h_v36 h_a2 using hinv7 else hinv7 hG in EoCases.__eo_prog_bv_rotate_left_eliminate_1.case_0
  pat_unapply h_v33 as ⟨v39, v40, x_v39, x_v40, h_v39, h_v40, hn_v39, hn_v40⟩ using hinv7 else hinv7 hG in EoCases.__eo_prog_bv_rotate_left_eliminate_1.case_0
  pat_unapply h_v39 as ⟨v42, v43, x_v42, x_v43, h_v42, h_v43, hn_v42, hn_v43⟩ using hinv7 else hinv7 hG in EoCases.__eo_prog_bv_rotate_left_eliminate_1.case_0
  step as ⟨e_v44, he_v44⟩
  store_step with CtorSpec.eo__2d.construct s7 e_v44 (by rw [he_v44]; exact empty_args) hinv7 h64 as ⟨v44, s8, hinv8, h_v44⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a7 h_a8 h_v40 h_v42 h_v43 dropping h_v33 h_v35 h_v36 h_v37 h_v39 he_v44 hinv7 e_v44 s7 v33 v35 v36 v37 v39
  pat_same v42 v44 with h_v42 h_v44 using hinv8 else hinv8 hG in EoCases.__eo_prog_bv_rotate_left_eliminate_1.case_0
  pat_unapply h_v43 as ⟨v46, v47, x_v46, x_v47, h_v46, h_v47, hn_v46, hn_v47⟩ using hinv8 else hinv8 hG in EoCases.__eo_prog_bv_rotate_left_eliminate_1.case_0
  step as ⟨e_v48, he_v48⟩
  store_step with CtorSpec.eo__40bvsize.construct s8 e_v48 (by rw [he_v48]; exact empty_args) hinv8 h64 as ⟨v48, s9, hinv9, h_v48⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a7 h_a8 h_v40 h_v46 h_v47 dropping h_v42 h_v43 h_v44 he_v48 hinv8 e_v48 s8 v42 v43 v44
  pat_same v46 v48 with h_v46 h_v48 using hinv9 else hinv9 hG in EoCases.__eo_prog_bv_rotate_left_eliminate_1.case_0
  pat_same v47 a0 with h_v47 h_a0 using hinv9 else hinv9 hG in EoCases.__eo_prog_bv_rotate_left_eliminate_1.case_0
  pat_unapply h_v40 as ⟨v50, v51, x_v50, x_v51, h_v50, h_v51, hn_v50, hn_v51⟩ using hinv9 else hinv9 hG in EoCases.__eo_prog_bv_rotate_left_eliminate_1.case_0
  pat_unapply h_v50 as ⟨v53, v54, x_v53, x_v54, h_v53, h_v54, hn_v53, hn_v54⟩ using hinv9 else hinv9 hG in EoCases.__eo_prog_bv_rotate_left_eliminate_1.case_0
  step as ⟨e_v55, he_v55⟩
  store_step with CtorSpec.eo__2b.construct s9 e_v55 (by rw [he_v55]; exact empty_args) hinv9 h64 as ⟨v55, s10, hinv10, h_v55⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a7 h_a8 h_v51 h_v53 h_v54 dropping h_v40 h_v46 h_v47 h_v48 h_v50 he_v55 hinv9 e_v55 s9 v40 v46 v47 v48 v50
  pat_same v53 v55 with h_v53 h_v55 using hinv10 else hinv10 hG in EoCases.__eo_prog_bv_rotate_left_eliminate_1.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s10 1#u32 (1) (by scalar_tac) hinv10 h64 as ⟨v56, s11, hinv11, h_v56⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a7 h_a8 h_v51 h_v54 dropping h_v53 h_v55 hinv10 s10 v53 v55
  pat_same v54 v56 with h_v54 h_v56 using hinv11 else hinv11 hG in EoCases.__eo_prog_bv_rotate_left_eliminate_1.case_0
  pat_unapply h_v51 as ⟨v58, v59, x_v58, x_v59, h_v58, h_v59, hn_v58, hn_v59⟩ using hinv11 else hinv11 hG in EoCases.__eo_prog_bv_rotate_left_eliminate_1.case_0
  pat_unapply h_v58 as ⟨v61, v62, x_v61, x_v62, h_v61, h_v62, hn_v61, hn_v62⟩ using hinv11 else hinv11 hG in EoCases.__eo_prog_bv_rotate_left_eliminate_1.case_0
  step as ⟨e_v63, he_v63⟩
  store_step with CtorSpec.eo__2b.construct s11 e_v63 (by rw [he_v63]; exact empty_args) hinv11 h64 as ⟨v63, s12, hinv12, h_v63⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a7 h_a8 h_v59 h_v61 h_v62 dropping h_v51 h_v54 h_v56 h_v58 he_v63 hinv11 e_v63 s11 v51 v54 v56 v58
  pat_same v61 v63 with h_v61 h_v63 using hinv12 else hinv12 hG in EoCases.__eo_prog_bv_rotate_left_eliminate_1.case_0
  pat_unapply h_v62 as ⟨v65, v66, x_v65, x_v66, h_v65, h_v66, hn_v65, hn_v66⟩ using hinv12 else hinv12 hG in EoCases.__eo_prog_bv_rotate_left_eliminate_1.case_0
  pat_unapply h_v65 as ⟨v68, v69, x_v68, x_v69, h_v68, h_v69, hn_v68, hn_v69⟩ using hinv12 else hinv12 hG in EoCases.__eo_prog_bv_rotate_left_eliminate_1.case_0
  step as ⟨e_v70, he_v70⟩
  store_step with CtorSpec.eo_mod.construct s12 e_v70 (by rw [he_v70]; exact empty_args) hinv12 h64 as ⟨v70, s13, hinv13, h_v70⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a7 h_a8 h_v59 h_v66 h_v68 h_v69 dropping h_v61 h_v62 h_v63 h_v65 he_v70 hinv12 e_v70 s12 v61 v62 v63 v65
  pat_same v68 v70 with h_v68 h_v70 using hinv13 else hinv13 hG in EoCases.__eo_prog_bv_rotate_left_eliminate_1.case_0
  pat_same v69 a1 with h_v69 h_a1 using hinv13 else hinv13 hG in EoCases.__eo_prog_bv_rotate_left_eliminate_1.case_0
  pat_unapply h_v66 as ⟨v72, v73, x_v72, x_v73, h_v72, h_v73, hn_v72, hn_v73⟩ using hinv13 else hinv13 hG in EoCases.__eo_prog_bv_rotate_left_eliminate_1.case_0
  step as ⟨e_v74, he_v74⟩
  store_step with CtorSpec.eo__40bvsize.construct s13 e_v74 (by rw [he_v74]; exact empty_args) hinv13 h64 as ⟨v74, s14, hinv14, h_v74⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a7 h_a8 h_v59 h_v72 h_v73 dropping h_v66 h_v68 h_v69 h_v70 he_v74 hinv13 e_v74 s13 v66 v68 v69 v70
  pat_same v72 v74 with h_v72 h_v74 using hinv14 else hinv14 hG in EoCases.__eo_prog_bv_rotate_left_eliminate_1.case_0
  pat_same v73 a0 with h_v73 h_a0 using hinv14 else hinv14 hG in EoCases.__eo_prog_bv_rotate_left_eliminate_1.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s14 0#u32 (0) (by scalar_tac) hinv14 h64 as ⟨v75, s15, hinv15, h_v75⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a7 h_a8 h_v59 dropping h_v72 h_v73 h_v74 hinv14 s14 v72 v73 v74
  pat_same v59 v75 with h_v59 h_v75 using hinv15 else hinv15 hG in EoCases.__eo_prog_bv_rotate_left_eliminate_1.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a7 as ⟨v77, x_v77, h_v77⟩ else hinv15 hG in EoCases.__eo_prog_bv_rotate_left_eliminate_1.case_0
  pat_unapply h_v77 as ⟨v79, v80, x_v79, x_v80, h_v79, h_v80, hn_v79, hn_v80⟩ using hinv15 else hinv15 hG in EoCases.__eo_prog_bv_rotate_left_eliminate_1.case_0
  pat_unapply h_v79 as ⟨v82, v83, x_v82, x_v83, h_v82, h_v83, hn_v82, hn_v83⟩ using hinv15 else hinv15 hG in EoCases.__eo_prog_bv_rotate_left_eliminate_1.case_0
  step as ⟨e_v84, he_v84⟩
  store_step with CtorSpec.eo__3d.construct s15 e_v84 (by rw [he_v84]; exact empty_args) hinv15 h64 as ⟨v84, s16, hinv16, h_v84⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a8 h_v80 h_v82 h_v83 dropping h_a7 h_v59 h_v75 h_v77 h_v79 he_v84 hinv15 e_v84 s15 v59 v75 v77 v79
  pat_same v82 v84 with h_v82 h_v84 using hinv16 else hinv16 hG in EoCases.__eo_prog_bv_rotate_left_eliminate_1.case_0
  pat_same v83 a3 with h_v83 h_a3 using hinv16 else hinv16 hG in EoCases.__eo_prog_bv_rotate_left_eliminate_1.case_0
  pat_unapply h_v80 as ⟨v86, v87, x_v86, x_v87, h_v86, h_v87, hn_v86, hn_v87⟩ using hinv16 else hinv16 hG in EoCases.__eo_prog_bv_rotate_left_eliminate_1.case_0
  pat_unapply h_v86 as ⟨v89, v90, x_v89, x_v90, h_v89, h_v90, hn_v89, hn_v90⟩ using hinv16 else hinv16 hG in EoCases.__eo_prog_bv_rotate_left_eliminate_1.case_0
  step as ⟨e_v91, he_v91⟩
  store_step with CtorSpec.eo__2d.construct s16 e_v91 (by rw [he_v91]; exact empty_args) hinv16 h64 as ⟨v91, s17, hinv17, h_v91⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a8 h_v87 h_v89 h_v90 dropping h_v80 h_v82 h_v83 h_v84 h_v86 he_v91 hinv16 e_v91 s16 v80 v82 v83 v84 v86
  pat_same v89 v91 with h_v89 h_v91 using hinv17 else hinv17 hG in EoCases.__eo_prog_bv_rotate_left_eliminate_1.case_0
  pat_unapply h_v90 as ⟨v93, v94, x_v93, x_v94, h_v93, h_v94, hn_v93, hn_v94⟩ using hinv17 else hinv17 hG in EoCases.__eo_prog_bv_rotate_left_eliminate_1.case_0
  step as ⟨e_v95, he_v95⟩
  store_step with CtorSpec.eo__40bvsize.construct s17 e_v95 (by rw [he_v95]; exact empty_args) hinv17 h64 as ⟨v95, s18, hinv18, h_v95⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a8 h_v87 h_v93 h_v94 dropping h_v89 h_v90 h_v91 he_v95 hinv17 e_v95 s17 v89 v90 v91
  pat_same v93 v95 with h_v93 h_v95 using hinv18 else hinv18 hG in EoCases.__eo_prog_bv_rotate_left_eliminate_1.case_0
  pat_same v94 a0 with h_v94 h_a0 using hinv18 else hinv18 hG in EoCases.__eo_prog_bv_rotate_left_eliminate_1.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s18 1#u32 (1) (by scalar_tac) hinv18 h64 as ⟨v96, s19, hinv19, h_v96⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a8 h_v87 dropping h_v93 h_v94 h_v95 hinv18 s18 v93 v94 v95
  pat_same v87 v96 with h_v87 h_v96 using hinv19 else hinv19 hG in EoCases.__eo_prog_bv_rotate_left_eliminate_1.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a8 as ⟨v98, x_v98, h_v98⟩ else hinv19 hG in EoCases.__eo_prog_bv_rotate_left_eliminate_1.case_0
  pat_unapply h_v98 as ⟨v100, v101, x_v100, x_v101, h_v100, h_v101, hn_v100, hn_v101⟩ using hinv19 else hinv19 hG in EoCases.__eo_prog_bv_rotate_left_eliminate_1.case_0
  pat_unapply h_v100 as ⟨v103, v104, x_v103, x_v104, h_v103, h_v104, hn_v103, hn_v104⟩ using hinv19 else hinv19 hG in EoCases.__eo_prog_bv_rotate_left_eliminate_1.case_0
  step as ⟨e_v105, he_v105⟩
  store_step with CtorSpec.eo__3d.construct s19 e_v105 (by rw [he_v105]; exact empty_args) hinv19 h64 as ⟨v105, s20, hinv20, h_v105⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v101 h_v103 h_v104 dropping h_a8 h_v100 h_v87 h_v96 h_v98 he_v105 hinv19 e_v105 s19 v100 v87 v96 v98
  pat_same v103 v105 with h_v103 h_v105 using hinv20 else hinv20 hG in EoCases.__eo_prog_bv_rotate_left_eliminate_1.case_0
  pat_same v104 a4 with h_v104 h_a4 using hinv20 else hinv20 hG in EoCases.__eo_prog_bv_rotate_left_eliminate_1.case_0
  pat_unapply h_v101 as ⟨v107, v108, x_v107, x_v108, h_v107, h_v108, hn_v107, hn_v108⟩ using hinv20 else hinv20 hG in EoCases.__eo_prog_bv_rotate_left_eliminate_1.case_0
  pat_unapply h_v107 as ⟨v110, v111, x_v110, x_v111, h_v110, h_v111, hn_v110, hn_v111⟩ using hinv20 else hinv20 hG in EoCases.__eo_prog_bv_rotate_left_eliminate_1.case_0
  step as ⟨e_v112, he_v112⟩
  store_step with CtorSpec.eo__2d.construct s20 e_v112 (by rw [he_v112]; exact empty_args) hinv20 h64 as ⟨v112, s21, hinv21, h_v112⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v108 h_v110 h_v111 dropping h_v101 h_v103 h_v104 h_v105 h_v107 he_v112 hinv20 e_v112 s20 v101 v103 v104 v105 v107
  pat_same v110 v112 with h_v110 h_v112 using hinv21 else hinv21 hG in EoCases.__eo_prog_bv_rotate_left_eliminate_1.case_0
  pat_unapply h_v111 as ⟨v114, v115, x_v114, x_v115, h_v114, h_v115, hn_v114, hn_v115⟩ using hinv21 else hinv21 hG in EoCases.__eo_prog_bv_rotate_left_eliminate_1.case_0
  step as ⟨e_v116, he_v116⟩
  store_step with CtorSpec.eo__40bvsize.construct s21 e_v116 (by rw [he_v116]; exact empty_args) hinv21 h64 as ⟨v116, s22, hinv22, h_v116⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v108 h_v114 h_v115 dropping h_v110 h_v111 h_v112 he_v116 hinv21 e_v116 s21 v110 v111 v112
  pat_same v114 v116 with h_v114 h_v116 using hinv22 else hinv22 hG in EoCases.__eo_prog_bv_rotate_left_eliminate_1.case_0
  pat_same v115 a0 with h_v115 h_a0 using hinv22 else hinv22 hG in EoCases.__eo_prog_bv_rotate_left_eliminate_1.case_0
  pat_unapply h_v108 as ⟨v118, v119, x_v118, x_v119, h_v118, h_v119, hn_v118, hn_v119⟩ using hinv22 else hinv22 hG in EoCases.__eo_prog_bv_rotate_left_eliminate_1.case_0
  pat_unapply h_v118 as ⟨v121, v122, x_v121, x_v122, h_v121, h_v122, hn_v121, hn_v122⟩ using hinv22 else hinv22 hG in EoCases.__eo_prog_bv_rotate_left_eliminate_1.case_0
  step as ⟨e_v123, he_v123⟩
  store_step with CtorSpec.eo_mod.construct s22 e_v123 (by rw [he_v123]; exact empty_args) hinv22 h64 as ⟨v123, s23, hinv23, h_v123⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v119 h_v121 h_v122 dropping h_v108 h_v114 h_v115 h_v116 h_v118 he_v123 hinv22 e_v123 s22 v108 v114 v115 v116 v118
  pat_same v121 v123 with h_v121 h_v123 using hinv23 else hinv23 hG in EoCases.__eo_prog_bv_rotate_left_eliminate_1.case_0
  pat_same v122 a1 with h_v122 h_a1 using hinv23 else hinv23 hG in EoCases.__eo_prog_bv_rotate_left_eliminate_1.case_0
  pat_unapply h_v119 as ⟨v125, v126, x_v125, x_v126, h_v125, h_v126, hn_v125, hn_v126⟩ using hinv23 else hinv23 hG in EoCases.__eo_prog_bv_rotate_left_eliminate_1.case_0
  step as ⟨e_v127, he_v127⟩
  store_step with CtorSpec.eo__40bvsize.construct s23 e_v127 (by rw [he_v127]; exact empty_args) hinv23 h64 as ⟨v127, s24, hinv24, h_v127⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v125 h_v126 dropping h_v119 h_v121 h_v122 h_v123 he_v127 hinv23 e_v127 s23 v119 v121 v122 v123
  pat_same v125 v127 with h_v125 h_v127 using hinv24 else hinv24 hG in EoCases.__eo_prog_bv_rotate_left_eliminate_1.case_0
  pat_same v126 a0 with h_v126 h_a0 using hinv24 else hinv24 hG in EoCases.__eo_prog_bv_rotate_left_eliminate_1.case_0
  step as ⟨e_v128, he_v128⟩
  store_step with CtorSpec.eo__3d.construct s24 e_v128 (by rw [he_v128]; exact empty_args) hinv24 h64 as ⟨v128, s25, hinv25, h_v128⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 dropping h_v125 h_v126 h_v127 he_v128 hinv24 e_v128 s24 v125 v126 v127
  step as ⟨e_v129, he_v129⟩
  store_step with CtorSpec.eo_rotate_5fleft.construct s25 e_v129 (by rw [he_v129]; rfl) h_a1 hinv25 h64 as ⟨v129, s26, hinv26, h_v129⟩ growing hG carrying h_a0 h_a2 h_a3 h_a4 h_v128 dropping h_a1 he_v129 hinv25 e_v129 s25
  store_step with Store.apply_rep s26 v129 a0 _ _ hinv26 h64 h_v129 h_a0 (by ns_tac) (by ns_tac) as ⟨v130, s27, hinv27, h_v130⟩ growing hG carrying h_a0 h_a2 h_a3 h_a4 h_v128 dropping h_v129 hinv26 s26 v129
  store_step with Store.apply_rep s27 v128 v130 _ _ hinv27 h64 h_v128 h_v130 (by ns_tac) (by ns_tac) as ⟨v131, s28, hinv28, h_v131⟩ growing hG carrying h_a0 h_a2 h_a3 h_a4 dropping h_v128 h_v130 hinv27 s27 v128 v130
  step as ⟨e_v132, he_v132⟩
  store_step with CtorSpec.eo_concat.construct s28 e_v132 (by rw [he_v132]; exact empty_args) hinv28 h64 as ⟨v132, s29, hinv29, h_v132⟩ growing hG carrying h_a0 h_a2 h_a3 h_a4 h_v131 dropping he_v132 hinv28 e_v132 s28
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s29 0#u32 (0) (by scalar_tac) hinv29 h64 as ⟨v133, s30, hinv30, h_v133⟩ growing hG carrying h_a0 h_a2 h_a3 h_a4 h_v131 h_v132 dropping hinv29 s29
  step as ⟨e_v134, he_v134⟩
  store_step with CtorSpec.eo_extract.construct s30 e_v134 (by rw [he_v134]; rfl) h_a2 h_v133 hinv30 h64 as ⟨v134, s31, hinv31, h_v134⟩ growing hG carrying h_a0 h_a3 h_a4 h_v131 h_v132 dropping h_a2 h_v133 he_v134 hinv30 e_v134 s30 v133
  store_step with Store.apply_rep s31 v134 a0 _ _ hinv31 h64 h_v134 h_a0 (by ns_tac) (by ns_tac) as ⟨v135, s32, hinv32, h_v135⟩ growing hG carrying h_a0 h_a3 h_a4 h_v131 h_v132 dropping h_v134 hinv31 s31 v134
  store_step with Store.apply_rep s32 v132 v135 _ _ hinv32 h64 h_v132 h_v135 (by ns_tac) (by ns_tac) as ⟨v136, s33, hinv33, h_v136⟩ growing hG carrying h_a0 h_a3 h_a4 h_v131 dropping h_v132 h_v135 hinv32 s32 v132 v135
  step as ⟨e_v137, he_v137⟩
  store_step with CtorSpec.eo_concat.construct s33 e_v137 (by rw [he_v137]; exact empty_args) hinv33 h64 as ⟨v137, s34, hinv34, h_v137⟩ growing hG carrying h_a0 h_a3 h_a4 h_v131 h_v136 dropping he_v137 hinv33 e_v137 s33
  step as ⟨e_v138, he_v138⟩
  store_step with CtorSpec.eo_extract.construct s34 e_v138 (by rw [he_v138]; rfl) h_a3 h_a4 hinv34 h64 as ⟨v138, s35, hinv35, h_v138⟩ growing hG carrying h_a0 h_v131 h_v136 h_v137 dropping h_a3 h_a4 he_v138 hinv34 e_v138 s34
  store_step with Store.apply_rep s35 v138 a0 _ _ hinv35 h64 h_v138 h_a0 (by ns_tac) (by ns_tac) as ⟨v139, s36, hinv36, h_v139⟩ growing hG carrying h_v131 h_v136 h_v137 dropping h_a0 h_v138 hinv35 s35 v138
  store_step with Store.apply_rep s36 v137 v139 _ _ hinv36 h64 h_v137 h_v139 (by ns_tac) (by ns_tac) as ⟨v140, s37, hinv37, h_v140⟩ growing hG carrying h_v131 h_v136 dropping h_v137 h_v139 hinv36 s36 v137 v139
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s37 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv37 h64 as ⟨v141, s38, hinv38, h_v141⟩ growing hG carrying h_v131 h_v136 h_v140 dropping hinv37 s37
  store_step with Store.apply_rep s38 v140 v141 _ _ hinv38 h64 h_v140 h_v141 (by ns_tac) (by ns_tac) as ⟨v142, s39, hinv39, h_v142⟩ growing hG carrying h_v131 h_v136 dropping h_v140 h_v141 hinv38 s38 v140 v141
  store_step with Store.apply_rep s39 v136 v142 _ _ hinv39 h64 h_v136 h_v142 (by ns_tac) (by ns_tac) as ⟨v143, s40, hinv40, h_v143⟩ growing hG carrying h_v131 dropping h_v136 h_v142 hinv39 s39 v136 v142
  store_step with Store.apply_rep s40 v131 v143 _ _ hinv40 h64 h_v131 h_v143 (by ns_tac) (by ns_tac) as ⟨v144, s41, hinv41, h_v144⟩ growing hG carrying dropping h_v131 h_v143 hinv40 s40 v131 v143
  case_done hinv41 hG with h_v144 in EoCases.__eo_prog_bv_rotate_left_eliminate_1.case_0 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v13 hn_v14 hn_v17 hn_v18 hn_v20 hn_v21 hn_v24 hn_v25 hn_v32 hn_v33 hn_v35 hn_v36 hn_v39 hn_v40 hn_v42 hn_v43 hn_v46 hn_v47 hn_v50 hn_v51 hn_v53 hn_v54 hn_v58 hn_v59 hn_v61 hn_v62 hn_v65 hn_v66 hn_v68 hn_v69 hn_v72 hn_v73 hn_v79 hn_v80 hn_v82 hn_v83 hn_v86 hn_v87 hn_v89 hn_v90 hn_v93 hn_v94 hn_v100 hn_v101 hn_v103 hn_v104 hn_v107 hn_v108 hn_v110 hn_v111 hn_v114 hn_v115 hn_v118 hn_v119 hn_v121 hn_v122 hn_v125 hn_v126

/-- logos's `__eo_prog_bv_rotate_left_eliminate_1` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fbv_2drotate_2dleft_2deliminate_2d1.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _) (x_a7 : _) (x_a8 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) (hw_a4 : Valid.valid x_a4) (hw_a5 : Valid.valid x_a5) (hw_a6 : Valid.valid x_a6) (hw_a7 : Valid.valid x_a7) (hw_a8 : Valid.valid x_a8) :
    __eo_prog_bv_rotate_left_eliminate_1 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else if x_a4 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_bv_rotate_left_eliminate_1.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_bv_rotate_left_eliminate_1
  unfold EoCases.__eo_prog_bv_rotate_left_eliminate_1.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fbv_2drotate_2dleft_2deliminate_2d1_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 a6 a7 a8 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _) (x_a7 : _) (x_a8 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) (h_a6 : Represents.rep s a6 x_a6) (h_a7 : Represents.rep s a7 x_a7) (h_a8 : Represents.rep s a8 x_a8) :
    body_eo__24eo_5fprog_5fbv_2drotate_2dleft_2deliminate_2d1 s a0 a1 a2 a3 a4 a5 a6 a7 a8 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_rotate_left_eliminate_1 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fbv_2drotate_2dleft_2deliminate_2d1.rust_eq x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3) (by valid_tac hinv h_a4) (by valid_tac hinv h_a5) (by valid_tac hinv h_a6) (by valid_tac hinv h_a7) (by valid_tac hinv h_a8)]
  unfold body_eo__24eo_5fprog_5fbv_2drotate_2dleft_2deliminate_2d1
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  stuck_check h_a3 : x_a3 as hn_a3 else hinv hG
  stuck_check h_a4 : x_a4 as hn_a4 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fbv_2drotate_2dleft_2deliminate_2d1_spec n ih s a0 a1 a2 a3 a4 a5 a6 a7 a8 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 hn_a0 hn_a1 hn_a2 hn_a3 hn_a4
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hc0 in EoCases.__eo_prog_bv_rotate_left_eliminate_1.case_0

theorem eo__24eo_5fprog_5fbv_2drotate_2dleft_2deliminate_2d1_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fbv_2drotate_2dleft_2deliminate_2d1.Spec n := by
  intro s a0 a1 a2 a3 a4 a5 a6 a7 a8 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8
  unfold eo__24eo_5fprog_5fbv_2drotate_2dleft_2deliminate_2d1
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fbv_2drotate_2dleft_2deliminate_2d1 s1 a0 a1 a2 a3 a4 a5 a6 a7 a8) (fun s' t => Represents.rep s' t (__eo_prog_bv_rotate_left_eliminate_1 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fbv_2drotate_2dleft_2deliminate_2d1_spec m (ih m hm) s1 a0 a1 a2 a3 a4 a5 a6 a7 a8 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn) (by congr_one h_a4 hn) (by congr_one h_a5 hn) (by congr_one h_a6 hn) (by congr_one h_a7 hn) (by congr_one h_a8 hn)))
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
  unfold case_0_eo__24eo_5fprog_5fbv_2drotate_2dleft_2deliminate_2d2
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a2 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_bv_rotate_left_eliminate_2.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_rotate_left_eliminate_2.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_rotate_left_eliminate_2.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_v4 h_v6 h_v7 dropping h_a2 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_rotate_left_eliminate_2.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_rotate_left_eliminate_2.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_rotate_left_eliminate_2.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo_mod.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_a1 h_v4 h_v11 h_v13 h_v14 dropping h_v10 h_v6 h_v7 h_v8 he_v15 hinv1 e_v15 s1 v10 v6 v7 v8
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_rotate_left_eliminate_2.case_0
  pat_same v14 a1 with h_v14 h_a1 using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_rotate_left_eliminate_2.case_0
  pat_unapply h_v11 as ⟨v17, v18, x_v17, x_v18, h_v17, h_v18, hn_v17, hn_v18⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_rotate_left_eliminate_2.case_0
  step as ⟨e_v19, he_v19⟩
  store_step with CtorSpec.eo__40bvsize.construct s2 e_v19 (by rw [he_v19]; exact empty_args) hinv2 h64 as ⟨v19, s3, hinv3, h_v19⟩ growing hG carrying h_a0 h_a1 h_v4 h_v17 h_v18 dropping h_v11 h_v13 h_v14 h_v15 he_v19 hinv2 e_v19 s2 v11 v13 v14 v15
  pat_same v17 v19 with h_v17 h_v19 using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_rotate_left_eliminate_2.case_0
  pat_same v18 a0 with h_v18 h_a0 using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_rotate_left_eliminate_2.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s3 0#u32 (0) (by scalar_tac) hinv3 h64 as ⟨v20, s4, hinv4, h_v20⟩ growing hG carrying h_a0 h_a1 h_v4 dropping h_v17 h_v18 h_v19 hinv3 s3 v17 v18 v19
  pat_same v4 v20 with h_v4 h_v20 using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_rotate_left_eliminate_2.case_0
  step as ⟨e_v21, he_v21⟩
  store_step with CtorSpec.eo__3d.construct s4 e_v21 (by rw [he_v21]; exact empty_args) hinv4 h64 as ⟨v21, s5, hinv5, h_v21⟩ growing hG carrying h_a0 h_a1 dropping h_v20 h_v4 he_v21 hinv4 e_v21 s4 v20 v4
  step as ⟨e_v22, he_v22⟩
  store_step with CtorSpec.eo_rotate_5fleft.construct s5 e_v22 (by rw [he_v22]; rfl) h_a1 hinv5 h64 as ⟨v22, s6, hinv6, h_v22⟩ growing hG carrying h_a0 h_v21 dropping h_a1 he_v22 hinv5 e_v22 s5
  store_step with Store.apply_rep s6 v22 a0 _ _ hinv6 h64 h_v22 h_a0 (by ns_tac) (by ns_tac) as ⟨v23, s7, hinv7, h_v23⟩ growing hG carrying h_a0 h_v21 dropping h_v22 hinv6 s6 v22
  store_step with Store.apply_rep s7 v21 v23 _ _ hinv7 h64 h_v21 h_v23 (by ns_tac) (by ns_tac) as ⟨v24, s8, hinv8, h_v24⟩ growing hG carrying h_a0 dropping h_v21 h_v23 hinv7 s7 v21 v23
  store_step with Store.apply_rep s8 v24 a0 _ _ hinv8 h64 h_v24 h_a0 (by ns_tac) (by ns_tac) as ⟨v25, s9, hinv9, h_v25⟩ growing hG carrying dropping h_a0 h_v24 hinv8 s8 v24
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
  unfold case_0_eo__24eo_5fprog_5fbv_2drotate_2dright_2deliminate_2d2
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a2 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_bv_rotate_right_eliminate_2.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_rotate_right_eliminate_2.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_rotate_right_eliminate_2.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_v4 h_v6 h_v7 dropping h_a2 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_rotate_right_eliminate_2.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_rotate_right_eliminate_2.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_rotate_right_eliminate_2.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo_mod.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_a1 h_v4 h_v11 h_v13 h_v14 dropping h_v10 h_v6 h_v7 h_v8 he_v15 hinv1 e_v15 s1 v10 v6 v7 v8
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_rotate_right_eliminate_2.case_0
  pat_same v14 a1 with h_v14 h_a1 using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_rotate_right_eliminate_2.case_0
  pat_unapply h_v11 as ⟨v17, v18, x_v17, x_v18, h_v17, h_v18, hn_v17, hn_v18⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_rotate_right_eliminate_2.case_0
  step as ⟨e_v19, he_v19⟩
  store_step with CtorSpec.eo__40bvsize.construct s2 e_v19 (by rw [he_v19]; exact empty_args) hinv2 h64 as ⟨v19, s3, hinv3, h_v19⟩ growing hG carrying h_a0 h_a1 h_v4 h_v17 h_v18 dropping h_v11 h_v13 h_v14 h_v15 he_v19 hinv2 e_v19 s2 v11 v13 v14 v15
  pat_same v17 v19 with h_v17 h_v19 using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_rotate_right_eliminate_2.case_0
  pat_same v18 a0 with h_v18 h_a0 using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_rotate_right_eliminate_2.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s3 0#u32 (0) (by scalar_tac) hinv3 h64 as ⟨v20, s4, hinv4, h_v20⟩ growing hG carrying h_a0 h_a1 h_v4 dropping h_v17 h_v18 h_v19 hinv3 s3 v17 v18 v19
  pat_same v4 v20 with h_v4 h_v20 using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_rotate_right_eliminate_2.case_0
  step as ⟨e_v21, he_v21⟩
  store_step with CtorSpec.eo__3d.construct s4 e_v21 (by rw [he_v21]; exact empty_args) hinv4 h64 as ⟨v21, s5, hinv5, h_v21⟩ growing hG carrying h_a0 h_a1 dropping h_v20 h_v4 he_v21 hinv4 e_v21 s4 v20 v4
  step as ⟨e_v22, he_v22⟩
  store_step with CtorSpec.eo_rotate_5fright.construct s5 e_v22 (by rw [he_v22]; rfl) h_a1 hinv5 h64 as ⟨v22, s6, hinv6, h_v22⟩ growing hG carrying h_a0 h_v21 dropping h_a1 he_v22 hinv5 e_v22 s5
  store_step with Store.apply_rep s6 v22 a0 _ _ hinv6 h64 h_v22 h_a0 (by ns_tac) (by ns_tac) as ⟨v23, s7, hinv7, h_v23⟩ growing hG carrying h_a0 h_v21 dropping h_v22 hinv6 s6 v22
  store_step with Store.apply_rep s7 v21 v23 _ _ hinv7 h64 h_v21 h_v23 (by ns_tac) (by ns_tac) as ⟨v24, s8, hinv8, h_v24⟩ growing hG carrying h_a0 dropping h_v21 h_v23 hinv7 s7 v21 v23
  store_step with Store.apply_rep s8 v24 a0 _ _ hinv8 h64 h_v24 h_a0 (by ns_tac) (by ns_tac) as ⟨v25, s9, hinv9, h_v25⟩ growing hG carrying dropping h_a0 h_v24 hinv8 s8 v24
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
  unfold case_0_eo__24eo_5fprog_5fbv_2dsdivo_2deliminate
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a4 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_bv_sdivo_eliminate.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_sdivo_eliminate.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_sdivo_eliminate.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a5 h_v4 h_v6 h_v7 dropping h_a4 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_sdivo_eliminate.case_0
  pat_same v7 a3 with h_v7 h_a3 using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_sdivo_eliminate.case_0
  pat_unapply h_v4 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_sdivo_eliminate.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_sdivo_eliminate.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__2d.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a5 h_v11 h_v13 h_v14 dropping h_v10 h_v4 h_v6 h_v7 h_v8 he_v15 hinv1 e_v15 s1 v10 v4 v6 v7 v8
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_sdivo_eliminate.case_0
  pat_unapply h_v14 as ⟨v17, v18, x_v17, x_v18, h_v17, h_v18, hn_v17, hn_v18⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_sdivo_eliminate.case_0
  step as ⟨e_v19, he_v19⟩
  store_step with CtorSpec.eo__40bvsize.construct s2 e_v19 (by rw [he_v19]; exact empty_args) hinv2 h64 as ⟨v19, s3, hinv3, h_v19⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a5 h_v11 h_v17 h_v18 dropping h_v13 h_v14 h_v15 he_v19 hinv2 e_v19 s2 v13 v14 v15
  pat_same v17 v19 with h_v17 h_v19 using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_sdivo_eliminate.case_0
  pat_same v18 a0 with h_v18 h_a0 using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_sdivo_eliminate.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s3 1#u32 (1) (by scalar_tac) hinv3 h64 as ⟨v20, s4, hinv4, h_v20⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a5 h_v11 dropping h_v17 h_v18 h_v19 hinv3 s3 v17 v18 v19
  pat_same v11 v20 with h_v11 h_v20 using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_sdivo_eliminate.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a5 as ⟨v22, x_v22, h_v22⟩ else hinv4 hG in EoCases.__eo_prog_bv_sdivo_eliminate.case_0
  pat_unapply h_v22 as ⟨v24, v25, x_v24, x_v25, h_v24, h_v25, hn_v24, hn_v25⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_sdivo_eliminate.case_0
  pat_unapply h_v24 as ⟨v27, v28, x_v27, x_v28, h_v27, h_v28, hn_v27, hn_v28⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_sdivo_eliminate.case_0
  step as ⟨e_v29, he_v29⟩
  store_step with CtorSpec.eo__3d.construct s4 e_v29 (by rw [he_v29]; exact empty_args) hinv4 h64 as ⟨v29, s5, hinv5, h_v29⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v25 h_v27 h_v28 dropping h_a5 h_v11 h_v20 h_v22 h_v24 he_v29 hinv4 e_v29 s4 v11 v20 v22 v24
  pat_same v27 v29 with h_v27 h_v29 using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_sdivo_eliminate.case_0
  pat_same v28 a2 with h_v28 h_a2 using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_sdivo_eliminate.case_0
  pat_unapply h_v25 as ⟨v31, v32, x_v31, x_v32, h_v31, h_v32, hn_v31, hn_v32⟩ using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_sdivo_eliminate.case_0
  step as ⟨e_v33, he_v33⟩
  store_step with CtorSpec.eo__40bvsize.construct s5 e_v33 (by rw [he_v33]; exact empty_args) hinv5 h64 as ⟨v33, s6, hinv6, h_v33⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v31 h_v32 dropping h_v25 h_v27 h_v28 h_v29 he_v33 hinv5 e_v33 s5 v25 v27 v28 v29
  pat_same v31 v33 with h_v31 h_v33 using hinv6 else hinv6 hG in EoCases.__eo_prog_bv_sdivo_eliminate.case_0
  pat_same v32 a1 with h_v32 h_a1 using hinv6 else hinv6 hG in EoCases.__eo_prog_bv_sdivo_eliminate.case_0
  step as ⟨e_v34, he_v34⟩
  store_step with CtorSpec.eo__3d.construct s6 e_v34 (by rw [he_v34]; exact empty_args) hinv6 h64 as ⟨v34, s7, hinv7, h_v34⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 dropping h_v31 h_v32 h_v33 he_v34 hinv6 e_v34 s6 v31 v32 v33
  step as ⟨e_v35, he_v35⟩
  store_step with CtorSpec.eo_bvsdivo.construct s7 e_v35 (by rw [he_v35]; exact empty_args) hinv7 h64 as ⟨v35, s8, hinv8, h_v35⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v34 dropping he_v35 hinv7 e_v35 s7
  store_step with Store.apply_rep s8 v35 a0 _ _ hinv8 h64 h_v35 h_a0 (by ns_tac) (by ns_tac) as ⟨v36, s9, hinv9, h_v36⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v34 dropping h_v35 hinv8 s8 v35
  store_step with Store.apply_rep s9 v36 a1 _ _ hinv9 h64 h_v36 h_a1 (by ns_tac) (by ns_tac) as ⟨v37, s10, hinv10, h_v37⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v34 dropping h_v36 hinv9 s9 v36
  store_step with Store.apply_rep s10 v34 v37 _ _ hinv10 h64 h_v34 h_v37 (by ns_tac) (by ns_tac) as ⟨v38, s11, hinv11, h_v38⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 dropping h_v34 h_v37 hinv10 s10 v34 v37
  step as ⟨e_v39, he_v39⟩
  store_step with CtorSpec.eo_and.construct s11 e_v39 (by rw [he_v39]; exact empty_args) hinv11 h64 as ⟨v39, s12, hinv12, h_v39⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v38 dropping he_v39 hinv11 e_v39 s11
  step as ⟨e_v40, he_v40⟩
  store_step with CtorSpec.eo__3d.construct s12 e_v40 (by rw [he_v40]; exact empty_args) hinv12 h64 as ⟨v40, s13, hinv13, h_v40⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v38 h_v39 dropping he_v40 hinv12 e_v40 s12
  store_step with Store.apply_rep s13 v40 a0 _ _ hinv13 h64 h_v40 h_a0 (by ns_tac) (by ns_tac) as ⟨v41, s14, hinv14, h_v41⟩ growing hG carrying h_a1 h_a2 h_a3 h_v38 h_v39 dropping h_a0 h_v40 hinv13 s13 v40
  step as ⟨e_v42, he_v42⟩
  store_step with CtorSpec.eo_concat.construct s14 e_v42 (by rw [he_v42]; exact empty_args) hinv14 h64 as ⟨v42, s15, hinv15, h_v42⟩ growing hG carrying h_a1 h_a2 h_a3 h_v38 h_v39 h_v41 dropping he_v42 hinv14 e_v42 s14
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s15 1#u32 (1) (by scalar_tac) hinv15 h64 as ⟨v43, s16, hinv16, h_v43⟩ growing hG carrying h_a1 h_a2 h_a3 h_v38 h_v39 h_v41 h_v42 dropping hinv15 s15
  step as ⟨e_v44, he_v44⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s16 e_v44 (by rw [he_v44]; rfl) h_v43 hinv16 h64 as ⟨v44, s17, hinv17, h_v44⟩ growing hG carrying h_a1 h_a2 h_a3 h_v38 h_v39 h_v41 h_v42 dropping h_v43 he_v44 hinv16 e_v44 s16 v43
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s17 1#u32 (1) (by scalar_tac) hinv17 h64 as ⟨v45, s18, hinv18, h_v45⟩ growing hG carrying h_a1 h_a2 h_a3 h_v38 h_v39 h_v41 h_v42 h_v44 dropping hinv17 s17
  store_step with Store.apply_rep s18 v44 v45 _ _ hinv18 h64 h_v44 h_v45 (by ns_tac) (by ns_tac) as ⟨v46, s19, hinv19, h_v46⟩ growing hG carrying h_a1 h_a2 h_a3 h_v38 h_v39 h_v41 h_v42 dropping h_v44 h_v45 hinv18 s18 v44 v45
  store_step with Store.apply_rep s19 v42 v46 _ _ hinv19 h64 h_v42 h_v46 (by ns_tac) (by ns_tac) as ⟨v47, s20, hinv20, h_v47⟩ growing hG carrying h_a1 h_a2 h_a3 h_v38 h_v39 h_v41 dropping h_v42 h_v46 hinv19 s19 v42 v46
  step as ⟨e_v48, he_v48⟩
  store_step with CtorSpec.eo_concat.construct s20 e_v48 (by rw [he_v48]; exact empty_args) hinv20 h64 as ⟨v48, s21, hinv21, h_v48⟩ growing hG carrying h_a1 h_a2 h_a3 h_v38 h_v39 h_v41 h_v47 dropping he_v48 hinv20 e_v48 s20
  step as ⟨e_v49, he_v49⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s21 e_v49 (by rw [he_v49]; rfl) h_a3 hinv21 h64 as ⟨v49, s22, hinv22, h_v49⟩ growing hG carrying h_a1 h_a2 h_v38 h_v39 h_v41 h_v47 h_v48 dropping h_a3 he_v49 hinv21 e_v49 s21
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s22 0#u32 (0) (by scalar_tac) hinv22 h64 as ⟨v50, s23, hinv23, h_v50⟩ growing hG carrying h_a1 h_a2 h_v38 h_v39 h_v41 h_v47 h_v48 h_v49 dropping hinv22 s22
  store_step with Store.apply_rep s23 v49 v50 _ _ hinv23 h64 h_v49 h_v50 (by ns_tac) (by ns_tac) as ⟨v51, s24, hinv24, h_v51⟩ growing hG carrying h_a1 h_a2 h_v38 h_v39 h_v41 h_v47 h_v48 dropping h_v49 h_v50 hinv23 s23 v49 v50
  store_step with Store.apply_rep s24 v48 v51 _ _ hinv24 h64 h_v48 h_v51 (by ns_tac) (by ns_tac) as ⟨v52, s25, hinv25, h_v52⟩ growing hG carrying h_a1 h_a2 h_v38 h_v39 h_v41 h_v47 dropping h_v48 h_v51 hinv24 s24 v48 v51
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s25 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv25 h64 as ⟨v53, s26, hinv26, h_v53⟩ growing hG carrying h_a1 h_a2 h_v38 h_v39 h_v41 h_v47 h_v52 dropping hinv25 s25
  store_step with Store.apply_rep s26 v52 v53 _ _ hinv26 h64 h_v52 h_v53 (by ns_tac) (by ns_tac) as ⟨v54, s27, hinv27, h_v54⟩ growing hG carrying h_a1 h_a2 h_v38 h_v39 h_v41 h_v47 dropping h_v52 h_v53 hinv26 s26 v52 v53
  store_step with Store.apply_rep s27 v47 v54 _ _ hinv27 h64 h_v47 h_v54 (by ns_tac) (by ns_tac) as ⟨v55, s28, hinv28, h_v55⟩ growing hG carrying h_a1 h_a2 h_v38 h_v39 h_v41 dropping h_v47 h_v54 hinv27 s27 v47 v54
  store_step with Store.apply_rep s28 v41 v55 _ _ hinv28 h64 h_v41 h_v55 (by ns_tac) (by ns_tac) as ⟨v56, s29, hinv29, h_v56⟩ growing hG carrying h_a1 h_a2 h_v38 h_v39 dropping h_v41 h_v55 hinv28 s28 v41 v55
  store_step with Store.apply_rep s29 v39 v56 _ _ hinv29 h64 h_v39 h_v56 (by ns_tac) (by ns_tac) as ⟨v57, s30, hinv30, h_v57⟩ growing hG carrying h_a1 h_a2 h_v38 dropping h_v39 h_v56 hinv29 s29 v39 v56
  step as ⟨e_v58, he_v58⟩
  store_step with CtorSpec.eo_and.construct s30 e_v58 (by rw [he_v58]; exact empty_args) hinv30 h64 as ⟨v58, s31, hinv31, h_v58⟩ growing hG carrying h_a1 h_a2 h_v38 h_v57 dropping he_v58 hinv30 e_v58 s30
  step as ⟨e_v59, he_v59⟩
  store_step with CtorSpec.eo__3d.construct s31 e_v59 (by rw [he_v59]; exact empty_args) hinv31 h64 as ⟨v59, s32, hinv32, h_v59⟩ growing hG carrying h_a1 h_a2 h_v38 h_v57 h_v58 dropping he_v59 hinv31 e_v59 s31
  store_step with Store.apply_rep s32 v59 a1 _ _ hinv32 h64 h_v59 h_a1 (by ns_tac) (by ns_tac) as ⟨v60, s33, hinv33, h_v60⟩ growing hG carrying h_a2 h_v38 h_v57 h_v58 dropping h_a1 h_v59 hinv32 s32 v59
  step as ⟨e_v61, he_v61⟩
  store_step with CtorSpec.eo_bvnot.construct s33 e_v61 (by rw [he_v61]; exact empty_args) hinv33 h64 as ⟨v61, s34, hinv34, h_v61⟩ growing hG carrying h_a2 h_v38 h_v57 h_v58 h_v60 dropping he_v61 hinv33 e_v61 s33
  step as ⟨e_v62, he_v62⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s34 e_v62 (by rw [he_v62]; rfl) h_a2 hinv34 h64 as ⟨v62, s35, hinv35, h_v62⟩ growing hG carrying h_v38 h_v57 h_v58 h_v60 h_v61 dropping h_a2 he_v62 hinv34 e_v62 s34
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s35 0#u32 (0) (by scalar_tac) hinv35 h64 as ⟨v63, s36, hinv36, h_v63⟩ growing hG carrying h_v38 h_v57 h_v58 h_v60 h_v61 h_v62 dropping hinv35 s35
  store_step with Store.apply_rep s36 v62 v63 _ _ hinv36 h64 h_v62 h_v63 (by ns_tac) (by ns_tac) as ⟨v64, s37, hinv37, h_v64⟩ growing hG carrying h_v38 h_v57 h_v58 h_v60 h_v61 dropping h_v62 h_v63 hinv36 s36 v62 v63
  store_step with Store.apply_rep s37 v61 v64 _ _ hinv37 h64 h_v61 h_v64 (by ns_tac) (by ns_tac) as ⟨v65, s38, hinv38, h_v65⟩ growing hG carrying h_v38 h_v57 h_v58 h_v60 dropping h_v61 h_v64 hinv37 s37 v61 v64
  store_step with Store.apply_rep s38 v60 v65 _ _ hinv38 h64 h_v60 h_v65 (by ns_tac) (by ns_tac) as ⟨v66, s39, hinv39, h_v66⟩ growing hG carrying h_v38 h_v57 h_v58 dropping h_v60 h_v65 hinv38 s38 v60 v65
  store_step with Store.apply_rep s39 v58 v66 _ _ hinv39 h64 h_v58 h_v66 (by ns_tac) (by ns_tac) as ⟨v67, s40, hinv40, h_v67⟩ growing hG carrying h_v38 h_v57 dropping h_v58 h_v66 hinv39 s39 v58 v66
  store_step with Store.literal_boolean_spec s40 true hinv40 h64 as ⟨v68, s41, hinv41, h_v68⟩ growing hG carrying h_v38 h_v57 h_v67 dropping hinv40 s40
  store_step with Store.apply_rep s41 v67 v68 _ _ hinv41 h64 h_v67 h_v68 (by ns_tac) (by ns_tac) as ⟨v69, s42, hinv42, h_v69⟩ growing hG carrying h_v38 h_v57 dropping h_v67 h_v68 hinv41 s41 v67 v68
  store_step with Store.apply_rep s42 v57 v69 _ _ hinv42 h64 h_v57 h_v69 (by ns_tac) (by ns_tac) as ⟨v70, s43, hinv43, h_v70⟩ growing hG carrying h_v38 dropping h_v57 h_v69 hinv42 s42 v57 v69
  store_step with Store.apply_rep s43 v38 v70 _ _ hinv43 h64 h_v38 h_v70 (by ns_tac) (by ns_tac) as ⟨v71, s44, hinv44, h_v71⟩ growing hG carrying dropping h_v38 h_v70 hinv43 s43 v38 v70
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
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 dropping he_v0 e_v0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_bvsge.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0 dropping he_v1 hinv1 e_v1 s1
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 dropping h_v1 hinv2 s2 v1
  store_step with Store.apply_rep s3 v2 a1 _ _ hinv3 h64 h_v2 h_a1 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_v0 dropping h_v2 hinv3 s3 v2
  store_step with Store.apply_rep s4 v0 v3 _ _ hinv4 h64 h_v0 h_v3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 dropping h_v0 h_v3 hinv4 s4 v0 v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo_bvsle.construct s5 e_v5 (by rw [he_v5]; exact empty_args) hinv5 h64 as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_v4 dropping he_v5 hinv5 e_v5 s5
  store_step with Store.apply_rep s6 v5 a1 _ _ hinv6 h64 h_v5 h_a1 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_v4 dropping h_a1 h_v5 hinv6 s6 v5
  store_step with Store.apply_rep s7 v6 a0 _ _ hinv7 h64 h_v6 h_a0 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_v4 dropping h_a0 h_v6 hinv7 s7 v6
  store_step with Store.apply_rep s8 v4 v7 _ _ hinv8 h64 h_v4 h_v7 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying dropping h_v4 h_v7 hinv8 s8 v4 v7
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
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 dropping he_v0 e_v0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_bvsgt.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0 dropping he_v1 hinv1 e_v1 s1
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 dropping h_v1 hinv2 s2 v1
  store_step with Store.apply_rep s3 v2 a1 _ _ hinv3 h64 h_v2 h_a1 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_v0 dropping h_v2 hinv3 s3 v2
  store_step with Store.apply_rep s4 v0 v3 _ _ hinv4 h64 h_v0 h_v3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 dropping h_v0 h_v3 hinv4 s4 v0 v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo_bvslt.construct s5 e_v5 (by rw [he_v5]; exact empty_args) hinv5 h64 as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_v4 dropping he_v5 hinv5 e_v5 s5
  store_step with Store.apply_rep s6 v5 a1 _ _ hinv6 h64 h_v5 h_a1 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_v4 dropping h_a1 h_v5 hinv6 s6 v5
  store_step with Store.apply_rep s7 v6 a0 _ _ hinv7 h64 h_v6 h_a0 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_v4 dropping h_a0 h_v6 hinv7 s7 v6
  store_step with Store.apply_rep s8 v4 v7 _ _ hinv8 h64 h_v4 h_v7 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying dropping h_v4 h_v7 hinv8 s8 v4 v7
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

end pathos_compiled_checker
