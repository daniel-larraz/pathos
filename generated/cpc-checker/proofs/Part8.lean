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

set_option maxHeartbeats 2610000 in
theorem case_0_eo__24eo_5fprog_5fbv_2dmult_2dslt_2dmult_2d1_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _) (x_a7 : _) (x_a8 : _) (x_a9 : _) (x_a10 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) (h_a6 : Represents.rep s a6 x_a6) (h_a7 : Represents.rep s a7 x_a7) (h_a8 : Represents.rep s a8 x_a8) (h_a9 : Represents.rep s a9 x_a9) (h_a10 : Represents.rep s a10 x_a10) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) (hn_a4 : x_a4 ≠ Eo.Term.Stuck) (hn_a5 : x_a5 ≠ Eo.Term.Stuck) (hn_a6 : x_a6 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fbv_2dmult_2dslt_2dmult_2d1 s a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_bv_mult_slt_mult_1.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 x_a9 x_a10 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_bv_mult_slt_mult_1.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 x_a9 x_a10 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fbv_2dmult_2dslt_2dmult_2d1
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a7 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_bv_mult_slt_mult_1.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_mult_slt_mult_1.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_mult_slt_mult_1.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a8 h_a9 h_a10 h_v4 h_v6 h_v7 dropping h_a7 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_mult_slt_mult_1.case_0
  pat_same v7 a5 with h_v7 h_a5 using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_mult_slt_mult_1.case_0
  pat_unapply h_v4 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_mult_slt_mult_1.case_0
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo__40bvsize.construct s1 e_v12 (by rw [he_v12]; exact empty_args) hinv1 h64 as ⟨v12, s2, hinv2, h_v12⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a8 h_a9 h_a10 h_v10 h_v11 dropping h_v4 h_v6 h_v7 h_v8 he_v12 hinv1 e_v12 s1 v4 v6 v7 v8
  pat_same v10 v12 with h_v10 h_v12 using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_mult_slt_mult_1.case_0
  pat_same v11 a0 with h_v11 h_a0 using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_mult_slt_mult_1.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a8 as ⟨v14, x_v14, h_v14⟩ else hinv2 hG in EoCases.__eo_prog_bv_mult_slt_mult_1.case_0
  pat_unapply h_v14 as ⟨v16, v17, x_v16, x_v17, h_v16, h_v17, hn_v16, hn_v17⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_mult_slt_mult_1.case_0
  pat_unapply h_v16 as ⟨v19, v20, x_v19, x_v20, h_v19, h_v20, hn_v19, hn_v20⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_mult_slt_mult_1.case_0
  step as ⟨e_v21, he_v21⟩
  store_step with CtorSpec.eo__3d.construct s2 e_v21 (by rw [he_v21]; exact empty_args) hinv2 h64 as ⟨v21, s3, hinv3, h_v21⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a9 h_a10 h_v17 h_v19 h_v20 dropping h_a8 h_v10 h_v11 h_v12 h_v14 h_v16 he_v21 hinv2 e_v21 s2 v10 v11 v12 v14 v16
  pat_same v19 v21 with h_v19 h_v21 using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_mult_slt_mult_1.case_0
  pat_same v20 a6 with h_v20 h_a6 using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_mult_slt_mult_1.case_0
  pat_unapply h_v17 as ⟨v23, v24, x_v23, x_v24, h_v23, h_v24, hn_v23, hn_v24⟩ using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_mult_slt_mult_1.case_0
  step as ⟨e_v25, he_v25⟩
  store_step with CtorSpec.eo__40bvsize.construct s3 e_v25 (by rw [he_v25]; exact empty_args) hinv3 h64 as ⟨v25, s4, hinv4, h_v25⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a9 h_a10 h_v23 h_v24 dropping h_v17 h_v19 h_v20 h_v21 he_v25 hinv3 e_v25 s3 v17 v19 v20 v21
  pat_same v23 v25 with h_v23 h_v25 using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_mult_slt_mult_1.case_0
  pat_same v24 a2 with h_v24 h_a2 using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_mult_slt_mult_1.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a9 as ⟨v27, x_v27, h_v27⟩ else hinv4 hG in EoCases.__eo_prog_bv_mult_slt_mult_1.case_0
  pat_unapply h_v27 as ⟨v29, v30, x_v29, x_v30, h_v29, h_v30, hn_v29, hn_v30⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_mult_slt_mult_1.case_0
  pat_unapply h_v29 as ⟨v32, v33, x_v32, x_v33, h_v32, h_v33, hn_v32, hn_v33⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_mult_slt_mult_1.case_0
  step as ⟨e_v34, he_v34⟩
  store_step with CtorSpec.eo__3d.construct s4 e_v34 (by rw [he_v34]; exact empty_args) hinv4 h64 as ⟨v34, s5, hinv5, h_v34⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a10 h_v30 h_v32 h_v33 dropping h_a9 h_v23 h_v24 h_v25 h_v27 h_v29 he_v34 hinv4 e_v34 s4 v23 v24 v25 v27 v29
  pat_same v32 v34 with h_v32 h_v34 using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_mult_slt_mult_1.case_0
  pat_unapply h_v33 as ⟨v36, v37, x_v36, x_v37, h_v36, h_v37, hn_v36, hn_v37⟩ using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_mult_slt_mult_1.case_0
  pat_unapply h_v36 as ⟨v39, v40, x_v39, x_v40, h_v39, h_v40, hn_v39, hn_v40⟩ using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_mult_slt_mult_1.case_0
  step as ⟨e_v41, he_v41⟩
  store_step with CtorSpec.eo__3e_3d.construct s5 e_v41 (by rw [he_v41]; exact empty_args) hinv5 h64 as ⟨v41, s6, hinv6, h_v41⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a10 h_v30 h_v37 h_v39 h_v40 dropping h_v32 h_v33 h_v34 h_v36 he_v41 hinv5 e_v41 s5 v32 v33 v34 v36
  pat_same v39 v41 with h_v39 h_v41 using hinv6 else hinv6 hG in EoCases.__eo_prog_bv_mult_slt_mult_1.case_0
  pat_same v40 a3 with h_v40 h_a3 using hinv6 else hinv6 hG in EoCases.__eo_prog_bv_mult_slt_mult_1.case_0
  pat_same v37 a5 with h_v37 h_a5 using hinv6 else hinv6 hG in EoCases.__eo_prog_bv_mult_slt_mult_1.case_0
  store_step with Store.literal_boolean_spec s6 true hinv6 h64 as ⟨v42, s7, hinv7, h_v42⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a10 h_v30 dropping h_v37 h_v39 h_v40 h_v41 hinv6 s6 v37 v39 v40 v41
  pat_same v30 v42 with h_v30 h_v42 using hinv7 else hinv7 hG in EoCases.__eo_prog_bv_mult_slt_mult_1.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a10 as ⟨v44, x_v44, h_v44⟩ else hinv7 hG in EoCases.__eo_prog_bv_mult_slt_mult_1.case_0
  pat_unapply h_v44 as ⟨v46, v47, x_v46, x_v47, h_v46, h_v47, hn_v46, hn_v47⟩ using hinv7 else hinv7 hG in EoCases.__eo_prog_bv_mult_slt_mult_1.case_0
  pat_unapply h_v46 as ⟨v49, v50, x_v49, x_v50, h_v49, h_v50, hn_v49, hn_v50⟩ using hinv7 else hinv7 hG in EoCases.__eo_prog_bv_mult_slt_mult_1.case_0
  step as ⟨e_v51, he_v51⟩
  store_step with CtorSpec.eo__3d.construct s7 e_v51 (by rw [he_v51]; exact empty_args) hinv7 h64 as ⟨v51, s8, hinv8, h_v51⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v47 h_v49 h_v50 dropping h_a10 h_v30 h_v42 h_v44 h_v46 he_v51 hinv7 e_v51 s7 v30 v42 v44 v46
  pat_same v49 v51 with h_v49 h_v51 using hinv8 else hinv8 hG in EoCases.__eo_prog_bv_mult_slt_mult_1.case_0
  pat_unapply h_v50 as ⟨v53, v54, x_v53, x_v54, h_v53, h_v54, hn_v53, hn_v54⟩ using hinv8 else hinv8 hG in EoCases.__eo_prog_bv_mult_slt_mult_1.case_0
  pat_unapply h_v53 as ⟨v56, v57, x_v56, x_v57, h_v56, h_v57, hn_v56, hn_v57⟩ using hinv8 else hinv8 hG in EoCases.__eo_prog_bv_mult_slt_mult_1.case_0
  step as ⟨e_v58, he_v58⟩
  store_step with CtorSpec.eo__3e_3d.construct s8 e_v58 (by rw [he_v58]; exact empty_args) hinv8 h64 as ⟨v58, s9, hinv9, h_v58⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v47 h_v54 h_v56 h_v57 dropping h_v49 h_v50 h_v51 h_v53 he_v58 hinv8 e_v58 s8 v49 v50 v51 v53
  pat_same v56 v58 with h_v56 h_v58 using hinv9 else hinv9 hG in EoCases.__eo_prog_bv_mult_slt_mult_1.case_0
  pat_same v57 a4 with h_v57 h_a4 using hinv9 else hinv9 hG in EoCases.__eo_prog_bv_mult_slt_mult_1.case_0
  pat_same v54 a6 with h_v54 h_a6 using hinv9 else hinv9 hG in EoCases.__eo_prog_bv_mult_slt_mult_1.case_0
  store_step with Store.literal_boolean_spec s9 true hinv9 h64 as ⟨v59, s10, hinv10, h_v59⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v47 dropping h_v54 h_v56 h_v57 h_v58 hinv9 s9 v54 v56 v57 v58
  pat_same v47 v59 with h_v47 h_v59 using hinv10 else hinv10 hG in EoCases.__eo_prog_bv_mult_slt_mult_1.case_0
  step as ⟨e_v60, he_v60⟩
  store_step with CtorSpec.eo__3d.construct s10 e_v60 (by rw [he_v60]; exact empty_args) hinv10 h64 as ⟨v60, s11, hinv11, h_v60⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 dropping h_v47 h_v59 he_v60 hinv10 e_v60 s10 v47 v59
  step as ⟨e_v61, he_v61⟩
  store_step with CtorSpec.eo_bvslt.construct s11 e_v61 (by rw [he_v61]; exact empty_args) hinv11 h64 as ⟨v61, s12, hinv12, h_v61⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v60 dropping he_v61 hinv11 e_v61 s11
  step as ⟨e_v62, he_v62⟩
  store_step with CtorSpec.eo_bvmul.construct s12 e_v62 (by rw [he_v62]; exact empty_args) hinv12 h64 as ⟨v62, s13, hinv13, h_v62⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v60 h_v61 dropping he_v62 hinv12 e_v62 s12
  step as ⟨e_v63, he_v63⟩
  store_step with CtorSpec.eo_sign_5fextend.construct s13 e_v63 (by rw [he_v63]; rfl) h_a3 hinv13 h64 as ⟨v63, s14, hinv14, h_v63⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v60 h_v61 h_v62 dropping he_v63 hinv13 e_v63 s13
  store_step with Store.apply_rep s14 v63 a1 _ _ hinv14 h64 h_v63 h_a1 (by ns_tac) (by ns_tac) as ⟨v64, s15, hinv15, h_v64⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v60 h_v61 h_v62 dropping h_v63 hinv14 s14 v63
  store_step with Store.apply_rep s15 v62 v64 _ _ hinv15 h64 h_v62 h_v64 (by ns_tac) (by ns_tac) as ⟨v65, s16, hinv16, h_v65⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v60 h_v61 dropping h_v62 h_v64 hinv15 s15 v62 v64
  step as ⟨e_v66, he_v66⟩
  store_step with CtorSpec.eo_bvmul.construct s16 e_v66 (by rw [he_v66]; exact empty_args) hinv16 h64 as ⟨v66, s17, hinv17, h_v66⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v60 h_v61 h_v65 dropping he_v66 hinv16 e_v66 s16
  step as ⟨e_v67, he_v67⟩
  store_step with CtorSpec.eo_sign_5fextend.construct s17 e_v67 (by rw [he_v67]; rfl) h_a4 hinv17 h64 as ⟨v67, s18, hinv18, h_v67⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v60 h_v61 h_v65 h_v66 dropping he_v67 hinv17 e_v67 s17
  store_step with Store.apply_rep s18 v67 a2 _ _ hinv18 h64 h_v67 h_a2 (by ns_tac) (by ns_tac) as ⟨v68, s19, hinv19, h_v68⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v60 h_v61 h_v65 h_v66 dropping h_v67 hinv18 s18 v67
  store_step with Store.apply_rep s19 v66 v68 _ _ hinv19 h64 h_v66 h_v68 (by ns_tac) (by ns_tac) as ⟨v69, s20, hinv20, h_v69⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v60 h_v61 h_v65 dropping h_v66 h_v68 hinv19 s19 v66 v68
  step as ⟨e_v70, he_v70⟩
  store_step with CtorSpec.eo_bvmul.construct s20 e_v70 (by rw [he_v70]; exact empty_args) hinv20 h64 as ⟨v70, s21, hinv21, h_v70⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v60 h_v61 h_v65 h_v69 dropping he_v70 hinv20 e_v70 s20
  step as ⟨e_v71, he_v71⟩
  store_step with CtorSpec.eo_sign_5fextend.construct s21 e_v71 (by rw [he_v71]; rfl) h_a3 hinv21 h64 as ⟨v71, s22, hinv22, h_v71⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v60 h_v61 h_v65 h_v69 h_v70 dropping he_v71 hinv21 e_v71 s21
  store_step with Store.apply_rep s22 v71 a1 _ _ hinv22 h64 h_v71 h_a1 (by ns_tac) (by ns_tac) as ⟨v72, s23, hinv23, h_v72⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v60 h_v61 h_v65 h_v69 h_v70 dropping h_v71 hinv22 s22 v71
  store_step with ih.eo__24eo_5ftypeof s23 v72 _ hinv23 h64 (hG.rem hrem) h_v72 as ⟨v73, s24, hinv24, h_v73⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v60 h_v61 h_v65 h_v69 h_v70 dropping h_v72 hinv23 s23 v72
  store_step with ih.eo__24eo_5fnil s24 v70 v73 _ _ hinv24 h64 (hG.rem hrem) h_v70 h_v73 as ⟨v74, s25, hinv25, h_v74⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v60 h_v61 h_v65 h_v69 dropping h_v70 h_v73 hinv24 s24 v70 v73
  store_step with Store.apply_mk_rep s25 v69 v74 _ _ hinv25 h64 h_v69 h_v74 as ⟨v75, s26, hinv26, h_v75⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v60 h_v61 h_v65 dropping h_v69 h_v74 hinv25 s25 v69 v74
  store_step with Store.apply_mk_rep s26 v65 v75 _ _ hinv26 h64 h_v65 h_v75 as ⟨v76, s27, hinv27, h_v76⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v60 h_v61 dropping h_v65 h_v75 hinv26 s26 v65 v75
  store_step with Store.apply_mk_rep s27 v61 v76 _ _ hinv27 h64 h_v61 h_v76 as ⟨v77, s28, hinv28, h_v77⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v60 dropping h_v61 h_v76 hinv27 s27 v61 v76
  step as ⟨e_v78, he_v78⟩
  store_step with CtorSpec.eo_bvmul.construct s28 e_v78 (by rw [he_v78]; exact empty_args) hinv28 h64 as ⟨v78, s29, hinv29, h_v78⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v60 h_v77 dropping he_v78 hinv28 e_v78 s28
  step as ⟨e_v79, he_v79⟩
  store_step with CtorSpec.eo_sign_5fextend.construct s29 e_v79 (by rw [he_v79]; rfl) h_a3 hinv29 h64 as ⟨v79, s30, hinv30, h_v79⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v60 h_v77 h_v78 dropping he_v79 hinv29 e_v79 s29
  store_step with Store.apply_rep s30 v79 a0 _ _ hinv30 h64 h_v79 h_a0 (by ns_tac) (by ns_tac) as ⟨v80, s31, hinv31, h_v80⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v60 h_v77 h_v78 dropping h_v79 hinv30 s30 v79
  store_step with Store.apply_rep s31 v78 v80 _ _ hinv31 h64 h_v78 h_v80 (by ns_tac) (by ns_tac) as ⟨v81, s32, hinv32, h_v81⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v60 h_v77 dropping h_v78 h_v80 hinv31 s31 v78 v80
  step as ⟨e_v82, he_v82⟩
  store_step with CtorSpec.eo_bvmul.construct s32 e_v82 (by rw [he_v82]; exact empty_args) hinv32 h64 as ⟨v82, s33, hinv33, h_v82⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v60 h_v77 h_v81 dropping he_v82 hinv32 e_v82 s32
  step as ⟨e_v83, he_v83⟩
  store_step with CtorSpec.eo_sign_5fextend.construct s33 e_v83 (by rw [he_v83]; rfl) h_a4 hinv33 h64 as ⟨v83, s34, hinv34, h_v83⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a5 h_a6 h_v60 h_v77 h_v81 h_v82 dropping h_a4 he_v83 hinv33 e_v83 s33
  store_step with Store.apply_rep s34 v83 a2 _ _ hinv34 h64 h_v83 h_a2 (by ns_tac) (by ns_tac) as ⟨v84, s35, hinv35, h_v84⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a5 h_a6 h_v60 h_v77 h_v81 h_v82 dropping h_v83 hinv34 s34 v83
  store_step with Store.apply_rep s35 v82 v84 _ _ hinv35 h64 h_v82 h_v84 (by ns_tac) (by ns_tac) as ⟨v85, s36, hinv36, h_v85⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a5 h_a6 h_v60 h_v77 h_v81 dropping h_v82 h_v84 hinv35 s35 v82 v84
  step as ⟨e_v86, he_v86⟩
  store_step with CtorSpec.eo_bvmul.construct s36 e_v86 (by rw [he_v86]; exact empty_args) hinv36 h64 as ⟨v86, s37, hinv37, h_v86⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a5 h_a6 h_v60 h_v77 h_v81 h_v85 dropping he_v86 hinv36 e_v86 s36
  step as ⟨e_v87, he_v87⟩
  store_step with CtorSpec.eo_sign_5fextend.construct s37 e_v87 (by rw [he_v87]; rfl) h_a3 hinv37 h64 as ⟨v87, s38, hinv38, h_v87⟩ growing hG carrying h_a0 h_a1 h_a2 h_a5 h_a6 h_v60 h_v77 h_v81 h_v85 h_v86 dropping h_a3 he_v87 hinv37 e_v87 s37
  store_step with Store.apply_rep s38 v87 a0 _ _ hinv38 h64 h_v87 h_a0 (by ns_tac) (by ns_tac) as ⟨v88, s39, hinv39, h_v88⟩ growing hG carrying h_a0 h_a1 h_a2 h_a5 h_a6 h_v60 h_v77 h_v81 h_v85 h_v86 dropping h_v87 hinv38 s38 v87
  store_step with ih.eo__24eo_5ftypeof s39 v88 _ hinv39 h64 (hG.rem hrem) h_v88 as ⟨v89, s40, hinv40, h_v89⟩ growing hG carrying h_a0 h_a1 h_a2 h_a5 h_a6 h_v60 h_v77 h_v81 h_v85 h_v86 dropping h_v88 hinv39 s39 v88
  store_step with ih.eo__24eo_5fnil s40 v86 v89 _ _ hinv40 h64 (hG.rem hrem) h_v86 h_v89 as ⟨v90, s41, hinv41, h_v90⟩ growing hG carrying h_a0 h_a1 h_a2 h_a5 h_a6 h_v60 h_v77 h_v81 h_v85 dropping h_v86 h_v89 hinv40 s40 v86 v89
  store_step with Store.apply_mk_rep s41 v85 v90 _ _ hinv41 h64 h_v85 h_v90 as ⟨v91, s42, hinv42, h_v91⟩ growing hG carrying h_a0 h_a1 h_a2 h_a5 h_a6 h_v60 h_v77 h_v81 dropping h_v85 h_v90 hinv41 s41 v85 v90
  store_step with Store.apply_mk_rep s42 v81 v91 _ _ hinv42 h64 h_v81 h_v91 as ⟨v92, s43, hinv43, h_v92⟩ growing hG carrying h_a0 h_a1 h_a2 h_a5 h_a6 h_v60 h_v77 dropping h_v81 h_v91 hinv42 s42 v81 v91
  store_step with Store.apply_mk_rep s43 v77 v92 _ _ hinv43 h64 h_v77 h_v92 as ⟨v93, s44, hinv44, h_v93⟩ growing hG carrying h_a0 h_a1 h_a2 h_a5 h_a6 h_v60 dropping h_v77 h_v92 hinv43 s43 v77 v92
  store_step with Store.apply_mk_rep s44 v60 v93 _ _ hinv44 h64 h_v60 h_v93 as ⟨v94, s45, hinv45, h_v94⟩ growing hG carrying h_a0 h_a1 h_a2 h_a5 h_a6 dropping h_v60 h_v93 hinv44 s44 v60 v93
  step as ⟨e_v95, he_v95⟩
  store_step with CtorSpec.eo_and.construct s45 e_v95 (by rw [he_v95]; exact empty_args) hinv45 h64 as ⟨v95, s46, hinv46, h_v95⟩ growing hG carrying h_a0 h_a1 h_a2 h_a5 h_a6 h_v94 dropping he_v95 hinv45 e_v95 s45
  step as ⟨e_v96, he_v96⟩
  store_step with CtorSpec.eo_not.construct s46 e_v96 (by rw [he_v96]; exact empty_args) hinv46 h64 as ⟨v96, s47, hinv47, h_v96⟩ growing hG carrying h_a0 h_a1 h_a2 h_a5 h_a6 h_v94 h_v95 dropping he_v96 hinv46 e_v96 s46
  step as ⟨e_v97, he_v97⟩
  store_step with CtorSpec.eo__3d.construct s47 e_v97 (by rw [he_v97]; exact empty_args) hinv47 h64 as ⟨v97, s48, hinv48, h_v97⟩ growing hG carrying h_a0 h_a1 h_a2 h_a5 h_a6 h_v94 h_v95 h_v96 dropping he_v97 hinv47 e_v97 s47
  step as ⟨e_v98, he_v98⟩
  store_step with CtorSpec.eo_bvsub.construct s48 e_v98 (by rw [he_v98]; exact empty_args) hinv48 h64 as ⟨v98, s49, hinv49, h_v98⟩ growing hG carrying h_a0 h_a1 h_a2 h_a5 h_a6 h_v94 h_v95 h_v96 h_v97 dropping he_v98 hinv48 e_v98 s48
  store_step with Store.apply_rep s49 v98 a1 _ _ hinv49 h64 h_v98 h_a1 (by ns_tac) (by ns_tac) as ⟨v99, s50, hinv50, h_v99⟩ growing hG carrying h_a0 h_a1 h_a2 h_a5 h_a6 h_v94 h_v95 h_v96 h_v97 dropping h_v98 hinv49 s49 v98
  store_step with Store.apply_rep s50 v99 a0 _ _ hinv50 h64 h_v99 h_a0 (by ns_tac) (by ns_tac) as ⟨v100, s51, hinv51, h_v100⟩ growing hG carrying h_a0 h_a1 h_a2 h_a5 h_a6 h_v94 h_v95 h_v96 h_v97 dropping h_v99 hinv50 s50 v99
  store_step with Store.apply_rep s51 v97 v100 _ _ hinv51 h64 h_v97 h_v100 (by ns_tac) (by ns_tac) as ⟨v101, s52, hinv52, h_v101⟩ growing hG carrying h_a0 h_a1 h_a2 h_a5 h_a6 h_v94 h_v95 h_v96 dropping h_v100 h_v97 hinv51 s51 v100 v97
  step as ⟨e_v102, he_v102⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s52 e_v102 (by rw [he_v102]; rfl) h_a5 hinv52 h64 as ⟨v102, s53, hinv53, h_v102⟩ growing hG carrying h_a0 h_a1 h_a2 h_a6 h_v94 h_v95 h_v96 h_v101 dropping h_a5 he_v102 hinv52 e_v102 s52
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s53 0#u32 (0) (by scalar_tac) hinv53 h64 as ⟨v103, s54, hinv54, h_v103⟩ growing hG carrying h_a0 h_a1 h_a2 h_a6 h_v94 h_v95 h_v96 h_v101 h_v102 dropping hinv53 s53
  store_step with Store.apply_rep s54 v102 v103 _ _ hinv54 h64 h_v102 h_v103 (by ns_tac) (by ns_tac) as ⟨v104, s55, hinv55, h_v104⟩ growing hG carrying h_a0 h_a1 h_a2 h_a6 h_v94 h_v95 h_v96 h_v101 dropping h_v102 h_v103 hinv54 s54 v102 v103
  store_step with Store.apply_rep s55 v101 v104 _ _ hinv55 h64 h_v101 h_v104 (by ns_tac) (by ns_tac) as ⟨v105, s56, hinv56, h_v105⟩ growing hG carrying h_a0 h_a1 h_a2 h_a6 h_v94 h_v95 h_v96 dropping h_v101 h_v104 hinv55 s55 v101 v104
  store_step with Store.apply_rep s56 v96 v105 _ _ hinv56 h64 h_v96 h_v105 (by ns_tac) (by ns_tac) as ⟨v106, s57, hinv57, h_v106⟩ growing hG carrying h_a0 h_a1 h_a2 h_a6 h_v94 h_v95 dropping h_v105 h_v96 hinv56 s56 v105 v96
  store_step with Store.apply_rep s57 v95 v106 _ _ hinv57 h64 h_v95 h_v106 (by ns_tac) (by ns_tac) as ⟨v107, s58, hinv58, h_v107⟩ growing hG carrying h_a0 h_a1 h_a2 h_a6 h_v94 dropping h_v106 h_v95 hinv57 s57 v106 v95
  step as ⟨e_v108, he_v108⟩
  store_step with CtorSpec.eo_and.construct s58 e_v108 (by rw [he_v108]; exact empty_args) hinv58 h64 as ⟨v108, s59, hinv59, h_v108⟩ growing hG carrying h_a0 h_a1 h_a2 h_a6 h_v94 h_v107 dropping he_v108 hinv58 e_v108 s58
  step as ⟨e_v109, he_v109⟩
  store_step with CtorSpec.eo_not.construct s59 e_v109 (by rw [he_v109]; exact empty_args) hinv59 h64 as ⟨v109, s60, hinv60, h_v109⟩ growing hG carrying h_a0 h_a1 h_a2 h_a6 h_v94 h_v107 h_v108 dropping he_v109 hinv59 e_v109 s59
  step as ⟨e_v110, he_v110⟩
  store_step with CtorSpec.eo__3d.construct s60 e_v110 (by rw [he_v110]; exact empty_args) hinv60 h64 as ⟨v110, s61, hinv61, h_v110⟩ growing hG carrying h_a0 h_a1 h_a2 h_a6 h_v94 h_v107 h_v108 h_v109 dropping he_v110 hinv60 e_v110 s60
  store_step with Store.apply_rep s61 v110 a2 _ _ hinv61 h64 h_v110 h_a2 (by ns_tac) (by ns_tac) as ⟨v111, s62, hinv62, h_v111⟩ growing hG carrying h_a0 h_a1 h_a2 h_a6 h_v94 h_v107 h_v108 h_v109 dropping h_v110 hinv61 s61 v110
  step as ⟨e_v112, he_v112⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s62 e_v112 (by rw [he_v112]; rfl) h_a6 hinv62 h64 as ⟨v112, s63, hinv63, h_v112⟩ growing hG carrying h_a0 h_a1 h_a2 h_a6 h_v94 h_v107 h_v108 h_v109 h_v111 dropping he_v112 hinv62 e_v112 s62
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s63 0#u32 (0) (by scalar_tac) hinv63 h64 as ⟨v113, s64, hinv64, h_v113⟩ growing hG carrying h_a0 h_a1 h_a2 h_a6 h_v94 h_v107 h_v108 h_v109 h_v111 h_v112 dropping hinv63 s63
  store_step with Store.apply_rep s64 v112 v113 _ _ hinv64 h64 h_v112 h_v113 (by ns_tac) (by ns_tac) as ⟨v114, s65, hinv65, h_v114⟩ growing hG carrying h_a0 h_a1 h_a2 h_a6 h_v94 h_v107 h_v108 h_v109 h_v111 dropping h_v112 h_v113 hinv64 s64 v112 v113
  store_step with Store.apply_rep s65 v111 v114 _ _ hinv65 h64 h_v111 h_v114 (by ns_tac) (by ns_tac) as ⟨v115, s66, hinv66, h_v115⟩ growing hG carrying h_a0 h_a1 h_a2 h_a6 h_v94 h_v107 h_v108 h_v109 dropping h_v111 h_v114 hinv65 s65 v111 v114
  store_step with Store.apply_rep s66 v109 v115 _ _ hinv66 h64 h_v109 h_v115 (by ns_tac) (by ns_tac) as ⟨v116, s67, hinv67, h_v116⟩ growing hG carrying h_a0 h_a1 h_a2 h_a6 h_v94 h_v107 h_v108 dropping h_v109 h_v115 hinv66 s66 v109 v115
  store_step with Store.apply_rep s67 v108 v116 _ _ hinv67 h64 h_v108 h_v116 (by ns_tac) (by ns_tac) as ⟨v117, s68, hinv68, h_v117⟩ growing hG carrying h_a0 h_a1 h_a2 h_a6 h_v94 h_v107 dropping h_v108 h_v116 hinv67 s67 v108 v116
  step as ⟨e_v118, he_v118⟩
  store_step with CtorSpec.eo_and.construct s68 e_v118 (by rw [he_v118]; exact empty_args) hinv68 h64 as ⟨v118, s69, hinv69, h_v118⟩ growing hG carrying h_a0 h_a1 h_a2 h_a6 h_v94 h_v107 h_v117 dropping he_v118 hinv68 e_v118 s68
  step as ⟨e_v119, he_v119⟩
  store_step with CtorSpec.eo__3d.construct s69 e_v119 (by rw [he_v119]; exact empty_args) hinv69 h64 as ⟨v119, s70, hinv70, h_v119⟩ growing hG carrying h_a0 h_a1 h_a2 h_a6 h_v94 h_v107 h_v117 h_v118 dropping he_v119 hinv69 e_v119 s69
  step as ⟨e_v120, he_v120⟩
  store_step with CtorSpec.eo_bvslt.construct s70 e_v120 (by rw [he_v120]; exact empty_args) hinv70 h64 as ⟨v120, s71, hinv71, h_v120⟩ growing hG carrying h_a0 h_a1 h_a2 h_a6 h_v94 h_v107 h_v117 h_v118 h_v119 dropping he_v120 hinv70 e_v120 s70
  store_step with Store.apply_rep s71 v120 a1 _ _ hinv71 h64 h_v120 h_a1 (by ns_tac) (by ns_tac) as ⟨v121, s72, hinv72, h_v121⟩ growing hG carrying h_a0 h_a2 h_a6 h_v94 h_v107 h_v117 h_v118 h_v119 dropping h_a1 h_v120 hinv71 s71 v120
  store_step with Store.apply_rep s72 v121 a0 _ _ hinv72 h64 h_v121 h_a0 (by ns_tac) (by ns_tac) as ⟨v122, s73, hinv73, h_v122⟩ growing hG carrying h_a2 h_a6 h_v94 h_v107 h_v117 h_v118 h_v119 dropping h_a0 h_v121 hinv72 s72 v121
  store_step with Store.apply_rep s73 v119 v122 _ _ hinv73 h64 h_v119 h_v122 (by ns_tac) (by ns_tac) as ⟨v123, s74, hinv74, h_v123⟩ growing hG carrying h_a2 h_a6 h_v94 h_v107 h_v117 h_v118 dropping h_v119 h_v122 hinv73 s73 v119 v122
  step as ⟨e_v124, he_v124⟩
  store_step with CtorSpec.eo_bvsgt.construct s74 e_v124 (by rw [he_v124]; exact empty_args) hinv74 h64 as ⟨v124, s75, hinv75, h_v124⟩ growing hG carrying h_a2 h_a6 h_v94 h_v107 h_v117 h_v118 h_v123 dropping he_v124 hinv74 e_v124 s74
  store_step with Store.apply_rep s75 v124 a2 _ _ hinv75 h64 h_v124 h_a2 (by ns_tac) (by ns_tac) as ⟨v125, s76, hinv76, h_v125⟩ growing hG carrying h_a6 h_v94 h_v107 h_v117 h_v118 h_v123 dropping h_a2 h_v124 hinv75 s75 v124
  step as ⟨e_v126, he_v126⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s76 e_v126 (by rw [he_v126]; rfl) h_a6 hinv76 h64 as ⟨v126, s77, hinv77, h_v126⟩ growing hG carrying h_v94 h_v107 h_v117 h_v118 h_v123 h_v125 dropping h_a6 he_v126 hinv76 e_v126 s76
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s77 0#u32 (0) (by scalar_tac) hinv77 h64 as ⟨v127, s78, hinv78, h_v127⟩ growing hG carrying h_v94 h_v107 h_v117 h_v118 h_v123 h_v125 h_v126 dropping hinv77 s77
  store_step with Store.apply_rep s78 v126 v127 _ _ hinv78 h64 h_v126 h_v127 (by ns_tac) (by ns_tac) as ⟨v128, s79, hinv79, h_v128⟩ growing hG carrying h_v94 h_v107 h_v117 h_v118 h_v123 h_v125 dropping h_v126 h_v127 hinv78 s78 v126 v127
  store_step with Store.apply_rep s79 v125 v128 _ _ hinv79 h64 h_v125 h_v128 (by ns_tac) (by ns_tac) as ⟨v129, s80, hinv80, h_v129⟩ growing hG carrying h_v94 h_v107 h_v117 h_v118 h_v123 dropping h_v125 h_v128 hinv79 s79 v125 v128
  store_step with Store.apply_rep s80 v123 v129 _ _ hinv80 h64 h_v123 h_v129 (by ns_tac) (by ns_tac) as ⟨v130, s81, hinv81, h_v130⟩ growing hG carrying h_v94 h_v107 h_v117 h_v118 dropping h_v123 h_v129 hinv80 s80 v123 v129
  store_step with Store.apply_rep s81 v118 v130 _ _ hinv81 h64 h_v118 h_v130 (by ns_tac) (by ns_tac) as ⟨v131, s82, hinv82, h_v131⟩ growing hG carrying h_v94 h_v107 h_v117 dropping h_v118 h_v130 hinv81 s81 v118 v130
  store_step with Store.literal_boolean_spec s82 true hinv82 h64 as ⟨v132, s83, hinv83, h_v132⟩ growing hG carrying h_v94 h_v107 h_v117 h_v131 dropping hinv82 s82
  store_step with Store.apply_rep s83 v131 v132 _ _ hinv83 h64 h_v131 h_v132 (by ns_tac) (by ns_tac) as ⟨v133, s84, hinv84, h_v133⟩ growing hG carrying h_v94 h_v107 h_v117 dropping h_v131 h_v132 hinv83 s83 v131 v132
  store_step with Store.apply_rep s84 v117 v133 _ _ hinv84 h64 h_v117 h_v133 (by ns_tac) (by ns_tac) as ⟨v134, s85, hinv85, h_v134⟩ growing hG carrying h_v94 h_v107 dropping h_v117 h_v133 hinv84 s84 v117 v133
  store_step with Store.apply_rep s85 v107 v134 _ _ hinv85 h64 h_v107 h_v134 (by ns_tac) (by ns_tac) as ⟨v135, s86, hinv86, h_v135⟩ growing hG carrying h_v94 dropping h_v107 h_v134 hinv85 s85 v107 v134
  store_step with Store.apply_mk_rep s86 v94 v135 _ _ hinv86 h64 h_v94 h_v135 as ⟨v136, s87, hinv87, h_v136⟩ growing hG carrying dropping h_v135 h_v94 hinv86 s86 v135 v94
  case_done hinv87 hG with h_v136 in EoCases.__eo_prog_bv_mult_slt_mult_1.case_0 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_a5 hn_a6 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v16 hn_v17 hn_v19 hn_v20 hn_v23 hn_v24 hn_v29 hn_v30 hn_v32 hn_v33 hn_v36 hn_v37 hn_v39 hn_v40 hn_v46 hn_v47 hn_v49 hn_v50 hn_v53 hn_v54 hn_v56 hn_v57

/-- logos's `__eo_prog_bv_mult_slt_mult_1` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fbv_2dmult_2dslt_2dmult_2d1.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _) (x_a7 : _) (x_a8 : _) (x_a9 : _) (x_a10 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) (hw_a4 : Valid.valid x_a4) (hw_a5 : Valid.valid x_a5) (hw_a6 : Valid.valid x_a6) (hw_a7 : Valid.valid x_a7) (hw_a8 : Valid.valid x_a8) (hw_a9 : Valid.valid x_a9) (hw_a10 : Valid.valid x_a10) :
    __eo_prog_bv_mult_slt_mult_1 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 x_a9 x_a10 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else if x_a4 = Eo.Term.Stuck then HasStuck.stuck else if x_a5 = Eo.Term.Stuck then HasStuck.stuck else if x_a6 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_bv_mult_slt_mult_1.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 x_a9 x_a10] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_bv_mult_slt_mult_1
  unfold EoCases.__eo_prog_bv_mult_slt_mult_1.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fbv_2dmult_2dslt_2dmult_2d1_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _) (x_a7 : _) (x_a8 : _) (x_a9 : _) (x_a10 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) (h_a6 : Represents.rep s a6 x_a6) (h_a7 : Represents.rep s a7 x_a7) (h_a8 : Represents.rep s a8 x_a8) (h_a9 : Represents.rep s a9 x_a9) (h_a10 : Represents.rep s a10 x_a10) :
    body_eo__24eo_5fprog_5fbv_2dmult_2dslt_2dmult_2d1 s a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_mult_slt_mult_1 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 x_a9 x_a10)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fbv_2dmult_2dslt_2dmult_2d1.rust_eq x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 x_a9 x_a10 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3) (by valid_tac hinv h_a4) (by valid_tac hinv h_a5) (by valid_tac hinv h_a6) (by valid_tac hinv h_a7) (by valid_tac hinv h_a8) (by valid_tac hinv h_a9) (by valid_tac hinv h_a10)]
  unfold body_eo__24eo_5fprog_5fbv_2dmult_2dslt_2dmult_2d1
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  stuck_check h_a3 : x_a3 as hn_a3 else hinv hG
  stuck_check h_a4 : x_a4 as hn_a4 else hinv hG
  stuck_check h_a5 : x_a5 as hn_a5 else hinv hG
  stuck_check h_a6 : x_a6 as hn_a6 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fbv_2dmult_2dslt_2dmult_2d1_spec n ih s a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 x_a9 x_a10 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 h_a9 h_a10 hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_a5 hn_a6
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 h_a9 h_a10 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_a5 hn_a6
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_a5 hn_a6 hc0 in EoCases.__eo_prog_bv_mult_slt_mult_1.case_0

theorem eo__24eo_5fprog_5fbv_2dmult_2dslt_2dmult_2d1_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fbv_2dmult_2dslt_2dmult_2d1.Spec n := by
  intro s a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 x_a9 x_a10 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 h_a9 h_a10
  unfold eo__24eo_5fprog_5fbv_2dmult_2dslt_2dmult_2d1
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fbv_2dmult_2dslt_2dmult_2d1 s1 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10) (fun s' t => Represents.rep s' t (__eo_prog_bv_mult_slt_mult_1 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 x_a9 x_a10))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fbv_2dmult_2dslt_2dmult_2d1_spec m (ih m hm) s1 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 x_a9 x_a10 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn) (by congr_one h_a4 hn) (by congr_one h_a5 hn) (by congr_one h_a6 hn) (by congr_one h_a7 hn) (by congr_one h_a8 hn) (by congr_one h_a9 hn) (by congr_one h_a10 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

set_option maxHeartbeats 2610000 in
theorem case_0_eo__24eo_5fprog_5fbv_2dmult_2dslt_2dmult_2d2_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _) (x_a7 : _) (x_a8 : _) (x_a9 : _) (x_a10 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) (h_a6 : Represents.rep s a6 x_a6) (h_a7 : Represents.rep s a7 x_a7) (h_a8 : Represents.rep s a8 x_a8) (h_a9 : Represents.rep s a9 x_a9) (h_a10 : Represents.rep s a10 x_a10) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) (hn_a4 : x_a4 ≠ Eo.Term.Stuck) (hn_a5 : x_a5 ≠ Eo.Term.Stuck) (hn_a6 : x_a6 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fbv_2dmult_2dslt_2dmult_2d2 s a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_bv_mult_slt_mult_2.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 x_a9 x_a10 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_bv_mult_slt_mult_2.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 x_a9 x_a10 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fbv_2dmult_2dslt_2dmult_2d2
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a7 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_bv_mult_slt_mult_2.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_mult_slt_mult_2.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_mult_slt_mult_2.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a8 h_a9 h_a10 h_v4 h_v6 h_v7 dropping h_a7 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_mult_slt_mult_2.case_0
  pat_same v7 a5 with h_v7 h_a5 using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_mult_slt_mult_2.case_0
  pat_unapply h_v4 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_mult_slt_mult_2.case_0
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo__40bvsize.construct s1 e_v12 (by rw [he_v12]; exact empty_args) hinv1 h64 as ⟨v12, s2, hinv2, h_v12⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a8 h_a9 h_a10 h_v10 h_v11 dropping h_v4 h_v6 h_v7 h_v8 he_v12 hinv1 e_v12 s1 v4 v6 v7 v8
  pat_same v10 v12 with h_v10 h_v12 using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_mult_slt_mult_2.case_0
  pat_same v11 a0 with h_v11 h_a0 using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_mult_slt_mult_2.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a8 as ⟨v14, x_v14, h_v14⟩ else hinv2 hG in EoCases.__eo_prog_bv_mult_slt_mult_2.case_0
  pat_unapply h_v14 as ⟨v16, v17, x_v16, x_v17, h_v16, h_v17, hn_v16, hn_v17⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_mult_slt_mult_2.case_0
  pat_unapply h_v16 as ⟨v19, v20, x_v19, x_v20, h_v19, h_v20, hn_v19, hn_v20⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_mult_slt_mult_2.case_0
  step as ⟨e_v21, he_v21⟩
  store_step with CtorSpec.eo__3d.construct s2 e_v21 (by rw [he_v21]; exact empty_args) hinv2 h64 as ⟨v21, s3, hinv3, h_v21⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a9 h_a10 h_v17 h_v19 h_v20 dropping h_a8 h_v10 h_v11 h_v12 h_v14 h_v16 he_v21 hinv2 e_v21 s2 v10 v11 v12 v14 v16
  pat_same v19 v21 with h_v19 h_v21 using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_mult_slt_mult_2.case_0
  pat_same v20 a6 with h_v20 h_a6 using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_mult_slt_mult_2.case_0
  pat_unapply h_v17 as ⟨v23, v24, x_v23, x_v24, h_v23, h_v24, hn_v23, hn_v24⟩ using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_mult_slt_mult_2.case_0
  step as ⟨e_v25, he_v25⟩
  store_step with CtorSpec.eo__40bvsize.construct s3 e_v25 (by rw [he_v25]; exact empty_args) hinv3 h64 as ⟨v25, s4, hinv4, h_v25⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a9 h_a10 h_v23 h_v24 dropping h_v17 h_v19 h_v20 h_v21 he_v25 hinv3 e_v25 s3 v17 v19 v20 v21
  pat_same v23 v25 with h_v23 h_v25 using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_mult_slt_mult_2.case_0
  pat_same v24 a2 with h_v24 h_a2 using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_mult_slt_mult_2.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a9 as ⟨v27, x_v27, h_v27⟩ else hinv4 hG in EoCases.__eo_prog_bv_mult_slt_mult_2.case_0
  pat_unapply h_v27 as ⟨v29, v30, x_v29, x_v30, h_v29, h_v30, hn_v29, hn_v30⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_mult_slt_mult_2.case_0
  pat_unapply h_v29 as ⟨v32, v33, x_v32, x_v33, h_v32, h_v33, hn_v32, hn_v33⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_mult_slt_mult_2.case_0
  step as ⟨e_v34, he_v34⟩
  store_step with CtorSpec.eo__3d.construct s4 e_v34 (by rw [he_v34]; exact empty_args) hinv4 h64 as ⟨v34, s5, hinv5, h_v34⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a10 h_v30 h_v32 h_v33 dropping h_a9 h_v23 h_v24 h_v25 h_v27 h_v29 he_v34 hinv4 e_v34 s4 v23 v24 v25 v27 v29
  pat_same v32 v34 with h_v32 h_v34 using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_mult_slt_mult_2.case_0
  pat_unapply h_v33 as ⟨v36, v37, x_v36, x_v37, h_v36, h_v37, hn_v36, hn_v37⟩ using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_mult_slt_mult_2.case_0
  pat_unapply h_v36 as ⟨v39, v40, x_v39, x_v40, h_v39, h_v40, hn_v39, hn_v40⟩ using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_mult_slt_mult_2.case_0
  step as ⟨e_v41, he_v41⟩
  store_step with CtorSpec.eo__3e_3d.construct s5 e_v41 (by rw [he_v41]; exact empty_args) hinv5 h64 as ⟨v41, s6, hinv6, h_v41⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a10 h_v30 h_v37 h_v39 h_v40 dropping h_v32 h_v33 h_v34 h_v36 he_v41 hinv5 e_v41 s5 v32 v33 v34 v36
  pat_same v39 v41 with h_v39 h_v41 using hinv6 else hinv6 hG in EoCases.__eo_prog_bv_mult_slt_mult_2.case_0
  pat_same v40 a3 with h_v40 h_a3 using hinv6 else hinv6 hG in EoCases.__eo_prog_bv_mult_slt_mult_2.case_0
  pat_same v37 a5 with h_v37 h_a5 using hinv6 else hinv6 hG in EoCases.__eo_prog_bv_mult_slt_mult_2.case_0
  store_step with Store.literal_boolean_spec s6 true hinv6 h64 as ⟨v42, s7, hinv7, h_v42⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a10 h_v30 dropping h_v37 h_v39 h_v40 h_v41 hinv6 s6 v37 v39 v40 v41
  pat_same v30 v42 with h_v30 h_v42 using hinv7 else hinv7 hG in EoCases.__eo_prog_bv_mult_slt_mult_2.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a10 as ⟨v44, x_v44, h_v44⟩ else hinv7 hG in EoCases.__eo_prog_bv_mult_slt_mult_2.case_0
  pat_unapply h_v44 as ⟨v46, v47, x_v46, x_v47, h_v46, h_v47, hn_v46, hn_v47⟩ using hinv7 else hinv7 hG in EoCases.__eo_prog_bv_mult_slt_mult_2.case_0
  pat_unapply h_v46 as ⟨v49, v50, x_v49, x_v50, h_v49, h_v50, hn_v49, hn_v50⟩ using hinv7 else hinv7 hG in EoCases.__eo_prog_bv_mult_slt_mult_2.case_0
  step as ⟨e_v51, he_v51⟩
  store_step with CtorSpec.eo__3d.construct s7 e_v51 (by rw [he_v51]; exact empty_args) hinv7 h64 as ⟨v51, s8, hinv8, h_v51⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v47 h_v49 h_v50 dropping h_a10 h_v30 h_v42 h_v44 h_v46 he_v51 hinv7 e_v51 s7 v30 v42 v44 v46
  pat_same v49 v51 with h_v49 h_v51 using hinv8 else hinv8 hG in EoCases.__eo_prog_bv_mult_slt_mult_2.case_0
  pat_unapply h_v50 as ⟨v53, v54, x_v53, x_v54, h_v53, h_v54, hn_v53, hn_v54⟩ using hinv8 else hinv8 hG in EoCases.__eo_prog_bv_mult_slt_mult_2.case_0
  pat_unapply h_v53 as ⟨v56, v57, x_v56, x_v57, h_v56, h_v57, hn_v56, hn_v57⟩ using hinv8 else hinv8 hG in EoCases.__eo_prog_bv_mult_slt_mult_2.case_0
  step as ⟨e_v58, he_v58⟩
  store_step with CtorSpec.eo__3e_3d.construct s8 e_v58 (by rw [he_v58]; exact empty_args) hinv8 h64 as ⟨v58, s9, hinv9, h_v58⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v47 h_v54 h_v56 h_v57 dropping h_v49 h_v50 h_v51 h_v53 he_v58 hinv8 e_v58 s8 v49 v50 v51 v53
  pat_same v56 v58 with h_v56 h_v58 using hinv9 else hinv9 hG in EoCases.__eo_prog_bv_mult_slt_mult_2.case_0
  pat_same v57 a4 with h_v57 h_a4 using hinv9 else hinv9 hG in EoCases.__eo_prog_bv_mult_slt_mult_2.case_0
  pat_same v54 a6 with h_v54 h_a6 using hinv9 else hinv9 hG in EoCases.__eo_prog_bv_mult_slt_mult_2.case_0
  store_step with Store.literal_boolean_spec s9 true hinv9 h64 as ⟨v59, s10, hinv10, h_v59⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v47 dropping h_v54 h_v56 h_v57 h_v58 hinv9 s9 v54 v56 v57 v58
  pat_same v47 v59 with h_v47 h_v59 using hinv10 else hinv10 hG in EoCases.__eo_prog_bv_mult_slt_mult_2.case_0
  step as ⟨e_v60, he_v60⟩
  store_step with CtorSpec.eo__3d.construct s10 e_v60 (by rw [he_v60]; exact empty_args) hinv10 h64 as ⟨v60, s11, hinv11, h_v60⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 dropping h_v47 h_v59 he_v60 hinv10 e_v60 s10 v47 v59
  step as ⟨e_v61, he_v61⟩
  store_step with CtorSpec.eo_bvslt.construct s11 e_v61 (by rw [he_v61]; exact empty_args) hinv11 h64 as ⟨v61, s12, hinv12, h_v61⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v60 dropping he_v61 hinv11 e_v61 s11
  step as ⟨e_v62, he_v62⟩
  store_step with CtorSpec.eo_bvmul.construct s12 e_v62 (by rw [he_v62]; exact empty_args) hinv12 h64 as ⟨v62, s13, hinv13, h_v62⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v60 h_v61 dropping he_v62 hinv12 e_v62 s12
  step as ⟨e_v63, he_v63⟩
  store_step with CtorSpec.eo_zero_5fextend.construct s13 e_v63 (by rw [he_v63]; rfl) h_a3 hinv13 h64 as ⟨v63, s14, hinv14, h_v63⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v60 h_v61 h_v62 dropping he_v63 hinv13 e_v63 s13
  store_step with Store.apply_rep s14 v63 a1 _ _ hinv14 h64 h_v63 h_a1 (by ns_tac) (by ns_tac) as ⟨v64, s15, hinv15, h_v64⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v60 h_v61 h_v62 dropping h_v63 hinv14 s14 v63
  store_step with Store.apply_rep s15 v62 v64 _ _ hinv15 h64 h_v62 h_v64 (by ns_tac) (by ns_tac) as ⟨v65, s16, hinv16, h_v65⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v60 h_v61 dropping h_v62 h_v64 hinv15 s15 v62 v64
  step as ⟨e_v66, he_v66⟩
  store_step with CtorSpec.eo_bvmul.construct s16 e_v66 (by rw [he_v66]; exact empty_args) hinv16 h64 as ⟨v66, s17, hinv17, h_v66⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v60 h_v61 h_v65 dropping he_v66 hinv16 e_v66 s16
  step as ⟨e_v67, he_v67⟩
  store_step with CtorSpec.eo_sign_5fextend.construct s17 e_v67 (by rw [he_v67]; rfl) h_a4 hinv17 h64 as ⟨v67, s18, hinv18, h_v67⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v60 h_v61 h_v65 h_v66 dropping he_v67 hinv17 e_v67 s17
  store_step with Store.apply_rep s18 v67 a2 _ _ hinv18 h64 h_v67 h_a2 (by ns_tac) (by ns_tac) as ⟨v68, s19, hinv19, h_v68⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v60 h_v61 h_v65 h_v66 dropping h_v67 hinv18 s18 v67
  store_step with Store.apply_rep s19 v66 v68 _ _ hinv19 h64 h_v66 h_v68 (by ns_tac) (by ns_tac) as ⟨v69, s20, hinv20, h_v69⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v60 h_v61 h_v65 dropping h_v66 h_v68 hinv19 s19 v66 v68
  step as ⟨e_v70, he_v70⟩
  store_step with CtorSpec.eo_bvmul.construct s20 e_v70 (by rw [he_v70]; exact empty_args) hinv20 h64 as ⟨v70, s21, hinv21, h_v70⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v60 h_v61 h_v65 h_v69 dropping he_v70 hinv20 e_v70 s20
  step as ⟨e_v71, he_v71⟩
  store_step with CtorSpec.eo_zero_5fextend.construct s21 e_v71 (by rw [he_v71]; rfl) h_a3 hinv21 h64 as ⟨v71, s22, hinv22, h_v71⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v60 h_v61 h_v65 h_v69 h_v70 dropping he_v71 hinv21 e_v71 s21
  store_step with Store.apply_rep s22 v71 a1 _ _ hinv22 h64 h_v71 h_a1 (by ns_tac) (by ns_tac) as ⟨v72, s23, hinv23, h_v72⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v60 h_v61 h_v65 h_v69 h_v70 dropping h_v71 hinv22 s22 v71
  store_step with ih.eo__24eo_5ftypeof s23 v72 _ hinv23 h64 (hG.rem hrem) h_v72 as ⟨v73, s24, hinv24, h_v73⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v60 h_v61 h_v65 h_v69 h_v70 dropping h_v72 hinv23 s23 v72
  store_step with ih.eo__24eo_5fnil s24 v70 v73 _ _ hinv24 h64 (hG.rem hrem) h_v70 h_v73 as ⟨v74, s25, hinv25, h_v74⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v60 h_v61 h_v65 h_v69 dropping h_v70 h_v73 hinv24 s24 v70 v73
  store_step with Store.apply_mk_rep s25 v69 v74 _ _ hinv25 h64 h_v69 h_v74 as ⟨v75, s26, hinv26, h_v75⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v60 h_v61 h_v65 dropping h_v69 h_v74 hinv25 s25 v69 v74
  store_step with Store.apply_mk_rep s26 v65 v75 _ _ hinv26 h64 h_v65 h_v75 as ⟨v76, s27, hinv27, h_v76⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v60 h_v61 dropping h_v65 h_v75 hinv26 s26 v65 v75
  store_step with Store.apply_mk_rep s27 v61 v76 _ _ hinv27 h64 h_v61 h_v76 as ⟨v77, s28, hinv28, h_v77⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v60 dropping h_v61 h_v76 hinv27 s27 v61 v76
  step as ⟨e_v78, he_v78⟩
  store_step with CtorSpec.eo_bvmul.construct s28 e_v78 (by rw [he_v78]; exact empty_args) hinv28 h64 as ⟨v78, s29, hinv29, h_v78⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v60 h_v77 dropping he_v78 hinv28 e_v78 s28
  step as ⟨e_v79, he_v79⟩
  store_step with CtorSpec.eo_zero_5fextend.construct s29 e_v79 (by rw [he_v79]; rfl) h_a3 hinv29 h64 as ⟨v79, s30, hinv30, h_v79⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v60 h_v77 h_v78 dropping he_v79 hinv29 e_v79 s29
  store_step with Store.apply_rep s30 v79 a0 _ _ hinv30 h64 h_v79 h_a0 (by ns_tac) (by ns_tac) as ⟨v80, s31, hinv31, h_v80⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v60 h_v77 h_v78 dropping h_v79 hinv30 s30 v79
  store_step with Store.apply_rep s31 v78 v80 _ _ hinv31 h64 h_v78 h_v80 (by ns_tac) (by ns_tac) as ⟨v81, s32, hinv32, h_v81⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v60 h_v77 dropping h_v78 h_v80 hinv31 s31 v78 v80
  step as ⟨e_v82, he_v82⟩
  store_step with CtorSpec.eo_bvmul.construct s32 e_v82 (by rw [he_v82]; exact empty_args) hinv32 h64 as ⟨v82, s33, hinv33, h_v82⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v60 h_v77 h_v81 dropping he_v82 hinv32 e_v82 s32
  step as ⟨e_v83, he_v83⟩
  store_step with CtorSpec.eo_sign_5fextend.construct s33 e_v83 (by rw [he_v83]; rfl) h_a4 hinv33 h64 as ⟨v83, s34, hinv34, h_v83⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a5 h_a6 h_v60 h_v77 h_v81 h_v82 dropping h_a4 he_v83 hinv33 e_v83 s33
  store_step with Store.apply_rep s34 v83 a2 _ _ hinv34 h64 h_v83 h_a2 (by ns_tac) (by ns_tac) as ⟨v84, s35, hinv35, h_v84⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a5 h_a6 h_v60 h_v77 h_v81 h_v82 dropping h_v83 hinv34 s34 v83
  store_step with Store.apply_rep s35 v82 v84 _ _ hinv35 h64 h_v82 h_v84 (by ns_tac) (by ns_tac) as ⟨v85, s36, hinv36, h_v85⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a5 h_a6 h_v60 h_v77 h_v81 dropping h_v82 h_v84 hinv35 s35 v82 v84
  step as ⟨e_v86, he_v86⟩
  store_step with CtorSpec.eo_bvmul.construct s36 e_v86 (by rw [he_v86]; exact empty_args) hinv36 h64 as ⟨v86, s37, hinv37, h_v86⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a5 h_a6 h_v60 h_v77 h_v81 h_v85 dropping he_v86 hinv36 e_v86 s36
  step as ⟨e_v87, he_v87⟩
  store_step with CtorSpec.eo_zero_5fextend.construct s37 e_v87 (by rw [he_v87]; rfl) h_a3 hinv37 h64 as ⟨v87, s38, hinv38, h_v87⟩ growing hG carrying h_a0 h_a1 h_a2 h_a5 h_a6 h_v60 h_v77 h_v81 h_v85 h_v86 dropping h_a3 he_v87 hinv37 e_v87 s37
  store_step with Store.apply_rep s38 v87 a0 _ _ hinv38 h64 h_v87 h_a0 (by ns_tac) (by ns_tac) as ⟨v88, s39, hinv39, h_v88⟩ growing hG carrying h_a0 h_a1 h_a2 h_a5 h_a6 h_v60 h_v77 h_v81 h_v85 h_v86 dropping h_v87 hinv38 s38 v87
  store_step with ih.eo__24eo_5ftypeof s39 v88 _ hinv39 h64 (hG.rem hrem) h_v88 as ⟨v89, s40, hinv40, h_v89⟩ growing hG carrying h_a0 h_a1 h_a2 h_a5 h_a6 h_v60 h_v77 h_v81 h_v85 h_v86 dropping h_v88 hinv39 s39 v88
  store_step with ih.eo__24eo_5fnil s40 v86 v89 _ _ hinv40 h64 (hG.rem hrem) h_v86 h_v89 as ⟨v90, s41, hinv41, h_v90⟩ growing hG carrying h_a0 h_a1 h_a2 h_a5 h_a6 h_v60 h_v77 h_v81 h_v85 dropping h_v86 h_v89 hinv40 s40 v86 v89
  store_step with Store.apply_mk_rep s41 v85 v90 _ _ hinv41 h64 h_v85 h_v90 as ⟨v91, s42, hinv42, h_v91⟩ growing hG carrying h_a0 h_a1 h_a2 h_a5 h_a6 h_v60 h_v77 h_v81 dropping h_v85 h_v90 hinv41 s41 v85 v90
  store_step with Store.apply_mk_rep s42 v81 v91 _ _ hinv42 h64 h_v81 h_v91 as ⟨v92, s43, hinv43, h_v92⟩ growing hG carrying h_a0 h_a1 h_a2 h_a5 h_a6 h_v60 h_v77 dropping h_v81 h_v91 hinv42 s42 v81 v91
  store_step with Store.apply_mk_rep s43 v77 v92 _ _ hinv43 h64 h_v77 h_v92 as ⟨v93, s44, hinv44, h_v93⟩ growing hG carrying h_a0 h_a1 h_a2 h_a5 h_a6 h_v60 dropping h_v77 h_v92 hinv43 s43 v77 v92
  store_step with Store.apply_mk_rep s44 v60 v93 _ _ hinv44 h64 h_v60 h_v93 as ⟨v94, s45, hinv45, h_v94⟩ growing hG carrying h_a0 h_a1 h_a2 h_a5 h_a6 dropping h_v60 h_v93 hinv44 s44 v60 v93
  step as ⟨e_v95, he_v95⟩
  store_step with CtorSpec.eo_and.construct s45 e_v95 (by rw [he_v95]; exact empty_args) hinv45 h64 as ⟨v95, s46, hinv46, h_v95⟩ growing hG carrying h_a0 h_a1 h_a2 h_a5 h_a6 h_v94 dropping he_v95 hinv45 e_v95 s45
  step as ⟨e_v96, he_v96⟩
  store_step with CtorSpec.eo_not.construct s46 e_v96 (by rw [he_v96]; exact empty_args) hinv46 h64 as ⟨v96, s47, hinv47, h_v96⟩ growing hG carrying h_a0 h_a1 h_a2 h_a5 h_a6 h_v94 h_v95 dropping he_v96 hinv46 e_v96 s46
  step as ⟨e_v97, he_v97⟩
  store_step with CtorSpec.eo__3d.construct s47 e_v97 (by rw [he_v97]; exact empty_args) hinv47 h64 as ⟨v97, s48, hinv48, h_v97⟩ growing hG carrying h_a0 h_a1 h_a2 h_a5 h_a6 h_v94 h_v95 h_v96 dropping he_v97 hinv47 e_v97 s47
  step as ⟨e_v98, he_v98⟩
  store_step with CtorSpec.eo_bvsub.construct s48 e_v98 (by rw [he_v98]; exact empty_args) hinv48 h64 as ⟨v98, s49, hinv49, h_v98⟩ growing hG carrying h_a0 h_a1 h_a2 h_a5 h_a6 h_v94 h_v95 h_v96 h_v97 dropping he_v98 hinv48 e_v98 s48
  store_step with Store.apply_rep s49 v98 a1 _ _ hinv49 h64 h_v98 h_a1 (by ns_tac) (by ns_tac) as ⟨v99, s50, hinv50, h_v99⟩ growing hG carrying h_a0 h_a1 h_a2 h_a5 h_a6 h_v94 h_v95 h_v96 h_v97 dropping h_v98 hinv49 s49 v98
  store_step with Store.apply_rep s50 v99 a0 _ _ hinv50 h64 h_v99 h_a0 (by ns_tac) (by ns_tac) as ⟨v100, s51, hinv51, h_v100⟩ growing hG carrying h_a0 h_a1 h_a2 h_a5 h_a6 h_v94 h_v95 h_v96 h_v97 dropping h_v99 hinv50 s50 v99
  store_step with Store.apply_rep s51 v97 v100 _ _ hinv51 h64 h_v97 h_v100 (by ns_tac) (by ns_tac) as ⟨v101, s52, hinv52, h_v101⟩ growing hG carrying h_a0 h_a1 h_a2 h_a5 h_a6 h_v94 h_v95 h_v96 dropping h_v100 h_v97 hinv51 s51 v100 v97
  step as ⟨e_v102, he_v102⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s52 e_v102 (by rw [he_v102]; rfl) h_a5 hinv52 h64 as ⟨v102, s53, hinv53, h_v102⟩ growing hG carrying h_a0 h_a1 h_a2 h_a6 h_v94 h_v95 h_v96 h_v101 dropping h_a5 he_v102 hinv52 e_v102 s52
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s53 0#u32 (0) (by scalar_tac) hinv53 h64 as ⟨v103, s54, hinv54, h_v103⟩ growing hG carrying h_a0 h_a1 h_a2 h_a6 h_v94 h_v95 h_v96 h_v101 h_v102 dropping hinv53 s53
  store_step with Store.apply_rep s54 v102 v103 _ _ hinv54 h64 h_v102 h_v103 (by ns_tac) (by ns_tac) as ⟨v104, s55, hinv55, h_v104⟩ growing hG carrying h_a0 h_a1 h_a2 h_a6 h_v94 h_v95 h_v96 h_v101 dropping h_v102 h_v103 hinv54 s54 v102 v103
  store_step with Store.apply_rep s55 v101 v104 _ _ hinv55 h64 h_v101 h_v104 (by ns_tac) (by ns_tac) as ⟨v105, s56, hinv56, h_v105⟩ growing hG carrying h_a0 h_a1 h_a2 h_a6 h_v94 h_v95 h_v96 dropping h_v101 h_v104 hinv55 s55 v101 v104
  store_step with Store.apply_rep s56 v96 v105 _ _ hinv56 h64 h_v96 h_v105 (by ns_tac) (by ns_tac) as ⟨v106, s57, hinv57, h_v106⟩ growing hG carrying h_a0 h_a1 h_a2 h_a6 h_v94 h_v95 dropping h_v105 h_v96 hinv56 s56 v105 v96
  store_step with Store.apply_rep s57 v95 v106 _ _ hinv57 h64 h_v95 h_v106 (by ns_tac) (by ns_tac) as ⟨v107, s58, hinv58, h_v107⟩ growing hG carrying h_a0 h_a1 h_a2 h_a6 h_v94 dropping h_v106 h_v95 hinv57 s57 v106 v95
  step as ⟨e_v108, he_v108⟩
  store_step with CtorSpec.eo_and.construct s58 e_v108 (by rw [he_v108]; exact empty_args) hinv58 h64 as ⟨v108, s59, hinv59, h_v108⟩ growing hG carrying h_a0 h_a1 h_a2 h_a6 h_v94 h_v107 dropping he_v108 hinv58 e_v108 s58
  step as ⟨e_v109, he_v109⟩
  store_step with CtorSpec.eo_not.construct s59 e_v109 (by rw [he_v109]; exact empty_args) hinv59 h64 as ⟨v109, s60, hinv60, h_v109⟩ growing hG carrying h_a0 h_a1 h_a2 h_a6 h_v94 h_v107 h_v108 dropping he_v109 hinv59 e_v109 s59
  step as ⟨e_v110, he_v110⟩
  store_step with CtorSpec.eo__3d.construct s60 e_v110 (by rw [he_v110]; exact empty_args) hinv60 h64 as ⟨v110, s61, hinv61, h_v110⟩ growing hG carrying h_a0 h_a1 h_a2 h_a6 h_v94 h_v107 h_v108 h_v109 dropping he_v110 hinv60 e_v110 s60
  store_step with Store.apply_rep s61 v110 a2 _ _ hinv61 h64 h_v110 h_a2 (by ns_tac) (by ns_tac) as ⟨v111, s62, hinv62, h_v111⟩ growing hG carrying h_a0 h_a1 h_a2 h_a6 h_v94 h_v107 h_v108 h_v109 dropping h_v110 hinv61 s61 v110
  step as ⟨e_v112, he_v112⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s62 e_v112 (by rw [he_v112]; rfl) h_a6 hinv62 h64 as ⟨v112, s63, hinv63, h_v112⟩ growing hG carrying h_a0 h_a1 h_a2 h_a6 h_v94 h_v107 h_v108 h_v109 h_v111 dropping he_v112 hinv62 e_v112 s62
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s63 0#u32 (0) (by scalar_tac) hinv63 h64 as ⟨v113, s64, hinv64, h_v113⟩ growing hG carrying h_a0 h_a1 h_a2 h_a6 h_v94 h_v107 h_v108 h_v109 h_v111 h_v112 dropping hinv63 s63
  store_step with Store.apply_rep s64 v112 v113 _ _ hinv64 h64 h_v112 h_v113 (by ns_tac) (by ns_tac) as ⟨v114, s65, hinv65, h_v114⟩ growing hG carrying h_a0 h_a1 h_a2 h_a6 h_v94 h_v107 h_v108 h_v109 h_v111 dropping h_v112 h_v113 hinv64 s64 v112 v113
  store_step with Store.apply_rep s65 v111 v114 _ _ hinv65 h64 h_v111 h_v114 (by ns_tac) (by ns_tac) as ⟨v115, s66, hinv66, h_v115⟩ growing hG carrying h_a0 h_a1 h_a2 h_a6 h_v94 h_v107 h_v108 h_v109 dropping h_v111 h_v114 hinv65 s65 v111 v114
  store_step with Store.apply_rep s66 v109 v115 _ _ hinv66 h64 h_v109 h_v115 (by ns_tac) (by ns_tac) as ⟨v116, s67, hinv67, h_v116⟩ growing hG carrying h_a0 h_a1 h_a2 h_a6 h_v94 h_v107 h_v108 dropping h_v109 h_v115 hinv66 s66 v109 v115
  store_step with Store.apply_rep s67 v108 v116 _ _ hinv67 h64 h_v108 h_v116 (by ns_tac) (by ns_tac) as ⟨v117, s68, hinv68, h_v117⟩ growing hG carrying h_a0 h_a1 h_a2 h_a6 h_v94 h_v107 dropping h_v108 h_v116 hinv67 s67 v108 v116
  step as ⟨e_v118, he_v118⟩
  store_step with CtorSpec.eo_and.construct s68 e_v118 (by rw [he_v118]; exact empty_args) hinv68 h64 as ⟨v118, s69, hinv69, h_v118⟩ growing hG carrying h_a0 h_a1 h_a2 h_a6 h_v94 h_v107 h_v117 dropping he_v118 hinv68 e_v118 s68
  step as ⟨e_v119, he_v119⟩
  store_step with CtorSpec.eo__3d.construct s69 e_v119 (by rw [he_v119]; exact empty_args) hinv69 h64 as ⟨v119, s70, hinv70, h_v119⟩ growing hG carrying h_a0 h_a1 h_a2 h_a6 h_v94 h_v107 h_v117 h_v118 dropping he_v119 hinv69 e_v119 s69
  step as ⟨e_v120, he_v120⟩
  store_step with CtorSpec.eo_bvult.construct s70 e_v120 (by rw [he_v120]; exact empty_args) hinv70 h64 as ⟨v120, s71, hinv71, h_v120⟩ growing hG carrying h_a0 h_a1 h_a2 h_a6 h_v94 h_v107 h_v117 h_v118 h_v119 dropping he_v120 hinv70 e_v120 s70
  store_step with Store.apply_rep s71 v120 a1 _ _ hinv71 h64 h_v120 h_a1 (by ns_tac) (by ns_tac) as ⟨v121, s72, hinv72, h_v121⟩ growing hG carrying h_a0 h_a2 h_a6 h_v94 h_v107 h_v117 h_v118 h_v119 dropping h_a1 h_v120 hinv71 s71 v120
  store_step with Store.apply_rep s72 v121 a0 _ _ hinv72 h64 h_v121 h_a0 (by ns_tac) (by ns_tac) as ⟨v122, s73, hinv73, h_v122⟩ growing hG carrying h_a2 h_a6 h_v94 h_v107 h_v117 h_v118 h_v119 dropping h_a0 h_v121 hinv72 s72 v121
  store_step with Store.apply_rep s73 v119 v122 _ _ hinv73 h64 h_v119 h_v122 (by ns_tac) (by ns_tac) as ⟨v123, s74, hinv74, h_v123⟩ growing hG carrying h_a2 h_a6 h_v94 h_v107 h_v117 h_v118 dropping h_v119 h_v122 hinv73 s73 v119 v122
  step as ⟨e_v124, he_v124⟩
  store_step with CtorSpec.eo_bvsgt.construct s74 e_v124 (by rw [he_v124]; exact empty_args) hinv74 h64 as ⟨v124, s75, hinv75, h_v124⟩ growing hG carrying h_a2 h_a6 h_v94 h_v107 h_v117 h_v118 h_v123 dropping he_v124 hinv74 e_v124 s74
  store_step with Store.apply_rep s75 v124 a2 _ _ hinv75 h64 h_v124 h_a2 (by ns_tac) (by ns_tac) as ⟨v125, s76, hinv76, h_v125⟩ growing hG carrying h_a6 h_v94 h_v107 h_v117 h_v118 h_v123 dropping h_a2 h_v124 hinv75 s75 v124
  step as ⟨e_v126, he_v126⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s76 e_v126 (by rw [he_v126]; rfl) h_a6 hinv76 h64 as ⟨v126, s77, hinv77, h_v126⟩ growing hG carrying h_v94 h_v107 h_v117 h_v118 h_v123 h_v125 dropping h_a6 he_v126 hinv76 e_v126 s76
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s77 0#u32 (0) (by scalar_tac) hinv77 h64 as ⟨v127, s78, hinv78, h_v127⟩ growing hG carrying h_v94 h_v107 h_v117 h_v118 h_v123 h_v125 h_v126 dropping hinv77 s77
  store_step with Store.apply_rep s78 v126 v127 _ _ hinv78 h64 h_v126 h_v127 (by ns_tac) (by ns_tac) as ⟨v128, s79, hinv79, h_v128⟩ growing hG carrying h_v94 h_v107 h_v117 h_v118 h_v123 h_v125 dropping h_v126 h_v127 hinv78 s78 v126 v127
  store_step with Store.apply_rep s79 v125 v128 _ _ hinv79 h64 h_v125 h_v128 (by ns_tac) (by ns_tac) as ⟨v129, s80, hinv80, h_v129⟩ growing hG carrying h_v94 h_v107 h_v117 h_v118 h_v123 dropping h_v125 h_v128 hinv79 s79 v125 v128
  store_step with Store.apply_rep s80 v123 v129 _ _ hinv80 h64 h_v123 h_v129 (by ns_tac) (by ns_tac) as ⟨v130, s81, hinv81, h_v130⟩ growing hG carrying h_v94 h_v107 h_v117 h_v118 dropping h_v123 h_v129 hinv80 s80 v123 v129
  store_step with Store.apply_rep s81 v118 v130 _ _ hinv81 h64 h_v118 h_v130 (by ns_tac) (by ns_tac) as ⟨v131, s82, hinv82, h_v131⟩ growing hG carrying h_v94 h_v107 h_v117 dropping h_v118 h_v130 hinv81 s81 v118 v130
  store_step with Store.literal_boolean_spec s82 true hinv82 h64 as ⟨v132, s83, hinv83, h_v132⟩ growing hG carrying h_v94 h_v107 h_v117 h_v131 dropping hinv82 s82
  store_step with Store.apply_rep s83 v131 v132 _ _ hinv83 h64 h_v131 h_v132 (by ns_tac) (by ns_tac) as ⟨v133, s84, hinv84, h_v133⟩ growing hG carrying h_v94 h_v107 h_v117 dropping h_v131 h_v132 hinv83 s83 v131 v132
  store_step with Store.apply_rep s84 v117 v133 _ _ hinv84 h64 h_v117 h_v133 (by ns_tac) (by ns_tac) as ⟨v134, s85, hinv85, h_v134⟩ growing hG carrying h_v94 h_v107 dropping h_v117 h_v133 hinv84 s84 v117 v133
  store_step with Store.apply_rep s85 v107 v134 _ _ hinv85 h64 h_v107 h_v134 (by ns_tac) (by ns_tac) as ⟨v135, s86, hinv86, h_v135⟩ growing hG carrying h_v94 dropping h_v107 h_v134 hinv85 s85 v107 v134
  store_step with Store.apply_mk_rep s86 v94 v135 _ _ hinv86 h64 h_v94 h_v135 as ⟨v136, s87, hinv87, h_v136⟩ growing hG carrying dropping h_v135 h_v94 hinv86 s86 v135 v94
  case_done hinv87 hG with h_v136 in EoCases.__eo_prog_bv_mult_slt_mult_2.case_0 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_a5 hn_a6 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v16 hn_v17 hn_v19 hn_v20 hn_v23 hn_v24 hn_v29 hn_v30 hn_v32 hn_v33 hn_v36 hn_v37 hn_v39 hn_v40 hn_v46 hn_v47 hn_v49 hn_v50 hn_v53 hn_v54 hn_v56 hn_v57

/-- logos's `__eo_prog_bv_mult_slt_mult_2` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fbv_2dmult_2dslt_2dmult_2d2.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _) (x_a7 : _) (x_a8 : _) (x_a9 : _) (x_a10 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) (hw_a4 : Valid.valid x_a4) (hw_a5 : Valid.valid x_a5) (hw_a6 : Valid.valid x_a6) (hw_a7 : Valid.valid x_a7) (hw_a8 : Valid.valid x_a8) (hw_a9 : Valid.valid x_a9) (hw_a10 : Valid.valid x_a10) :
    __eo_prog_bv_mult_slt_mult_2 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 x_a9 x_a10 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else if x_a4 = Eo.Term.Stuck then HasStuck.stuck else if x_a5 = Eo.Term.Stuck then HasStuck.stuck else if x_a6 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_bv_mult_slt_mult_2.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 x_a9 x_a10] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_bv_mult_slt_mult_2
  unfold EoCases.__eo_prog_bv_mult_slt_mult_2.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fbv_2dmult_2dslt_2dmult_2d2_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _) (x_a7 : _) (x_a8 : _) (x_a9 : _) (x_a10 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) (h_a6 : Represents.rep s a6 x_a6) (h_a7 : Represents.rep s a7 x_a7) (h_a8 : Represents.rep s a8 x_a8) (h_a9 : Represents.rep s a9 x_a9) (h_a10 : Represents.rep s a10 x_a10) :
    body_eo__24eo_5fprog_5fbv_2dmult_2dslt_2dmult_2d2 s a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_mult_slt_mult_2 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 x_a9 x_a10)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fbv_2dmult_2dslt_2dmult_2d2.rust_eq x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 x_a9 x_a10 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3) (by valid_tac hinv h_a4) (by valid_tac hinv h_a5) (by valid_tac hinv h_a6) (by valid_tac hinv h_a7) (by valid_tac hinv h_a8) (by valid_tac hinv h_a9) (by valid_tac hinv h_a10)]
  unfold body_eo__24eo_5fprog_5fbv_2dmult_2dslt_2dmult_2d2
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  stuck_check h_a3 : x_a3 as hn_a3 else hinv hG
  stuck_check h_a4 : x_a4 as hn_a4 else hinv hG
  stuck_check h_a5 : x_a5 as hn_a5 else hinv hG
  stuck_check h_a6 : x_a6 as hn_a6 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fbv_2dmult_2dslt_2dmult_2d2_spec n ih s a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 x_a9 x_a10 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 h_a9 h_a10 hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_a5 hn_a6
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 h_a9 h_a10 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_a5 hn_a6
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_a5 hn_a6 hc0 in EoCases.__eo_prog_bv_mult_slt_mult_2.case_0

theorem eo__24eo_5fprog_5fbv_2dmult_2dslt_2dmult_2d2_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fbv_2dmult_2dslt_2dmult_2d2.Spec n := by
  intro s a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 x_a9 x_a10 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 h_a9 h_a10
  unfold eo__24eo_5fprog_5fbv_2dmult_2dslt_2dmult_2d2
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fbv_2dmult_2dslt_2dmult_2d2 s1 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10) (fun s' t => Represents.rep s' t (__eo_prog_bv_mult_slt_mult_2 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 x_a9 x_a10))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fbv_2dmult_2dslt_2dmult_2d2_spec m (ih m hm) s1 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 x_a9 x_a10 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn) (by congr_one h_a4 hn) (by congr_one h_a5 hn) (by congr_one h_a6 hn) (by congr_one h_a7 hn) (by congr_one h_a8 hn) (by congr_one h_a9 hn) (by congr_one h_a10 hn)))
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

set_option maxHeartbeats 3510000 in
theorem case_0_eo__24eo_5fprog_5fbv_2dsaddo_2deliminate_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fbv_2dsaddo_2deliminate s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_bv_saddo_eliminate.case_0 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_bv_saddo_eliminate.case_0 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fbv_2dsaddo_2deliminate
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a3 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_bv_saddo_eliminate.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_saddo_eliminate.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_saddo_eliminate.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_v4 h_v6 h_v7 dropping h_a3 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_saddo_eliminate.case_0
  pat_same v7 a2 with h_v7 h_a2 using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_saddo_eliminate.case_0
  pat_unapply h_v4 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_saddo_eliminate.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_saddo_eliminate.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__2d.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_v11 h_v13 h_v14 dropping h_v10 h_v4 h_v6 h_v7 h_v8 he_v15 hinv1 e_v15 s1 v10 v4 v6 v7 v8
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_saddo_eliminate.case_0
  pat_unapply h_v14 as ⟨v17, v18, x_v17, x_v18, h_v17, h_v18, hn_v17, hn_v18⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_saddo_eliminate.case_0
  step as ⟨e_v19, he_v19⟩
  store_step with CtorSpec.eo__40bvsize.construct s2 e_v19 (by rw [he_v19]; exact empty_args) hinv2 h64 as ⟨v19, s3, hinv3, h_v19⟩ growing hG carrying h_a0 h_a1 h_a2 h_v11 h_v17 h_v18 dropping h_v13 h_v14 h_v15 he_v19 hinv2 e_v19 s2 v13 v14 v15
  pat_same v17 v19 with h_v17 h_v19 using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_saddo_eliminate.case_0
  pat_same v18 a0 with h_v18 h_a0 using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_saddo_eliminate.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s3 1#u32 (1) (by scalar_tac) hinv3 h64 as ⟨v20, s4, hinv4, h_v20⟩ growing hG carrying h_a0 h_a1 h_a2 h_v11 dropping h_v17 h_v18 h_v19 hinv3 s3 v17 v18 v19
  pat_same v11 v20 with h_v11 h_v20 using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_saddo_eliminate.case_0
  step as ⟨e_v21, he_v21⟩
  store_step with CtorSpec.eo__3d.construct s4 e_v21 (by rw [he_v21]; exact empty_args) hinv4 h64 as ⟨v21, s5, hinv5, h_v21⟩ growing hG carrying h_a0 h_a1 h_a2 dropping h_v11 h_v20 he_v21 hinv4 e_v21 s4 v11 v20
  step as ⟨e_v22, he_v22⟩
  store_step with CtorSpec.eo_bvsaddo.construct s5 e_v22 (by rw [he_v22]; exact empty_args) hinv5 h64 as ⟨v22, s6, hinv6, h_v22⟩ growing hG carrying h_a0 h_a1 h_a2 h_v21 dropping he_v22 hinv5 e_v22 s5
  store_step with Store.apply_rep s6 v22 a0 _ _ hinv6 h64 h_v22 h_a0 (by ns_tac) (by ns_tac) as ⟨v23, s7, hinv7, h_v23⟩ growing hG carrying h_a0 h_a1 h_a2 h_v21 dropping h_v22 hinv6 s6 v22
  store_step with Store.apply_rep s7 v23 a1 _ _ hinv7 h64 h_v23 h_a1 (by ns_tac) (by ns_tac) as ⟨v24, s8, hinv8, h_v24⟩ growing hG carrying h_a0 h_a1 h_a2 h_v21 dropping h_v23 hinv7 s7 v23
  store_step with Store.apply_rep s8 v21 v24 _ _ hinv8 h64 h_v21 h_v24 (by ns_tac) (by ns_tac) as ⟨v25, s9, hinv9, h_v25⟩ growing hG carrying h_a0 h_a1 h_a2 dropping h_v21 h_v24 hinv8 s8 v21 v24
  step as ⟨e_v26, he_v26⟩
  store_step with CtorSpec.eo_or.construct s9 e_v26 (by rw [he_v26]; exact empty_args) hinv9 h64 as ⟨v26, s10, hinv10, h_v26⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 dropping he_v26 hinv9 e_v26 s9
  step as ⟨e_v27, he_v27⟩
  store_step with CtorSpec.eo_and.construct s10 e_v27 (by rw [he_v27]; exact empty_args) hinv10 h64 as ⟨v27, s11, hinv11, h_v27⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 dropping he_v27 hinv10 e_v27 s10
  step as ⟨e_v28, he_v28⟩
  store_step with CtorSpec.eo_and.construct s11 e_v28 (by rw [he_v28]; exact empty_args) hinv11 h64 as ⟨v28, s12, hinv12, h_v28⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 h_v27 dropping he_v28 hinv11 e_v28 s11
  step as ⟨e_v29, he_v29⟩
  store_step with CtorSpec.eo__3d.construct s12 e_v29 (by rw [he_v29]; exact empty_args) hinv12 h64 as ⟨v29, s13, hinv13, h_v29⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 h_v27 h_v28 dropping he_v29 hinv12 e_v29 s12
  step as ⟨e_v30, he_v30⟩
  store_step with CtorSpec.eo_extract.construct s13 e_v30 (by rw [he_v30]; rfl) h_a2 h_a2 hinv13 h64 as ⟨v30, s14, hinv14, h_v30⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 h_v27 h_v28 h_v29 dropping he_v30 hinv13 e_v30 s13
  store_step with Store.apply_rep s14 v30 a0 _ _ hinv14 h64 h_v30 h_a0 (by ns_tac) (by ns_tac) as ⟨v31, s15, hinv15, h_v31⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 h_v27 h_v28 h_v29 dropping h_v30 hinv14 s14 v30
  store_step with Store.apply_rep s15 v29 v31 _ _ hinv15 h64 h_v29 h_v31 (by ns_tac) (by ns_tac) as ⟨v32, s16, hinv16, h_v32⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 h_v27 h_v28 dropping h_v29 h_v31 hinv15 s15 v29 v31
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s16 1#u32 (1) (by scalar_tac) hinv16 h64 as ⟨v33, s17, hinv17, h_v33⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 h_v27 h_v28 h_v32 dropping hinv16 s16
  step as ⟨e_v34, he_v34⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s17 e_v34 (by rw [he_v34]; rfl) h_v33 hinv17 h64 as ⟨v34, s18, hinv18, h_v34⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 h_v27 h_v28 h_v32 dropping h_v33 he_v34 hinv17 e_v34 s17 v33
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s18 1#u32 (1) (by scalar_tac) hinv18 h64 as ⟨v35, s19, hinv19, h_v35⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 h_v27 h_v28 h_v32 h_v34 dropping hinv18 s18
  store_step with Store.apply_rep s19 v34 v35 _ _ hinv19 h64 h_v34 h_v35 (by ns_tac) (by ns_tac) as ⟨v36, s20, hinv20, h_v36⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 h_v27 h_v28 h_v32 dropping h_v34 h_v35 hinv19 s19 v34 v35
  store_step with Store.apply_rep s20 v32 v36 _ _ hinv20 h64 h_v32 h_v36 (by ns_tac) (by ns_tac) as ⟨v37, s21, hinv21, h_v37⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 h_v27 h_v28 dropping h_v32 h_v36 hinv20 s20 v32 v36
  store_step with Store.apply_rep s21 v28 v37 _ _ hinv21 h64 h_v28 h_v37 (by ns_tac) (by ns_tac) as ⟨v38, s22, hinv22, h_v38⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 h_v27 dropping h_v28 h_v37 hinv21 s21 v28 v37
  step as ⟨e_v39, he_v39⟩
  store_step with CtorSpec.eo_and.construct s22 e_v39 (by rw [he_v39]; exact empty_args) hinv22 h64 as ⟨v39, s23, hinv23, h_v39⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 h_v27 h_v38 dropping he_v39 hinv22 e_v39 s22
  step as ⟨e_v40, he_v40⟩
  store_step with CtorSpec.eo__3d.construct s23 e_v40 (by rw [he_v40]; exact empty_args) hinv23 h64 as ⟨v40, s24, hinv24, h_v40⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 h_v27 h_v38 h_v39 dropping he_v40 hinv23 e_v40 s23
  step as ⟨e_v41, he_v41⟩
  store_step with CtorSpec.eo_extract.construct s24 e_v41 (by rw [he_v41]; rfl) h_a2 h_a2 hinv24 h64 as ⟨v41, s25, hinv25, h_v41⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 h_v27 h_v38 h_v39 h_v40 dropping he_v41 hinv24 e_v41 s24
  store_step with Store.apply_rep s25 v41 a1 _ _ hinv25 h64 h_v41 h_a1 (by ns_tac) (by ns_tac) as ⟨v42, s26, hinv26, h_v42⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 h_v27 h_v38 h_v39 h_v40 dropping h_v41 hinv25 s25 v41
  store_step with Store.apply_rep s26 v40 v42 _ _ hinv26 h64 h_v40 h_v42 (by ns_tac) (by ns_tac) as ⟨v43, s27, hinv27, h_v43⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 h_v27 h_v38 h_v39 dropping h_v40 h_v42 hinv26 s26 v40 v42
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s27 1#u32 (1) (by scalar_tac) hinv27 h64 as ⟨v44, s28, hinv28, h_v44⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 h_v27 h_v38 h_v39 h_v43 dropping hinv27 s27
  step as ⟨e_v45, he_v45⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s28 e_v45 (by rw [he_v45]; rfl) h_v44 hinv28 h64 as ⟨v45, s29, hinv29, h_v45⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 h_v27 h_v38 h_v39 h_v43 dropping h_v44 he_v45 hinv28 e_v45 s28 v44
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s29 1#u32 (1) (by scalar_tac) hinv29 h64 as ⟨v46, s30, hinv30, h_v46⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 h_v27 h_v38 h_v39 h_v43 h_v45 dropping hinv29 s29
  store_step with Store.apply_rep s30 v45 v46 _ _ hinv30 h64 h_v45 h_v46 (by ns_tac) (by ns_tac) as ⟨v47, s31, hinv31, h_v47⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 h_v27 h_v38 h_v39 h_v43 dropping h_v45 h_v46 hinv30 s30 v45 v46
  store_step with Store.apply_rep s31 v43 v47 _ _ hinv31 h64 h_v43 h_v47 (by ns_tac) (by ns_tac) as ⟨v48, s32, hinv32, h_v48⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 h_v27 h_v38 h_v39 dropping h_v43 h_v47 hinv31 s31 v43 v47
  store_step with Store.apply_rep s32 v39 v48 _ _ hinv32 h64 h_v39 h_v48 (by ns_tac) (by ns_tac) as ⟨v49, s33, hinv33, h_v49⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 h_v27 h_v38 dropping h_v39 h_v48 hinv32 s32 v39 v48
  store_step with Store.literal_boolean_spec s33 true hinv33 h64 as ⟨v50, s34, hinv34, h_v50⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 h_v27 h_v38 h_v49 dropping hinv33 s33
  store_step with Store.apply_rep s34 v49 v50 _ _ hinv34 h64 h_v49 h_v50 (by ns_tac) (by ns_tac) as ⟨v51, s35, hinv35, h_v51⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 h_v27 h_v38 dropping h_v49 h_v50 hinv34 s34 v49 v50
  store_step with Store.apply_rep s35 v38 v51 _ _ hinv35 h64 h_v38 h_v51 (by ns_tac) (by ns_tac) as ⟨v52, s36, hinv36, h_v52⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 h_v27 dropping h_v38 h_v51 hinv35 s35 v38 v51
  store_step with Store.apply_rep s36 v27 v52 _ _ hinv36 h64 h_v27 h_v52 (by ns_tac) (by ns_tac) as ⟨v53, s37, hinv37, h_v53⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 dropping h_v27 h_v52 hinv36 s36 v27 v52
  step as ⟨e_v54, he_v54⟩
  store_step with CtorSpec.eo_and.construct s37 e_v54 (by rw [he_v54]; exact empty_args) hinv37 h64 as ⟨v54, s38, hinv38, h_v54⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 h_v53 dropping he_v54 hinv37 e_v54 s37
  step as ⟨e_v55, he_v55⟩
  store_step with CtorSpec.eo__3d.construct s38 e_v55 (by rw [he_v55]; exact empty_args) hinv38 h64 as ⟨v55, s39, hinv39, h_v55⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 h_v53 h_v54 dropping he_v55 hinv38 e_v55 s38
  step as ⟨e_v56, he_v56⟩
  store_step with CtorSpec.eo_extract.construct s39 e_v56 (by rw [he_v56]; rfl) h_a2 h_a2 hinv39 h64 as ⟨v56, s40, hinv40, h_v56⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 h_v53 h_v54 h_v55 dropping he_v56 hinv39 e_v56 s39
  step as ⟨e_v57, he_v57⟩
  store_step with CtorSpec.eo_bvadd.construct s40 e_v57 (by rw [he_v57]; exact empty_args) hinv40 h64 as ⟨v57, s41, hinv41, h_v57⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 h_v53 h_v54 h_v55 h_v56 dropping he_v57 hinv40 e_v57 s40
  store_step with Store.apply_rep s41 v57 a0 _ _ hinv41 h64 h_v57 h_a0 (by ns_tac) (by ns_tac) as ⟨v58, s42, hinv42, h_v58⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 h_v53 h_v54 h_v55 h_v56 dropping h_v57 hinv41 s41 v57
  step as ⟨e_v59, he_v59⟩
  store_step with CtorSpec.eo_bvadd.construct s42 e_v59 (by rw [he_v59]; exact empty_args) hinv42 h64 as ⟨v59, s43, hinv43, h_v59⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 h_v53 h_v54 h_v55 h_v56 h_v58 dropping he_v59 hinv42 e_v59 s42
  store_step with Store.apply_rep s43 v59 a1 _ _ hinv43 h64 h_v59 h_a1 (by ns_tac) (by ns_tac) as ⟨v60, s44, hinv44, h_v60⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 h_v53 h_v54 h_v55 h_v56 h_v58 dropping h_v59 hinv43 s43 v59
  step as ⟨e_v61, he_v61⟩
  store_step with CtorSpec.eo_bvadd.construct s44 e_v61 (by rw [he_v61]; exact empty_args) hinv44 h64 as ⟨v61, s45, hinv45, h_v61⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 h_v53 h_v54 h_v55 h_v56 h_v58 h_v60 dropping he_v61 hinv44 e_v61 s44
  store_step with ih.eo__24eo_5ftypeof s45 a0 _ hinv45 h64 (hG.rem hrem) h_a0 as ⟨v62, s46, hinv46, h_v62⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 h_v53 h_v54 h_v55 h_v56 h_v58 h_v60 h_v61 dropping hinv45 s45
  store_step with ih.eo__24eo_5fnil s46 v61 v62 _ _ hinv46 h64 (hG.rem hrem) h_v61 h_v62 as ⟨v63, s47, hinv47, h_v63⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 h_v53 h_v54 h_v55 h_v56 h_v58 h_v60 dropping h_v61 h_v62 hinv46 s46 v61 v62
  store_step with Store.apply_mk_rep s47 v60 v63 _ _ hinv47 h64 h_v60 h_v63 as ⟨v64, s48, hinv48, h_v64⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 h_v53 h_v54 h_v55 h_v56 h_v58 dropping h_v60 h_v63 hinv47 s47 v60 v63
  store_step with Store.apply_mk_rep s48 v58 v64 _ _ hinv48 h64 h_v58 h_v64 as ⟨v65, s49, hinv49, h_v65⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 h_v53 h_v54 h_v55 h_v56 dropping h_v58 h_v64 hinv48 s48 v58 v64
  store_step with Store.apply_mk_rep s49 v56 v65 _ _ hinv49 h64 h_v56 h_v65 as ⟨v66, s50, hinv50, h_v66⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 h_v53 h_v54 h_v55 dropping h_v56 h_v65 hinv49 s49 v56 v65
  store_step with Store.apply_mk_rep s50 v55 v66 _ _ hinv50 h64 h_v55 h_v66 as ⟨v67, s51, hinv51, h_v67⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 h_v53 h_v54 dropping h_v55 h_v66 hinv50 s50 v55 v66
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s51 1#u32 (1) (by scalar_tac) hinv51 h64 as ⟨v68, s52, hinv52, h_v68⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 h_v53 h_v54 h_v67 dropping hinv51 s51
  step as ⟨e_v69, he_v69⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s52 e_v69 (by rw [he_v69]; rfl) h_v68 hinv52 h64 as ⟨v69, s53, hinv53, h_v69⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 h_v53 h_v54 h_v67 dropping h_v68 he_v69 hinv52 e_v69 s52 v68
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s53 0#u32 (0) (by scalar_tac) hinv53 h64 as ⟨v70, s54, hinv54, h_v70⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 h_v53 h_v54 h_v67 h_v69 dropping hinv53 s53
  store_step with Store.apply_rep s54 v69 v70 _ _ hinv54 h64 h_v69 h_v70 (by ns_tac) (by ns_tac) as ⟨v71, s55, hinv55, h_v71⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 h_v53 h_v54 h_v67 dropping h_v69 h_v70 hinv54 s54 v69 v70
  store_step with Store.apply_mk_rep s55 v67 v71 _ _ hinv55 h64 h_v67 h_v71 as ⟨v72, s56, hinv56, h_v72⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 h_v53 h_v54 dropping h_v67 h_v71 hinv55 s55 v67 v71
  store_step with Store.apply_mk_rep s56 v54 v72 _ _ hinv56 h64 h_v54 h_v72 as ⟨v73, s57, hinv57, h_v73⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 h_v53 dropping h_v54 h_v72 hinv56 s56 v54 v72
  store_step with Store.literal_boolean_spec s57 true hinv57 h64 as ⟨v74, s58, hinv58, h_v74⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 h_v53 h_v73 dropping hinv57 s57
  store_step with Store.apply_mk_rep s58 v73 v74 _ _ hinv58 h64 h_v73 h_v74 as ⟨v75, s59, hinv59, h_v75⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 h_v53 dropping h_v73 h_v74 hinv58 s58 v73 v74
  store_step with Store.apply_mk_rep s59 v53 v75 _ _ hinv59 h64 h_v53 h_v75 as ⟨v76, s60, hinv60, h_v76⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 dropping h_v53 h_v75 hinv59 s59 v53 v75
  store_step with Store.apply_mk_rep s60 v26 v76 _ _ hinv60 h64 h_v26 h_v76 as ⟨v77, s61, hinv61, h_v77⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 dropping h_v26 h_v76 hinv60 s60 v26 v76
  step as ⟨e_v78, he_v78⟩
  store_step with CtorSpec.eo_or.construct s61 e_v78 (by rw [he_v78]; exact empty_args) hinv61 h64 as ⟨v78, s62, hinv62, h_v78⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v77 dropping he_v78 hinv61 e_v78 s61
  step as ⟨e_v79, he_v79⟩
  store_step with CtorSpec.eo_and.construct s62 e_v79 (by rw [he_v79]; exact empty_args) hinv62 h64 as ⟨v79, s63, hinv63, h_v79⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v77 h_v78 dropping he_v79 hinv62 e_v79 s62
  step as ⟨e_v80, he_v80⟩
  store_step with CtorSpec.eo_and.construct s63 e_v80 (by rw [he_v80]; exact empty_args) hinv63 h64 as ⟨v80, s64, hinv64, h_v80⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v77 h_v78 h_v79 dropping he_v80 hinv63 e_v80 s63
  step as ⟨e_v81, he_v81⟩
  store_step with CtorSpec.eo__3d.construct s64 e_v81 (by rw [he_v81]; exact empty_args) hinv64 h64 as ⟨v81, s65, hinv65, h_v81⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v77 h_v78 h_v79 h_v80 dropping he_v81 hinv64 e_v81 s64
  step as ⟨e_v82, he_v82⟩
  store_step with CtorSpec.eo_extract.construct s65 e_v82 (by rw [he_v82]; rfl) h_a2 h_a2 hinv65 h64 as ⟨v82, s66, hinv66, h_v82⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v77 h_v78 h_v79 h_v80 h_v81 dropping he_v82 hinv65 e_v82 s65
  store_step with Store.apply_rep s66 v82 a0 _ _ hinv66 h64 h_v82 h_a0 (by ns_tac) (by ns_tac) as ⟨v83, s67, hinv67, h_v83⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v77 h_v78 h_v79 h_v80 h_v81 dropping h_v82 hinv66 s66 v82
  store_step with Store.apply_rep s67 v81 v83 _ _ hinv67 h64 h_v81 h_v83 (by ns_tac) (by ns_tac) as ⟨v84, s68, hinv68, h_v84⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v77 h_v78 h_v79 h_v80 dropping h_v81 h_v83 hinv67 s67 v81 v83
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s68 1#u32 (1) (by scalar_tac) hinv68 h64 as ⟨v85, s69, hinv69, h_v85⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v77 h_v78 h_v79 h_v80 h_v84 dropping hinv68 s68
  step as ⟨e_v86, he_v86⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s69 e_v86 (by rw [he_v86]; rfl) h_v85 hinv69 h64 as ⟨v86, s70, hinv70, h_v86⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v77 h_v78 h_v79 h_v80 h_v84 dropping h_v85 he_v86 hinv69 e_v86 s69 v85
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s70 0#u32 (0) (by scalar_tac) hinv70 h64 as ⟨v87, s71, hinv71, h_v87⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v77 h_v78 h_v79 h_v80 h_v84 h_v86 dropping hinv70 s70
  store_step with Store.apply_rep s71 v86 v87 _ _ hinv71 h64 h_v86 h_v87 (by ns_tac) (by ns_tac) as ⟨v88, s72, hinv72, h_v88⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v77 h_v78 h_v79 h_v80 h_v84 dropping h_v86 h_v87 hinv71 s71 v86 v87
  store_step with Store.apply_rep s72 v84 v88 _ _ hinv72 h64 h_v84 h_v88 (by ns_tac) (by ns_tac) as ⟨v89, s73, hinv73, h_v89⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v77 h_v78 h_v79 h_v80 dropping h_v84 h_v88 hinv72 s72 v84 v88
  store_step with Store.apply_rep s73 v80 v89 _ _ hinv73 h64 h_v80 h_v89 (by ns_tac) (by ns_tac) as ⟨v90, s74, hinv74, h_v90⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v77 h_v78 h_v79 dropping h_v80 h_v89 hinv73 s73 v80 v89
  step as ⟨e_v91, he_v91⟩
  store_step with CtorSpec.eo_and.construct s74 e_v91 (by rw [he_v91]; exact empty_args) hinv74 h64 as ⟨v91, s75, hinv75, h_v91⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v77 h_v78 h_v79 h_v90 dropping he_v91 hinv74 e_v91 s74
  step as ⟨e_v92, he_v92⟩
  store_step with CtorSpec.eo__3d.construct s75 e_v92 (by rw [he_v92]; exact empty_args) hinv75 h64 as ⟨v92, s76, hinv76, h_v92⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v77 h_v78 h_v79 h_v90 h_v91 dropping he_v92 hinv75 e_v92 s75
  step as ⟨e_v93, he_v93⟩
  store_step with CtorSpec.eo_extract.construct s76 e_v93 (by rw [he_v93]; rfl) h_a2 h_a2 hinv76 h64 as ⟨v93, s77, hinv77, h_v93⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v77 h_v78 h_v79 h_v90 h_v91 h_v92 dropping he_v93 hinv76 e_v93 s76
  store_step with Store.apply_rep s77 v93 a1 _ _ hinv77 h64 h_v93 h_a1 (by ns_tac) (by ns_tac) as ⟨v94, s78, hinv78, h_v94⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v77 h_v78 h_v79 h_v90 h_v91 h_v92 dropping h_v93 hinv77 s77 v93
  store_step with Store.apply_rep s78 v92 v94 _ _ hinv78 h64 h_v92 h_v94 (by ns_tac) (by ns_tac) as ⟨v95, s79, hinv79, h_v95⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v77 h_v78 h_v79 h_v90 h_v91 dropping h_v92 h_v94 hinv78 s78 v92 v94
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s79 1#u32 (1) (by scalar_tac) hinv79 h64 as ⟨v96, s80, hinv80, h_v96⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v77 h_v78 h_v79 h_v90 h_v91 h_v95 dropping hinv79 s79
  step as ⟨e_v97, he_v97⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s80 e_v97 (by rw [he_v97]; rfl) h_v96 hinv80 h64 as ⟨v97, s81, hinv81, h_v97⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v77 h_v78 h_v79 h_v90 h_v91 h_v95 dropping h_v96 he_v97 hinv80 e_v97 s80 v96
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s81 0#u32 (0) (by scalar_tac) hinv81 h64 as ⟨v98, s82, hinv82, h_v98⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v77 h_v78 h_v79 h_v90 h_v91 h_v95 h_v97 dropping hinv81 s81
  store_step with Store.apply_rep s82 v97 v98 _ _ hinv82 h64 h_v97 h_v98 (by ns_tac) (by ns_tac) as ⟨v99, s83, hinv83, h_v99⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v77 h_v78 h_v79 h_v90 h_v91 h_v95 dropping h_v97 h_v98 hinv82 s82 v97 v98
  store_step with Store.apply_rep s83 v95 v99 _ _ hinv83 h64 h_v95 h_v99 (by ns_tac) (by ns_tac) as ⟨v100, s84, hinv84, h_v100⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v77 h_v78 h_v79 h_v90 h_v91 dropping h_v95 h_v99 hinv83 s83 v95 v99
  store_step with Store.apply_rep s84 v91 v100 _ _ hinv84 h64 h_v91 h_v100 (by ns_tac) (by ns_tac) as ⟨v101, s85, hinv85, h_v101⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v77 h_v78 h_v79 h_v90 dropping h_v100 h_v91 hinv84 s84 v100 v91
  store_step with Store.literal_boolean_spec s85 true hinv85 h64 as ⟨v102, s86, hinv86, h_v102⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v77 h_v78 h_v79 h_v90 h_v101 dropping hinv85 s85
  store_step with Store.apply_rep s86 v101 v102 _ _ hinv86 h64 h_v101 h_v102 (by ns_tac) (by ns_tac) as ⟨v103, s87, hinv87, h_v103⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v77 h_v78 h_v79 h_v90 dropping h_v101 h_v102 hinv86 s86 v101 v102
  store_step with Store.apply_rep s87 v90 v103 _ _ hinv87 h64 h_v90 h_v103 (by ns_tac) (by ns_tac) as ⟨v104, s88, hinv88, h_v104⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v77 h_v78 h_v79 dropping h_v103 h_v90 hinv87 s87 v103 v90
  store_step with Store.apply_rep s88 v79 v104 _ _ hinv88 h64 h_v79 h_v104 (by ns_tac) (by ns_tac) as ⟨v105, s89, hinv89, h_v105⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v77 h_v78 dropping h_v104 h_v79 hinv88 s88 v104 v79
  step as ⟨e_v106, he_v106⟩
  store_step with CtorSpec.eo_and.construct s89 e_v106 (by rw [he_v106]; exact empty_args) hinv89 h64 as ⟨v106, s90, hinv90, h_v106⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v77 h_v78 h_v105 dropping he_v106 hinv89 e_v106 s89
  step as ⟨e_v107, he_v107⟩
  store_step with CtorSpec.eo__3d.construct s90 e_v107 (by rw [he_v107]; exact empty_args) hinv90 h64 as ⟨v107, s91, hinv91, h_v107⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v77 h_v78 h_v105 h_v106 dropping he_v107 hinv90 e_v107 s90
  step as ⟨e_v108, he_v108⟩
  store_step with CtorSpec.eo_extract.construct s91 e_v108 (by rw [he_v108]; rfl) h_a2 h_a2 hinv91 h64 as ⟨v108, s92, hinv92, h_v108⟩ growing hG carrying h_a0 h_a1 h_v25 h_v77 h_v78 h_v105 h_v106 h_v107 dropping h_a2 he_v108 hinv91 e_v108 s91
  step as ⟨e_v109, he_v109⟩
  store_step with CtorSpec.eo_bvadd.construct s92 e_v109 (by rw [he_v109]; exact empty_args) hinv92 h64 as ⟨v109, s93, hinv93, h_v109⟩ growing hG carrying h_a0 h_a1 h_v25 h_v77 h_v78 h_v105 h_v106 h_v107 h_v108 dropping he_v109 hinv92 e_v109 s92
  store_step with Store.apply_rep s93 v109 a0 _ _ hinv93 h64 h_v109 h_a0 (by ns_tac) (by ns_tac) as ⟨v110, s94, hinv94, h_v110⟩ growing hG carrying h_a0 h_a1 h_v25 h_v77 h_v78 h_v105 h_v106 h_v107 h_v108 dropping h_v109 hinv93 s93 v109
  step as ⟨e_v111, he_v111⟩
  store_step with CtorSpec.eo_bvadd.construct s94 e_v111 (by rw [he_v111]; exact empty_args) hinv94 h64 as ⟨v111, s95, hinv95, h_v111⟩ growing hG carrying h_a0 h_a1 h_v25 h_v77 h_v78 h_v105 h_v106 h_v107 h_v108 h_v110 dropping he_v111 hinv94 e_v111 s94
  store_step with Store.apply_rep s95 v111 a1 _ _ hinv95 h64 h_v111 h_a1 (by ns_tac) (by ns_tac) as ⟨v112, s96, hinv96, h_v112⟩ growing hG carrying h_a0 h_v25 h_v77 h_v78 h_v105 h_v106 h_v107 h_v108 h_v110 dropping h_a1 h_v111 hinv95 s95 v111
  step as ⟨e_v113, he_v113⟩
  store_step with CtorSpec.eo_bvadd.construct s96 e_v113 (by rw [he_v113]; exact empty_args) hinv96 h64 as ⟨v113, s97, hinv97, h_v113⟩ growing hG carrying h_a0 h_v25 h_v77 h_v78 h_v105 h_v106 h_v107 h_v108 h_v110 h_v112 dropping he_v113 hinv96 e_v113 s96
  store_step with ih.eo__24eo_5ftypeof s97 a0 _ hinv97 h64 (hG.rem hrem) h_a0 as ⟨v114, s98, hinv98, h_v114⟩ growing hG carrying h_v25 h_v77 h_v78 h_v105 h_v106 h_v107 h_v108 h_v110 h_v112 h_v113 dropping h_a0 hinv97 s97
  store_step with ih.eo__24eo_5fnil s98 v113 v114 _ _ hinv98 h64 (hG.rem hrem) h_v113 h_v114 as ⟨v115, s99, hinv99, h_v115⟩ growing hG carrying h_v25 h_v77 h_v78 h_v105 h_v106 h_v107 h_v108 h_v110 h_v112 dropping h_v113 h_v114 hinv98 s98 v113 v114
  store_step with Store.apply_mk_rep s99 v112 v115 _ _ hinv99 h64 h_v112 h_v115 as ⟨v116, s100, hinv100, h_v116⟩ growing hG carrying h_v25 h_v77 h_v78 h_v105 h_v106 h_v107 h_v108 h_v110 dropping h_v112 h_v115 hinv99 s99 v112 v115
  store_step with Store.apply_mk_rep s100 v110 v116 _ _ hinv100 h64 h_v110 h_v116 as ⟨v117, s101, hinv101, h_v117⟩ growing hG carrying h_v25 h_v77 h_v78 h_v105 h_v106 h_v107 h_v108 dropping h_v110 h_v116 hinv100 s100 v110 v116
  store_step with Store.apply_mk_rep s101 v108 v117 _ _ hinv101 h64 h_v108 h_v117 as ⟨v118, s102, hinv102, h_v118⟩ growing hG carrying h_v25 h_v77 h_v78 h_v105 h_v106 h_v107 dropping h_v108 h_v117 hinv101 s101 v108 v117
  store_step with Store.apply_mk_rep s102 v107 v118 _ _ hinv102 h64 h_v107 h_v118 as ⟨v119, s103, hinv103, h_v119⟩ growing hG carrying h_v25 h_v77 h_v78 h_v105 h_v106 dropping h_v107 h_v118 hinv102 s102 v107 v118
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s103 1#u32 (1) (by scalar_tac) hinv103 h64 as ⟨v120, s104, hinv104, h_v120⟩ growing hG carrying h_v25 h_v77 h_v78 h_v105 h_v106 h_v119 dropping hinv103 s103
  step as ⟨e_v121, he_v121⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s104 e_v121 (by rw [he_v121]; rfl) h_v120 hinv104 h64 as ⟨v121, s105, hinv105, h_v121⟩ growing hG carrying h_v25 h_v77 h_v78 h_v105 h_v106 h_v119 dropping h_v120 he_v121 hinv104 e_v121 s104 v120
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s105 1#u32 (1) (by scalar_tac) hinv105 h64 as ⟨v122, s106, hinv106, h_v122⟩ growing hG carrying h_v25 h_v77 h_v78 h_v105 h_v106 h_v119 h_v121 dropping hinv105 s105
  store_step with Store.apply_rep s106 v121 v122 _ _ hinv106 h64 h_v121 h_v122 (by ns_tac) (by ns_tac) as ⟨v123, s107, hinv107, h_v123⟩ growing hG carrying h_v25 h_v77 h_v78 h_v105 h_v106 h_v119 dropping h_v121 h_v122 hinv106 s106 v121 v122
  store_step with Store.apply_mk_rep s107 v119 v123 _ _ hinv107 h64 h_v119 h_v123 as ⟨v124, s108, hinv108, h_v124⟩ growing hG carrying h_v25 h_v77 h_v78 h_v105 h_v106 dropping h_v119 h_v123 hinv107 s107 v119 v123
  store_step with Store.apply_mk_rep s108 v106 v124 _ _ hinv108 h64 h_v106 h_v124 as ⟨v125, s109, hinv109, h_v125⟩ growing hG carrying h_v25 h_v77 h_v78 h_v105 dropping h_v106 h_v124 hinv108 s108 v106 v124
  store_step with Store.literal_boolean_spec s109 true hinv109 h64 as ⟨v126, s110, hinv110, h_v126⟩ growing hG carrying h_v25 h_v77 h_v78 h_v105 h_v125 dropping hinv109 s109
  store_step with Store.apply_mk_rep s110 v125 v126 _ _ hinv110 h64 h_v125 h_v126 as ⟨v127, s111, hinv111, h_v127⟩ growing hG carrying h_v25 h_v77 h_v78 h_v105 dropping h_v125 h_v126 hinv110 s110 v125 v126
  store_step with Store.apply_mk_rep s111 v105 v127 _ _ hinv111 h64 h_v105 h_v127 as ⟨v128, s112, hinv112, h_v128⟩ growing hG carrying h_v25 h_v77 h_v78 dropping h_v105 h_v127 hinv111 s111 v105 v127
  store_step with Store.apply_mk_rep s112 v78 v128 _ _ hinv112 h64 h_v78 h_v128 as ⟨v129, s113, hinv113, h_v129⟩ growing hG carrying h_v25 h_v77 dropping h_v128 h_v78 hinv112 s112 v128 v78
  store_step with Store.literal_boolean_spec s113 false hinv113 h64 as ⟨v130, s114, hinv114, h_v130⟩ growing hG carrying h_v25 h_v77 h_v129 dropping hinv113 s113
  store_step with Store.apply_mk_rep s114 v129 v130 _ _ hinv114 h64 h_v129 h_v130 as ⟨v131, s115, hinv115, h_v131⟩ growing hG carrying h_v25 h_v77 dropping h_v129 h_v130 hinv114 s114 v129 v130
  store_step with Store.apply_mk_rep s115 v77 v131 _ _ hinv115 h64 h_v77 h_v131 as ⟨v132, s116, hinv116, h_v132⟩ growing hG carrying h_v25 dropping h_v131 h_v77 hinv115 s115 v131 v77
  store_step with Store.apply_mk_rep s116 v25 v132 _ _ hinv116 h64 h_v25 h_v132 as ⟨v133, s117, hinv117, h_v133⟩ growing hG carrying dropping h_v132 h_v25 hinv116 s116 v132 v25
  case_done hinv117 hG with h_v133 in EoCases.__eo_prog_bv_saddo_eliminate.case_0 using hn_a0 hn_a1 hn_a2 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v13 hn_v14 hn_v17 hn_v18

/-- logos's `__eo_prog_bv_saddo_eliminate` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fbv_2dsaddo_2deliminate.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) :
    __eo_prog_bv_saddo_eliminate x_a0 x_a1 x_a2 x_a3 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_bv_saddo_eliminate.case_0 x_a0 x_a1 x_a2 x_a3] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_bv_saddo_eliminate
  unfold EoCases.__eo_prog_bv_saddo_eliminate.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fbv_2dsaddo_2deliminate_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) :
    body_eo__24eo_5fprog_5fbv_2dsaddo_2deliminate s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_saddo_eliminate x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fbv_2dsaddo_2deliminate.rust_eq x_a0 x_a1 x_a2 x_a3 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3)]
  unfold body_eo__24eo_5fprog_5fbv_2dsaddo_2deliminate
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fbv_2dsaddo_2deliminate_spec n ih s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 using hn_a0 hn_a1 hn_a2
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hc0 in EoCases.__eo_prog_bv_saddo_eliminate.case_0

theorem eo__24eo_5fprog_5fbv_2dsaddo_2deliminate_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fbv_2dsaddo_2deliminate.Spec n := by
  intro s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3
  unfold eo__24eo_5fprog_5fbv_2dsaddo_2deliminate
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fbv_2dsaddo_2deliminate s1 a0 a1 a2 a3) (fun s' t => Represents.rep s' t (__eo_prog_bv_saddo_eliminate x_a0 x_a1 x_a2 x_a3))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fbv_2dsaddo_2deliminate_spec m (ih m hm) s1 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

set_option maxHeartbeats 3090000 in
theorem case_0_eo__24eo_5fprog_5fbv_2dsdiv_2deliminate_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fbv_2dsdiv_2deliminate s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_bv_sdiv_eliminate.case_0 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_bv_sdiv_eliminate.case_0 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fbv_2dsdiv_2deliminate
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a3 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_bv_sdiv_eliminate.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_sdiv_eliminate.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_sdiv_eliminate.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_v4 h_v6 h_v7 dropping h_a3 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_sdiv_eliminate.case_0
  pat_same v7 a2 with h_v7 h_a2 using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_sdiv_eliminate.case_0
  pat_unapply h_v4 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_sdiv_eliminate.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_sdiv_eliminate.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__2d.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_v11 h_v13 h_v14 dropping h_v10 h_v4 h_v6 h_v7 h_v8 he_v15 hinv1 e_v15 s1 v10 v4 v6 v7 v8
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_sdiv_eliminate.case_0
  pat_unapply h_v14 as ⟨v17, v18, x_v17, x_v18, h_v17, h_v18, hn_v17, hn_v18⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_sdiv_eliminate.case_0
  step as ⟨e_v19, he_v19⟩
  store_step with CtorSpec.eo__40bvsize.construct s2 e_v19 (by rw [he_v19]; exact empty_args) hinv2 h64 as ⟨v19, s3, hinv3, h_v19⟩ growing hG carrying h_a0 h_a1 h_a2 h_v11 h_v17 h_v18 dropping h_v13 h_v14 h_v15 he_v19 hinv2 e_v19 s2 v13 v14 v15
  pat_same v17 v19 with h_v17 h_v19 using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_sdiv_eliminate.case_0
  pat_same v18 a0 with h_v18 h_a0 using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_sdiv_eliminate.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s3 1#u32 (1) (by scalar_tac) hinv3 h64 as ⟨v20, s4, hinv4, h_v20⟩ growing hG carrying h_a0 h_a1 h_a2 h_v11 dropping h_v17 h_v18 h_v19 hinv3 s3 v17 v18 v19
  pat_same v11 v20 with h_v11 h_v20 using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_sdiv_eliminate.case_0
  step as ⟨e_v21, he_v21⟩
  store_step with CtorSpec.eo__3d.construct s4 e_v21 (by rw [he_v21]; exact empty_args) hinv4 h64 as ⟨v21, s5, hinv5, h_v21⟩ growing hG carrying h_a0 h_a1 h_a2 dropping h_v11 h_v20 he_v21 hinv4 e_v21 s4 v11 v20
  step as ⟨e_v22, he_v22⟩
  store_step with CtorSpec.eo_bvsdiv.construct s5 e_v22 (by rw [he_v22]; exact empty_args) hinv5 h64 as ⟨v22, s6, hinv6, h_v22⟩ growing hG carrying h_a0 h_a1 h_a2 h_v21 dropping he_v22 hinv5 e_v22 s5
  store_step with Store.apply_rep s6 v22 a0 _ _ hinv6 h64 h_v22 h_a0 (by ns_tac) (by ns_tac) as ⟨v23, s7, hinv7, h_v23⟩ growing hG carrying h_a0 h_a1 h_a2 h_v21 dropping h_v22 hinv6 s6 v22
  store_step with Store.apply_rep s7 v23 a1 _ _ hinv7 h64 h_v23 h_a1 (by ns_tac) (by ns_tac) as ⟨v24, s8, hinv8, h_v24⟩ growing hG carrying h_a0 h_a1 h_a2 h_v21 dropping h_v23 hinv7 s7 v23
  store_step with Store.apply_rep s8 v21 v24 _ _ hinv8 h64 h_v21 h_v24 (by ns_tac) (by ns_tac) as ⟨v25, s9, hinv9, h_v25⟩ growing hG carrying h_a0 h_a1 h_a2 dropping h_v21 h_v24 hinv8 s8 v21 v24
  step as ⟨e_v26, he_v26⟩
  store_step with CtorSpec.eo_ite.construct s9 e_v26 (by rw [he_v26]; exact empty_args) hinv9 h64 as ⟨v26, s10, hinv10, h_v26⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 dropping he_v26 hinv9 e_v26 s9
  step as ⟨e_v27, he_v27⟩
  store_step with CtorSpec.eo_xor.construct s10 e_v27 (by rw [he_v27]; exact empty_args) hinv10 h64 as ⟨v27, s11, hinv11, h_v27⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 dropping he_v27 hinv10 e_v27 s10
  step as ⟨e_v28, he_v28⟩
  store_step with CtorSpec.eo__3d.construct s11 e_v28 (by rw [he_v28]; exact empty_args) hinv11 h64 as ⟨v28, s12, hinv12, h_v28⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 h_v27 dropping he_v28 hinv11 e_v28 s11
  step as ⟨e_v29, he_v29⟩
  store_step with CtorSpec.eo_extract.construct s12 e_v29 (by rw [he_v29]; rfl) h_a2 h_a2 hinv12 h64 as ⟨v29, s13, hinv13, h_v29⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 h_v27 h_v28 dropping he_v29 hinv12 e_v29 s12
  store_step with Store.apply_rep s13 v29 a0 _ _ hinv13 h64 h_v29 h_a0 (by ns_tac) (by ns_tac) as ⟨v30, s14, hinv14, h_v30⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 h_v27 h_v28 dropping h_v29 hinv13 s13 v29
  store_step with Store.apply_rep s14 v28 v30 _ _ hinv14 h64 h_v28 h_v30 (by ns_tac) (by ns_tac) as ⟨v31, s15, hinv15, h_v31⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 h_v27 dropping h_v28 h_v30 hinv14 s14 v28 v30
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s15 1#u32 (1) (by scalar_tac) hinv15 h64 as ⟨v32, s16, hinv16, h_v32⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 h_v27 h_v31 dropping hinv15 s15
  step as ⟨e_v33, he_v33⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s16 e_v33 (by rw [he_v33]; rfl) h_v32 hinv16 h64 as ⟨v33, s17, hinv17, h_v33⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 h_v27 h_v31 dropping h_v32 he_v33 hinv16 e_v33 s16 v32
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s17 1#u32 (1) (by scalar_tac) hinv17 h64 as ⟨v34, s18, hinv18, h_v34⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 h_v27 h_v31 h_v33 dropping hinv17 s17
  store_step with Store.apply_rep s18 v33 v34 _ _ hinv18 h64 h_v33 h_v34 (by ns_tac) (by ns_tac) as ⟨v35, s19, hinv19, h_v35⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 h_v27 h_v31 dropping h_v33 h_v34 hinv18 s18 v33 v34
  store_step with Store.apply_rep s19 v31 v35 _ _ hinv19 h64 h_v31 h_v35 (by ns_tac) (by ns_tac) as ⟨v36, s20, hinv20, h_v36⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 h_v27 dropping h_v31 h_v35 hinv19 s19 v31 v35
  store_step with Store.apply_rep s20 v27 v36 _ _ hinv20 h64 h_v27 h_v36 (by ns_tac) (by ns_tac) as ⟨v37, s21, hinv21, h_v37⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 dropping h_v27 h_v36 hinv20 s20 v27 v36
  step as ⟨e_v38, he_v38⟩
  store_step with CtorSpec.eo__3d.construct s21 e_v38 (by rw [he_v38]; exact empty_args) hinv21 h64 as ⟨v38, s22, hinv22, h_v38⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 h_v37 dropping he_v38 hinv21 e_v38 s21
  step as ⟨e_v39, he_v39⟩
  store_step with CtorSpec.eo_extract.construct s22 e_v39 (by rw [he_v39]; rfl) h_a2 h_a2 hinv22 h64 as ⟨v39, s23, hinv23, h_v39⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 h_v37 h_v38 dropping he_v39 hinv22 e_v39 s22
  store_step with Store.apply_rep s23 v39 a1 _ _ hinv23 h64 h_v39 h_a1 (by ns_tac) (by ns_tac) as ⟨v40, s24, hinv24, h_v40⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 h_v37 h_v38 dropping h_v39 hinv23 s23 v39
  store_step with Store.apply_rep s24 v38 v40 _ _ hinv24 h64 h_v38 h_v40 (by ns_tac) (by ns_tac) as ⟨v41, s25, hinv25, h_v41⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 h_v37 dropping h_v38 h_v40 hinv24 s24 v38 v40
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s25 1#u32 (1) (by scalar_tac) hinv25 h64 as ⟨v42, s26, hinv26, h_v42⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 h_v37 h_v41 dropping hinv25 s25
  step as ⟨e_v43, he_v43⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s26 e_v43 (by rw [he_v43]; rfl) h_v42 hinv26 h64 as ⟨v43, s27, hinv27, h_v43⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 h_v37 h_v41 dropping h_v42 he_v43 hinv26 e_v43 s26 v42
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s27 1#u32 (1) (by scalar_tac) hinv27 h64 as ⟨v44, s28, hinv28, h_v44⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 h_v37 h_v41 h_v43 dropping hinv27 s27
  store_step with Store.apply_rep s28 v43 v44 _ _ hinv28 h64 h_v43 h_v44 (by ns_tac) (by ns_tac) as ⟨v45, s29, hinv29, h_v45⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 h_v37 h_v41 dropping h_v43 h_v44 hinv28 s28 v43 v44
  store_step with Store.apply_rep s29 v41 v45 _ _ hinv29 h64 h_v41 h_v45 (by ns_tac) (by ns_tac) as ⟨v46, s30, hinv30, h_v46⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 h_v37 dropping h_v41 h_v45 hinv29 s29 v41 v45
  store_step with Store.apply_rep s30 v37 v46 _ _ hinv30 h64 h_v37 h_v46 (by ns_tac) (by ns_tac) as ⟨v47, s31, hinv31, h_v47⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 dropping h_v37 h_v46 hinv30 s30 v37 v46
  store_step with Store.apply_rep s31 v26 v47 _ _ hinv31 h64 h_v26 h_v47 (by ns_tac) (by ns_tac) as ⟨v48, s32, hinv32, h_v48⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 dropping h_v26 h_v47 hinv31 s31 v26 v47
  step as ⟨e_v49, he_v49⟩
  store_step with CtorSpec.eo_bvneg.construct s32 e_v49 (by rw [he_v49]; exact empty_args) hinv32 h64 as ⟨v49, s33, hinv33, h_v49⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v48 dropping he_v49 hinv32 e_v49 s32
  step as ⟨e_v50, he_v50⟩
  store_step with CtorSpec.eo_bvudiv.construct s33 e_v50 (by rw [he_v50]; exact empty_args) hinv33 h64 as ⟨v50, s34, hinv34, h_v50⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v48 h_v49 dropping he_v50 hinv33 e_v50 s33
  step as ⟨e_v51, he_v51⟩
  store_step with CtorSpec.eo_ite.construct s34 e_v51 (by rw [he_v51]; exact empty_args) hinv34 h64 as ⟨v51, s35, hinv35, h_v51⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v48 h_v49 h_v50 dropping he_v51 hinv34 e_v51 s34
  step as ⟨e_v52, he_v52⟩
  store_step with CtorSpec.eo__3d.construct s35 e_v52 (by rw [he_v52]; exact empty_args) hinv35 h64 as ⟨v52, s36, hinv36, h_v52⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v48 h_v49 h_v50 h_v51 dropping he_v52 hinv35 e_v52 s35
  step as ⟨e_v53, he_v53⟩
  store_step with CtorSpec.eo_extract.construct s36 e_v53 (by rw [he_v53]; rfl) h_a2 h_a2 hinv36 h64 as ⟨v53, s37, hinv37, h_v53⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v48 h_v49 h_v50 h_v51 h_v52 dropping he_v53 hinv36 e_v53 s36
  store_step with Store.apply_rep s37 v53 a0 _ _ hinv37 h64 h_v53 h_a0 (by ns_tac) (by ns_tac) as ⟨v54, s38, hinv38, h_v54⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v48 h_v49 h_v50 h_v51 h_v52 dropping h_v53 hinv37 s37 v53
  store_step with Store.apply_rep s38 v52 v54 _ _ hinv38 h64 h_v52 h_v54 (by ns_tac) (by ns_tac) as ⟨v55, s39, hinv39, h_v55⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v48 h_v49 h_v50 h_v51 dropping h_v52 h_v54 hinv38 s38 v52 v54
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s39 1#u32 (1) (by scalar_tac) hinv39 h64 as ⟨v56, s40, hinv40, h_v56⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v48 h_v49 h_v50 h_v51 h_v55 dropping hinv39 s39
  step as ⟨e_v57, he_v57⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s40 e_v57 (by rw [he_v57]; rfl) h_v56 hinv40 h64 as ⟨v57, s41, hinv41, h_v57⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v48 h_v49 h_v50 h_v51 h_v55 dropping h_v56 he_v57 hinv40 e_v57 s40 v56
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s41 1#u32 (1) (by scalar_tac) hinv41 h64 as ⟨v58, s42, hinv42, h_v58⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v48 h_v49 h_v50 h_v51 h_v55 h_v57 dropping hinv41 s41
  store_step with Store.apply_rep s42 v57 v58 _ _ hinv42 h64 h_v57 h_v58 (by ns_tac) (by ns_tac) as ⟨v59, s43, hinv43, h_v59⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v48 h_v49 h_v50 h_v51 h_v55 dropping h_v57 h_v58 hinv42 s42 v57 v58
  store_step with Store.apply_rep s43 v55 v59 _ _ hinv43 h64 h_v55 h_v59 (by ns_tac) (by ns_tac) as ⟨v60, s44, hinv44, h_v60⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v48 h_v49 h_v50 h_v51 dropping h_v55 h_v59 hinv43 s43 v55 v59
  store_step with Store.apply_rep s44 v51 v60 _ _ hinv44 h64 h_v51 h_v60 (by ns_tac) (by ns_tac) as ⟨v61, s45, hinv45, h_v61⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v48 h_v49 h_v50 dropping h_v51 h_v60 hinv44 s44 v51 v60
  step as ⟨e_v62, he_v62⟩
  store_step with CtorSpec.eo_bvneg.construct s45 e_v62 (by rw [he_v62]; exact empty_args) hinv45 h64 as ⟨v62, s46, hinv46, h_v62⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v48 h_v49 h_v50 h_v61 dropping he_v62 hinv45 e_v62 s45
  store_step with Store.apply_rep s46 v62 a0 _ _ hinv46 h64 h_v62 h_a0 (by ns_tac) (by ns_tac) as ⟨v63, s47, hinv47, h_v63⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v48 h_v49 h_v50 h_v61 dropping h_v62 hinv46 s46 v62
  store_step with Store.apply_rep s47 v61 v63 _ _ hinv47 h64 h_v61 h_v63 (by ns_tac) (by ns_tac) as ⟨v64, s48, hinv48, h_v64⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v48 h_v49 h_v50 dropping h_v61 h_v63 hinv47 s47 v61 v63
  store_step with Store.apply_rep s48 v64 a0 _ _ hinv48 h64 h_v64 h_a0 (by ns_tac) (by ns_tac) as ⟨v65, s49, hinv49, h_v65⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v48 h_v49 h_v50 dropping h_v64 hinv48 s48 v64
  store_step with Store.apply_rep s49 v50 v65 _ _ hinv49 h64 h_v50 h_v65 (by ns_tac) (by ns_tac) as ⟨v66, s50, hinv50, h_v66⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v48 h_v49 dropping h_v50 h_v65 hinv49 s49 v50 v65
  step as ⟨e_v67, he_v67⟩
  store_step with CtorSpec.eo_ite.construct s50 e_v67 (by rw [he_v67]; exact empty_args) hinv50 h64 as ⟨v67, s51, hinv51, h_v67⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v48 h_v49 h_v66 dropping he_v67 hinv50 e_v67 s50
  step as ⟨e_v68, he_v68⟩
  store_step with CtorSpec.eo__3d.construct s51 e_v68 (by rw [he_v68]; exact empty_args) hinv51 h64 as ⟨v68, s52, hinv52, h_v68⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v48 h_v49 h_v66 h_v67 dropping he_v68 hinv51 e_v68 s51
  step as ⟨e_v69, he_v69⟩
  store_step with CtorSpec.eo_extract.construct s52 e_v69 (by rw [he_v69]; rfl) h_a2 h_a2 hinv52 h64 as ⟨v69, s53, hinv53, h_v69⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v48 h_v49 h_v66 h_v67 h_v68 dropping he_v69 hinv52 e_v69 s52
  store_step with Store.apply_rep s53 v69 a1 _ _ hinv53 h64 h_v69 h_a1 (by ns_tac) (by ns_tac) as ⟨v70, s54, hinv54, h_v70⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v48 h_v49 h_v66 h_v67 h_v68 dropping h_v69 hinv53 s53 v69
  store_step with Store.apply_rep s54 v68 v70 _ _ hinv54 h64 h_v68 h_v70 (by ns_tac) (by ns_tac) as ⟨v71, s55, hinv55, h_v71⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v48 h_v49 h_v66 h_v67 dropping h_v68 h_v70 hinv54 s54 v68 v70
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s55 1#u32 (1) (by scalar_tac) hinv55 h64 as ⟨v72, s56, hinv56, h_v72⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v48 h_v49 h_v66 h_v67 h_v71 dropping hinv55 s55
  step as ⟨e_v73, he_v73⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s56 e_v73 (by rw [he_v73]; rfl) h_v72 hinv56 h64 as ⟨v73, s57, hinv57, h_v73⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v48 h_v49 h_v66 h_v67 h_v71 dropping h_v72 he_v73 hinv56 e_v73 s56 v72
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s57 1#u32 (1) (by scalar_tac) hinv57 h64 as ⟨v74, s58, hinv58, h_v74⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v48 h_v49 h_v66 h_v67 h_v71 h_v73 dropping hinv57 s57
  store_step with Store.apply_rep s58 v73 v74 _ _ hinv58 h64 h_v73 h_v74 (by ns_tac) (by ns_tac) as ⟨v75, s59, hinv59, h_v75⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v48 h_v49 h_v66 h_v67 h_v71 dropping h_v73 h_v74 hinv58 s58 v73 v74
  store_step with Store.apply_rep s59 v71 v75 _ _ hinv59 h64 h_v71 h_v75 (by ns_tac) (by ns_tac) as ⟨v76, s60, hinv60, h_v76⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v48 h_v49 h_v66 h_v67 dropping h_v71 h_v75 hinv59 s59 v71 v75
  store_step with Store.apply_rep s60 v67 v76 _ _ hinv60 h64 h_v67 h_v76 (by ns_tac) (by ns_tac) as ⟨v77, s61, hinv61, h_v77⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v48 h_v49 h_v66 dropping h_v67 h_v76 hinv60 s60 v67 v76
  step as ⟨e_v78, he_v78⟩
  store_step with CtorSpec.eo_bvneg.construct s61 e_v78 (by rw [he_v78]; exact empty_args) hinv61 h64 as ⟨v78, s62, hinv62, h_v78⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v48 h_v49 h_v66 h_v77 dropping he_v78 hinv61 e_v78 s61
  store_step with Store.apply_rep s62 v78 a1 _ _ hinv62 h64 h_v78 h_a1 (by ns_tac) (by ns_tac) as ⟨v79, s63, hinv63, h_v79⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v48 h_v49 h_v66 h_v77 dropping h_v78 hinv62 s62 v78
  store_step with Store.apply_rep s63 v77 v79 _ _ hinv63 h64 h_v77 h_v79 (by ns_tac) (by ns_tac) as ⟨v80, s64, hinv64, h_v80⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v48 h_v49 h_v66 dropping h_v77 h_v79 hinv63 s63 v77 v79
  store_step with Store.apply_rep s64 v80 a1 _ _ hinv64 h64 h_v80 h_a1 (by ns_tac) (by ns_tac) as ⟨v81, s65, hinv65, h_v81⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v48 h_v49 h_v66 dropping h_v80 hinv64 s64 v80
  store_step with Store.apply_rep s65 v66 v81 _ _ hinv65 h64 h_v66 h_v81 (by ns_tac) (by ns_tac) as ⟨v82, s66, hinv66, h_v82⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v48 h_v49 dropping h_v66 h_v81 hinv65 s65 v66 v81
  store_step with Store.apply_rep s66 v49 v82 _ _ hinv66 h64 h_v49 h_v82 (by ns_tac) (by ns_tac) as ⟨v83, s67, hinv67, h_v83⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v48 dropping h_v49 h_v82 hinv66 s66 v49 v82
  store_step with Store.apply_rep s67 v48 v83 _ _ hinv67 h64 h_v48 h_v83 (by ns_tac) (by ns_tac) as ⟨v84, s68, hinv68, h_v84⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 dropping h_v48 h_v83 hinv67 s67 v48 v83
  step as ⟨e_v85, he_v85⟩
  store_step with CtorSpec.eo_bvudiv.construct s68 e_v85 (by rw [he_v85]; exact empty_args) hinv68 h64 as ⟨v85, s69, hinv69, h_v85⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v84 dropping he_v85 hinv68 e_v85 s68
  step as ⟨e_v86, he_v86⟩
  store_step with CtorSpec.eo_ite.construct s69 e_v86 (by rw [he_v86]; exact empty_args) hinv69 h64 as ⟨v86, s70, hinv70, h_v86⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v84 h_v85 dropping he_v86 hinv69 e_v86 s69
  step as ⟨e_v87, he_v87⟩
  store_step with CtorSpec.eo__3d.construct s70 e_v87 (by rw [he_v87]; exact empty_args) hinv70 h64 as ⟨v87, s71, hinv71, h_v87⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v84 h_v85 h_v86 dropping he_v87 hinv70 e_v87 s70
  step as ⟨e_v88, he_v88⟩
  store_step with CtorSpec.eo_extract.construct s71 e_v88 (by rw [he_v88]; rfl) h_a2 h_a2 hinv71 h64 as ⟨v88, s72, hinv72, h_v88⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v84 h_v85 h_v86 h_v87 dropping he_v88 hinv71 e_v88 s71
  store_step with Store.apply_rep s72 v88 a0 _ _ hinv72 h64 h_v88 h_a0 (by ns_tac) (by ns_tac) as ⟨v89, s73, hinv73, h_v89⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v84 h_v85 h_v86 h_v87 dropping h_v88 hinv72 s72 v88
  store_step with Store.apply_rep s73 v87 v89 _ _ hinv73 h64 h_v87 h_v89 (by ns_tac) (by ns_tac) as ⟨v90, s74, hinv74, h_v90⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v84 h_v85 h_v86 dropping h_v87 h_v89 hinv73 s73 v87 v89
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s74 1#u32 (1) (by scalar_tac) hinv74 h64 as ⟨v91, s75, hinv75, h_v91⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v84 h_v85 h_v86 h_v90 dropping hinv74 s74
  step as ⟨e_v92, he_v92⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s75 e_v92 (by rw [he_v92]; rfl) h_v91 hinv75 h64 as ⟨v92, s76, hinv76, h_v92⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v84 h_v85 h_v86 h_v90 dropping h_v91 he_v92 hinv75 e_v92 s75 v91
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s76 1#u32 (1) (by scalar_tac) hinv76 h64 as ⟨v93, s77, hinv77, h_v93⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v84 h_v85 h_v86 h_v90 h_v92 dropping hinv76 s76
  store_step with Store.apply_rep s77 v92 v93 _ _ hinv77 h64 h_v92 h_v93 (by ns_tac) (by ns_tac) as ⟨v94, s78, hinv78, h_v94⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v84 h_v85 h_v86 h_v90 dropping h_v92 h_v93 hinv77 s77 v92 v93
  store_step with Store.apply_rep s78 v90 v94 _ _ hinv78 h64 h_v90 h_v94 (by ns_tac) (by ns_tac) as ⟨v95, s79, hinv79, h_v95⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v84 h_v85 h_v86 dropping h_v90 h_v94 hinv78 s78 v90 v94
  store_step with Store.apply_rep s79 v86 v95 _ _ hinv79 h64 h_v86 h_v95 (by ns_tac) (by ns_tac) as ⟨v96, s80, hinv80, h_v96⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v84 h_v85 dropping h_v86 h_v95 hinv79 s79 v86 v95
  step as ⟨e_v97, he_v97⟩
  store_step with CtorSpec.eo_bvneg.construct s80 e_v97 (by rw [he_v97]; exact empty_args) hinv80 h64 as ⟨v97, s81, hinv81, h_v97⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v84 h_v85 h_v96 dropping he_v97 hinv80 e_v97 s80
  store_step with Store.apply_rep s81 v97 a0 _ _ hinv81 h64 h_v97 h_a0 (by ns_tac) (by ns_tac) as ⟨v98, s82, hinv82, h_v98⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v84 h_v85 h_v96 dropping h_v97 hinv81 s81 v97
  store_step with Store.apply_rep s82 v96 v98 _ _ hinv82 h64 h_v96 h_v98 (by ns_tac) (by ns_tac) as ⟨v99, s83, hinv83, h_v99⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v84 h_v85 dropping h_v96 h_v98 hinv82 s82 v96 v98
  store_step with Store.apply_rep s83 v99 a0 _ _ hinv83 h64 h_v99 h_a0 (by ns_tac) (by ns_tac) as ⟨v100, s84, hinv84, h_v100⟩ growing hG carrying h_a1 h_a2 h_v25 h_v84 h_v85 dropping h_a0 h_v99 hinv83 s83 v99
  store_step with Store.apply_rep s84 v85 v100 _ _ hinv84 h64 h_v85 h_v100 (by ns_tac) (by ns_tac) as ⟨v101, s85, hinv85, h_v101⟩ growing hG carrying h_a1 h_a2 h_v25 h_v84 dropping h_v100 h_v85 hinv84 s84 v100 v85
  step as ⟨e_v102, he_v102⟩
  store_step with CtorSpec.eo_ite.construct s85 e_v102 (by rw [he_v102]; exact empty_args) hinv85 h64 as ⟨v102, s86, hinv86, h_v102⟩ growing hG carrying h_a1 h_a2 h_v25 h_v84 h_v101 dropping he_v102 hinv85 e_v102 s85
  step as ⟨e_v103, he_v103⟩
  store_step with CtorSpec.eo__3d.construct s86 e_v103 (by rw [he_v103]; exact empty_args) hinv86 h64 as ⟨v103, s87, hinv87, h_v103⟩ growing hG carrying h_a1 h_a2 h_v25 h_v84 h_v101 h_v102 dropping he_v103 hinv86 e_v103 s86
  step as ⟨e_v104, he_v104⟩
  store_step with CtorSpec.eo_extract.construct s87 e_v104 (by rw [he_v104]; rfl) h_a2 h_a2 hinv87 h64 as ⟨v104, s88, hinv88, h_v104⟩ growing hG carrying h_a1 h_v25 h_v84 h_v101 h_v102 h_v103 dropping h_a2 he_v104 hinv87 e_v104 s87
  store_step with Store.apply_rep s88 v104 a1 _ _ hinv88 h64 h_v104 h_a1 (by ns_tac) (by ns_tac) as ⟨v105, s89, hinv89, h_v105⟩ growing hG carrying h_a1 h_v25 h_v84 h_v101 h_v102 h_v103 dropping h_v104 hinv88 s88 v104
  store_step with Store.apply_rep s89 v103 v105 _ _ hinv89 h64 h_v103 h_v105 (by ns_tac) (by ns_tac) as ⟨v106, s90, hinv90, h_v106⟩ growing hG carrying h_a1 h_v25 h_v84 h_v101 h_v102 dropping h_v103 h_v105 hinv89 s89 v103 v105
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s90 1#u32 (1) (by scalar_tac) hinv90 h64 as ⟨v107, s91, hinv91, h_v107⟩ growing hG carrying h_a1 h_v25 h_v84 h_v101 h_v102 h_v106 dropping hinv90 s90
  step as ⟨e_v108, he_v108⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s91 e_v108 (by rw [he_v108]; rfl) h_v107 hinv91 h64 as ⟨v108, s92, hinv92, h_v108⟩ growing hG carrying h_a1 h_v25 h_v84 h_v101 h_v102 h_v106 dropping h_v107 he_v108 hinv91 e_v108 s91 v107
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s92 1#u32 (1) (by scalar_tac) hinv92 h64 as ⟨v109, s93, hinv93, h_v109⟩ growing hG carrying h_a1 h_v25 h_v84 h_v101 h_v102 h_v106 h_v108 dropping hinv92 s92
  store_step with Store.apply_rep s93 v108 v109 _ _ hinv93 h64 h_v108 h_v109 (by ns_tac) (by ns_tac) as ⟨v110, s94, hinv94, h_v110⟩ growing hG carrying h_a1 h_v25 h_v84 h_v101 h_v102 h_v106 dropping h_v108 h_v109 hinv93 s93 v108 v109
  store_step with Store.apply_rep s94 v106 v110 _ _ hinv94 h64 h_v106 h_v110 (by ns_tac) (by ns_tac) as ⟨v111, s95, hinv95, h_v111⟩ growing hG carrying h_a1 h_v25 h_v84 h_v101 h_v102 dropping h_v106 h_v110 hinv94 s94 v106 v110
  store_step with Store.apply_rep s95 v102 v111 _ _ hinv95 h64 h_v102 h_v111 (by ns_tac) (by ns_tac) as ⟨v112, s96, hinv96, h_v112⟩ growing hG carrying h_a1 h_v25 h_v84 h_v101 dropping h_v102 h_v111 hinv95 s95 v102 v111
  step as ⟨e_v113, he_v113⟩
  store_step with CtorSpec.eo_bvneg.construct s96 e_v113 (by rw [he_v113]; exact empty_args) hinv96 h64 as ⟨v113, s97, hinv97, h_v113⟩ growing hG carrying h_a1 h_v25 h_v84 h_v101 h_v112 dropping he_v113 hinv96 e_v113 s96
  store_step with Store.apply_rep s97 v113 a1 _ _ hinv97 h64 h_v113 h_a1 (by ns_tac) (by ns_tac) as ⟨v114, s98, hinv98, h_v114⟩ growing hG carrying h_a1 h_v25 h_v84 h_v101 h_v112 dropping h_v113 hinv97 s97 v113
  store_step with Store.apply_rep s98 v112 v114 _ _ hinv98 h64 h_v112 h_v114 (by ns_tac) (by ns_tac) as ⟨v115, s99, hinv99, h_v115⟩ growing hG carrying h_a1 h_v25 h_v84 h_v101 dropping h_v112 h_v114 hinv98 s98 v112 v114
  store_step with Store.apply_rep s99 v115 a1 _ _ hinv99 h64 h_v115 h_a1 (by ns_tac) (by ns_tac) as ⟨v116, s100, hinv100, h_v116⟩ growing hG carrying h_v25 h_v84 h_v101 dropping h_a1 h_v115 hinv99 s99 v115
  store_step with Store.apply_rep s100 v101 v116 _ _ hinv100 h64 h_v101 h_v116 (by ns_tac) (by ns_tac) as ⟨v117, s101, hinv101, h_v117⟩ growing hG carrying h_v25 h_v84 dropping h_v101 h_v116 hinv100 s100 v101 v116
  store_step with Store.apply_rep s101 v84 v117 _ _ hinv101 h64 h_v84 h_v117 (by ns_tac) (by ns_tac) as ⟨v118, s102, hinv102, h_v118⟩ growing hG carrying h_v25 dropping h_v117 h_v84 hinv101 s101 v117 v84
  store_step with Store.apply_rep s102 v25 v118 _ _ hinv102 h64 h_v25 h_v118 (by ns_tac) (by ns_tac) as ⟨v119, s103, hinv103, h_v119⟩ growing hG carrying dropping h_v118 h_v25 hinv102 s102 v118 v25
  case_done hinv103 hG with h_v119 in EoCases.__eo_prog_bv_sdiv_eliminate.case_0 using hn_a0 hn_a1 hn_a2 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v13 hn_v14 hn_v17 hn_v18

/-- logos's `__eo_prog_bv_sdiv_eliminate` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fbv_2dsdiv_2deliminate.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) :
    __eo_prog_bv_sdiv_eliminate x_a0 x_a1 x_a2 x_a3 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_bv_sdiv_eliminate.case_0 x_a0 x_a1 x_a2 x_a3] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_bv_sdiv_eliminate
  unfold EoCases.__eo_prog_bv_sdiv_eliminate.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fbv_2dsdiv_2deliminate_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) :
    body_eo__24eo_5fprog_5fbv_2dsdiv_2deliminate s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_sdiv_eliminate x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fbv_2dsdiv_2deliminate.rust_eq x_a0 x_a1 x_a2 x_a3 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3)]
  unfold body_eo__24eo_5fprog_5fbv_2dsdiv_2deliminate
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fbv_2dsdiv_2deliminate_spec n ih s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 using hn_a0 hn_a1 hn_a2
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hc0 in EoCases.__eo_prog_bv_sdiv_eliminate.case_0

theorem eo__24eo_5fprog_5fbv_2dsdiv_2deliminate_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fbv_2dsdiv_2deliminate.Spec n := by
  intro s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3
  unfold eo__24eo_5fprog_5fbv_2dsdiv_2deliminate
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fbv_2dsdiv_2deliminate s1 a0 a1 a2 a3) (fun s' t => Represents.rep s' t (__eo_prog_bv_sdiv_eliminate x_a0 x_a1 x_a2 x_a3))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fbv_2dsdiv_2deliminate_spec m (ih m hm) s1 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn)))
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

end pathos_compiled_checker
