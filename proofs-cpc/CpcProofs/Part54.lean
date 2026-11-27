module
public import CpcProofs.Head
public import CpcChecker
public import Cpc.Logos
import all Cpc.Logos
public import Cpc.SmtTranslate
import all Cpc.SmtTranslate
public import Cpc.SmtModel
import all Cpc.SmtModel
public import CpcCases
import all CpcCases
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

set_option maxHeartbeats 4000000 in
/-- logos's `__eo_prog_bv_mult_slt_mult_1` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fbv_2dmult_2dslt_2dmult_2d1.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _) (x_a7 : _) (x_a8 : _) (x_a9 : _) (x_a10 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) (hw_a4 : Valid.valid x_a4) (hw_a5 : Valid.valid x_a5) (hw_a6 : Valid.valid x_a6) (hw_a7 : Valid.valid x_a7) (hw_a8 : Valid.valid x_a8) (hw_a9 : Valid.valid x_a9) (hw_a10 : Valid.valid x_a10) :
    __eo_prog_bv_mult_slt_mult_1 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 x_a9 x_a10 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else if x_a4 = Eo.Term.Stuck then HasStuck.stuck else if x_a5 = Eo.Term.Stuck then HasStuck.stuck else if x_a6 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_bv_mult_slt_mult_1.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 x_a9 x_a10] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_bv_mult_slt_mult_1
  unfold EoCases.__eo_prog_bv_mult_slt_mult_1.case_0
  logos_eq

set_option maxHeartbeats 4000000 in
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

set_option maxHeartbeats 4000000 in
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

end pathos_compiled_checker
