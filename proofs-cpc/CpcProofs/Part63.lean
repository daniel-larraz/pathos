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

set_option maxHeartbeats 20000000 in
theorem case_0_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d3_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 a6 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) (h_a6 : Represents.rep s a6 x_a6) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) (hn_a4 : x_a4 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d3 s a0 a1 a2 a3 a4 a5 a6 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_bv_sign_extend_ult_const_3.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_bv_sign_extend_ult_const_3.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d3
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a5 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_bv_sign_extend_ult_const_3.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_sign_extend_ult_const_3.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_sign_extend_ult_const_3.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a6 h_v4 h_v6 h_v7 dropping h_a5 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_3.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_3.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_3.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo_or.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a6 h_v4 h_v11 h_v13 h_v14 dropping h_v10 h_v6 h_v7 h_v8 he_v15 hinv1 e_v15 s1 v10 v6 v7 v8
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_3.case_0
  pat_unapply h_v14 as ⟨v17, v18, x_v17, x_v18, h_v17, h_v18, hn_v17, hn_v18⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_3.case_0
  pat_unapply h_v17 as ⟨v20, v21, x_v20, x_v21, h_v20, h_v21, hn_v20, hn_v21⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_3.case_0
  step as ⟨e_v22, he_v22⟩
  store_step with CtorSpec.eo_bvult.construct s2 e_v22 (by rw [he_v22]; exact empty_args) hinv2 h64 as ⟨v22, s3, hinv3, h_v22⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a6 h_v4 h_v11 h_v18 h_v20 h_v21 dropping h_v13 h_v14 h_v15 h_v17 he_v22 hinv2 e_v22 s2 v13 v14 v15 v17
  pat_same v20 v22 with h_v20 h_v22 using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_3.case_0
  pat_unapply h_v21 as ⟨v24, v25, x_v24, x_v25, h_v24, h_v25, hn_v24, hn_v25⟩ using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_3.case_0
  pat_destruct CtorSpec.eo_int_5fto_5fbv.destruct h_v24 as ⟨v27, x_v27, h_v27⟩ else hinv3 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_3.case_0
  obtain hn_v27 := CtorSpec.eo_int_5fto_5fbv.fields_ne_stuck hinv3 h_v24
  pat_same v27 a3 with h_v27 h_a3 using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_3.case_0
  pat_same v25 a2 with h_v25 h_a2 using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_3.case_0
  pat_unapply h_v18 as ⟨v29, v30, x_v29, x_v30, h_v29, h_v30, hn_v29, hn_v30⟩ using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_3.case_0
  pat_unapply h_v29 as ⟨v32, v33, x_v32, x_v33, h_v32, h_v33, hn_v32, hn_v33⟩ using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_3.case_0
  step as ⟨e_v34, he_v34⟩
  store_step with CtorSpec.eo_bvshl.construct s3 e_v34 (by rw [he_v34]; exact empty_args) hinv3 h64 as ⟨v34, s4, hinv4, h_v34⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a6 h_v4 h_v11 h_v30 h_v32 h_v33 dropping h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v27 h_v29 he_v34 hinv3 e_v34 s3 v18 v20 v21 v22 v24 v25 v27 v29
  pat_same v32 v34 with h_v32 h_v34 using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_3.case_0
  pat_unapply h_v33 as ⟨v36, v37, x_v36, x_v37, h_v36, h_v37, hn_v36, hn_v37⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_3.case_0
  pat_destruct CtorSpec.eo_int_5fto_5fbv.destruct h_v36 as ⟨v39, x_v39, h_v39⟩ else hinv4 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_3.case_0
  obtain hn_v39 := CtorSpec.eo_int_5fto_5fbv.fields_ne_stuck hinv4 h_v36
  pat_same v39 a3 with h_v39 h_a3 using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_3.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s4 1#u32 (1) (by scalar_tac) hinv4 h64 as ⟨v40, s5, hinv5, h_v40⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a6 h_v4 h_v11 h_v30 h_v37 dropping h_v32 h_v33 h_v34 h_v36 h_v39 hinv4 s4 v32 v33 v34 v36 v39
  pat_same v37 v40 with h_v37 h_v40 using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_3.case_0
  pat_unapply h_v30 as ⟨v42, v43, x_v42, x_v43, h_v42, h_v43, hn_v42, hn_v43⟩ using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_3.case_0
  pat_destruct CtorSpec.eo_int_5fto_5fbv.destruct h_v42 as ⟨v45, x_v45, h_v45⟩ else hinv5 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_3.case_0
  obtain hn_v45 := CtorSpec.eo_int_5fto_5fbv.fields_ne_stuck hinv5 h_v42
  pat_same v45 a3 with h_v45 h_a3 using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_3.case_0
  pat_unapply h_v43 as ⟨v47, v48, x_v47, x_v48, h_v47, h_v48, hn_v47, hn_v48⟩ using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_3.case_0
  pat_unapply h_v47 as ⟨v50, v51, x_v50, x_v51, h_v50, h_v51, hn_v50, hn_v51⟩ using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_3.case_0
  step as ⟨e_v52, he_v52⟩
  store_step with CtorSpec.eo__2d.construct s5 e_v52 (by rw [he_v52]; exact empty_args) hinv5 h64 as ⟨v52, s6, hinv6, h_v52⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a6 h_v4 h_v11 h_v48 h_v50 h_v51 dropping h_v30 h_v37 h_v40 h_v42 h_v43 h_v45 h_v47 he_v52 hinv5 e_v52 s5 v30 v37 v40 v42 v43 v45 v47
  pat_same v50 v52 with h_v50 h_v52 using hinv6 else hinv6 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_3.case_0
  pat_unapply h_v51 as ⟨v54, v55, x_v54, x_v55, h_v54, h_v55, hn_v54, hn_v55⟩ using hinv6 else hinv6 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_3.case_0
  step as ⟨e_v56, he_v56⟩
  store_step with CtorSpec.eo__40bvsize.construct s6 e_v56 (by rw [he_v56]; exact empty_args) hinv6 h64 as ⟨v56, s7, hinv7, h_v56⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a6 h_v4 h_v11 h_v48 h_v54 h_v55 dropping h_v50 h_v51 h_v52 he_v56 hinv6 e_v56 s6 v50 v51 v52
  pat_same v54 v56 with h_v54 h_v56 using hinv7 else hinv7 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_3.case_0
  pat_same v55 a0 with h_v55 h_a0 using hinv7 else hinv7 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_3.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s7 1#u32 (1) (by scalar_tac) hinv7 h64 as ⟨v57, s8, hinv8, h_v57⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a6 h_v4 h_v11 h_v48 dropping h_v54 h_v55 h_v56 hinv7 s7 v54 v55 v56
  pat_same v48 v57 with h_v48 h_v57 using hinv8 else hinv8 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_3.case_0
  pat_unapply h_v11 as ⟨v59, v60, x_v59, x_v60, h_v59, h_v60, hn_v59, hn_v60⟩ using hinv8 else hinv8 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_3.case_0
  pat_unapply h_v59 as ⟨v62, v63, x_v62, x_v63, h_v62, h_v63, hn_v62, hn_v63⟩ using hinv8 else hinv8 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_3.case_0
  step as ⟨e_v64, he_v64⟩
  store_step with CtorSpec.eo_or.construct s8 e_v64 (by rw [he_v64]; exact empty_args) hinv8 h64 as ⟨v64, s9, hinv9, h_v64⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a6 h_v4 h_v60 h_v62 h_v63 dropping h_v11 h_v48 h_v57 h_v59 he_v64 hinv8 e_v64 s8 v11 v48 v57 v59
  pat_same v62 v64 with h_v62 h_v64 using hinv9 else hinv9 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_3.case_0
  pat_unapply h_v63 as ⟨v66, v67, x_v66, x_v67, h_v66, h_v67, hn_v66, hn_v67⟩ using hinv9 else hinv9 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_3.case_0
  pat_unapply h_v66 as ⟨v69, v70, x_v69, x_v70, h_v69, h_v70, hn_v69, hn_v70⟩ using hinv9 else hinv9 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_3.case_0
  step as ⟨e_v71, he_v71⟩
  store_step with CtorSpec.eo_bvuge.construct s9 e_v71 (by rw [he_v71]; exact empty_args) hinv9 h64 as ⟨v71, s10, hinv10, h_v71⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a6 h_v4 h_v60 h_v67 h_v69 h_v70 dropping h_v62 h_v63 h_v64 h_v66 he_v71 hinv9 e_v71 s9 v62 v63 v64 v66
  pat_same v69 v71 with h_v69 h_v71 using hinv10 else hinv10 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_3.case_0
  pat_unapply h_v70 as ⟨v73, v74, x_v73, x_v74, h_v73, h_v74, hn_v73, hn_v74⟩ using hinv10 else hinv10 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_3.case_0
  pat_destruct CtorSpec.eo_int_5fto_5fbv.destruct h_v73 as ⟨v76, x_v76, h_v76⟩ else hinv10 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_3.case_0
  obtain hn_v76 := CtorSpec.eo_int_5fto_5fbv.fields_ne_stuck hinv10 h_v73
  pat_same v76 a3 with h_v76 h_a3 using hinv10 else hinv10 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_3.case_0
  pat_same v74 a2 with h_v74 h_a2 using hinv10 else hinv10 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_3.case_0
  pat_unapply h_v67 as ⟨v78, v79, x_v78, x_v79, h_v78, h_v79, hn_v78, hn_v79⟩ using hinv10 else hinv10 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_3.case_0
  step as ⟨e_v80, he_v80⟩
  store_step with CtorSpec.eo_bvnot.construct s10 e_v80 (by rw [he_v80]; exact empty_args) hinv10 h64 as ⟨v80, s11, hinv11, h_v80⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a6 h_v4 h_v60 h_v78 h_v79 dropping h_v67 h_v69 h_v70 h_v71 h_v73 h_v74 h_v76 he_v80 hinv10 e_v80 s10 v67 v69 v70 v71 v73 v74 v76
  pat_same v78 v80 with h_v78 h_v80 using hinv11 else hinv11 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_3.case_0
  pat_unapply h_v79 as ⟨v82, v83, x_v82, x_v83, h_v82, h_v83, hn_v82, hn_v83⟩ using hinv11 else hinv11 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_3.case_0
  pat_unapply h_v82 as ⟨v85, v86, x_v85, x_v86, h_v85, h_v86, hn_v85, hn_v86⟩ using hinv11 else hinv11 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_3.case_0
  step as ⟨e_v87, he_v87⟩
  store_step with CtorSpec.eo_bvshl.construct s11 e_v87 (by rw [he_v87]; exact empty_args) hinv11 h64 as ⟨v87, s12, hinv12, h_v87⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a6 h_v4 h_v60 h_v83 h_v85 h_v86 dropping h_v78 h_v79 h_v80 h_v82 he_v87 hinv11 e_v87 s11 v78 v79 v80 v82
  pat_same v85 v87 with h_v85 h_v87 using hinv12 else hinv12 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_3.case_0
  pat_unapply h_v86 as ⟨v89, v90, x_v89, x_v90, h_v89, h_v90, hn_v89, hn_v90⟩ using hinv12 else hinv12 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_3.case_0
  pat_destruct CtorSpec.eo_int_5fto_5fbv.destruct h_v89 as ⟨v92, x_v92, h_v92⟩ else hinv12 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_3.case_0
  obtain hn_v92 := CtorSpec.eo_int_5fto_5fbv.fields_ne_stuck hinv12 h_v89
  pat_same v92 a3 with h_v92 h_a3 using hinv12 else hinv12 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_3.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s12 1#u32 (1) (by scalar_tac) hinv12 h64 as ⟨v93, s13, hinv13, h_v93⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a6 h_v4 h_v60 h_v83 h_v90 dropping h_v85 h_v86 h_v87 h_v89 h_v92 hinv12 s12 v85 v86 v87 v89 v92
  pat_same v90 v93 with h_v90 h_v93 using hinv13 else hinv13 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_3.case_0
  pat_unapply h_v83 as ⟨v95, v96, x_v95, x_v96, h_v95, h_v96, hn_v95, hn_v96⟩ using hinv13 else hinv13 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_3.case_0
  pat_destruct CtorSpec.eo_int_5fto_5fbv.destruct h_v95 as ⟨v98, x_v98, h_v98⟩ else hinv13 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_3.case_0
  obtain hn_v98 := CtorSpec.eo_int_5fto_5fbv.fields_ne_stuck hinv13 h_v95
  pat_same v98 a3 with h_v98 h_a3 using hinv13 else hinv13 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_3.case_0
  pat_unapply h_v96 as ⟨v100, v101, x_v100, x_v101, h_v100, h_v101, hn_v100, hn_v101⟩ using hinv13 else hinv13 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_3.case_0
  pat_unapply h_v100 as ⟨v103, v104, x_v103, x_v104, h_v103, h_v104, hn_v103, hn_v104⟩ using hinv13 else hinv13 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_3.case_0
  step as ⟨e_v105, he_v105⟩
  store_step with CtorSpec.eo__2d.construct s13 e_v105 (by rw [he_v105]; exact empty_args) hinv13 h64 as ⟨v105, s14, hinv14, h_v105⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a6 h_v4 h_v60 h_v101 h_v103 h_v104 dropping h_v100 h_v83 h_v90 h_v93 h_v95 h_v96 h_v98 he_v105 hinv13 e_v105 s13 v100 v83 v90 v93 v95 v96 v98
  pat_same v103 v105 with h_v103 h_v105 using hinv14 else hinv14 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_3.case_0
  pat_unapply h_v104 as ⟨v107, v108, x_v107, x_v108, h_v107, h_v108, hn_v107, hn_v108⟩ using hinv14 else hinv14 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_3.case_0
  step as ⟨e_v109, he_v109⟩
  store_step with CtorSpec.eo__40bvsize.construct s14 e_v109 (by rw [he_v109]; exact empty_args) hinv14 h64 as ⟨v109, s15, hinv15, h_v109⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a6 h_v4 h_v60 h_v101 h_v107 h_v108 dropping h_v103 h_v104 h_v105 he_v109 hinv14 e_v109 s14 v103 v104 v105
  pat_same v107 v109 with h_v107 h_v109 using hinv15 else hinv15 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_3.case_0
  pat_same v108 a0 with h_v108 h_a0 using hinv15 else hinv15 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_3.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s15 1#u32 (1) (by scalar_tac) hinv15 h64 as ⟨v110, s16, hinv16, h_v110⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a6 h_v4 h_v60 h_v101 dropping h_v107 h_v108 h_v109 hinv15 s15 v107 v108 v109
  pat_same v101 v110 with h_v101 h_v110 using hinv16 else hinv16 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_3.case_0
  store_step with Store.literal_boolean_spec s16 false hinv16 h64 as ⟨v111, s17, hinv17, h_v111⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a6 h_v4 h_v60 dropping h_v101 h_v110 hinv16 s16 v101 v110
  pat_same v60 v111 with h_v60 h_v111 using hinv17 else hinv17 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_3.case_0
  store_step with Store.literal_boolean_spec s17 true hinv17 h64 as ⟨v112, s18, hinv18, h_v112⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a6 h_v4 dropping h_v111 h_v60 hinv17 s17 v111 v60
  pat_same v4 v112 with h_v4 h_v112 using hinv18 else hinv18 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_3.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a6 as ⟨v114, x_v114, h_v114⟩ else hinv18 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_3.case_0
  pat_unapply h_v114 as ⟨v116, v117, x_v116, x_v117, h_v116, h_v117, hn_v116, hn_v117⟩ using hinv18 else hinv18 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_3.case_0
  pat_unapply h_v116 as ⟨v119, v120, x_v119, x_v120, h_v119, h_v120, hn_v119, hn_v120⟩ using hinv18 else hinv18 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_3.case_0
  step as ⟨e_v121, he_v121⟩
  store_step with CtorSpec.eo__3d.construct s18 e_v121 (by rw [he_v121]; exact empty_args) hinv18 h64 as ⟨v121, s19, hinv19, h_v121⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v117 h_v119 h_v120 dropping h_a6 h_v112 h_v114 h_v116 h_v4 he_v121 hinv18 e_v121 s18 v112 v114 v116 v4
  pat_same v119 v121 with h_v119 h_v121 using hinv19 else hinv19 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_3.case_0
  pat_same v120 a4 with h_v120 h_a4 using hinv19 else hinv19 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_3.case_0
  pat_unapply h_v117 as ⟨v123, v124, x_v123, x_v124, h_v123, h_v124, hn_v123, hn_v124⟩ using hinv19 else hinv19 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_3.case_0
  pat_unapply h_v123 as ⟨v126, v127, x_v126, x_v127, h_v126, h_v127, hn_v126, hn_v127⟩ using hinv19 else hinv19 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_3.case_0
  step as ⟨e_v128, he_v128⟩
  store_step with CtorSpec.eo__2d.construct s19 e_v128 (by rw [he_v128]; exact empty_args) hinv19 h64 as ⟨v128, s20, hinv20, h_v128⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v124 h_v126 h_v127 dropping h_v117 h_v119 h_v120 h_v121 h_v123 he_v128 hinv19 e_v128 s19 v117 v119 v120 v121 v123
  pat_same v126 v128 with h_v126 h_v128 using hinv20 else hinv20 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_3.case_0
  pat_unapply h_v127 as ⟨v130, v131, x_v130, x_v131, h_v130, h_v131, hn_v130, hn_v131⟩ using hinv20 else hinv20 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_3.case_0
  step as ⟨e_v132, he_v132⟩
  store_step with CtorSpec.eo__40bvsize.construct s20 e_v132 (by rw [he_v132]; exact empty_args) hinv20 h64 as ⟨v132, s21, hinv21, h_v132⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v124 h_v130 h_v131 dropping h_v126 h_v127 h_v128 he_v132 hinv20 e_v132 s20 v126 v127 v128
  pat_same v130 v132 with h_v130 h_v132 using hinv21 else hinv21 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_3.case_0
  pat_same v131 a0 with h_v131 h_a0 using hinv21 else hinv21 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_3.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s21 1#u32 (1) (by scalar_tac) hinv21 h64 as ⟨v133, s22, hinv22, h_v133⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v124 dropping h_v130 h_v131 h_v132 hinv21 s21 v130 v131 v132
  pat_same v124 v133 with h_v124 h_v133 using hinv22 else hinv22 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_3.case_0
  step as ⟨e_v134, he_v134⟩
  store_step with CtorSpec.eo__3d.construct s22 e_v134 (by rw [he_v134]; exact empty_args) hinv22 h64 as ⟨v134, s23, hinv23, h_v134⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 dropping h_v124 h_v133 he_v134 hinv22 e_v134 s22 v124 v133
  step as ⟨e_v135, he_v135⟩
  store_step with CtorSpec.eo_bvult.construct s23 e_v135 (by rw [he_v135]; exact empty_args) hinv23 h64 as ⟨v135, s24, hinv24, h_v135⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v134 dropping he_v135 hinv23 e_v135 s23
  step as ⟨e_v136, he_v136⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s24 e_v136 (by rw [he_v136]; rfl) h_a3 hinv24 h64 as ⟨v136, s25, hinv25, h_v136⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v134 h_v135 dropping he_v136 hinv24 e_v136 s24
  store_step with Store.apply_rep s25 v136 a2 _ _ hinv25 h64 h_v136 h_a2 (by ns_tac) (by ns_tac) as ⟨v137, s26, hinv26, h_v137⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v134 h_v135 dropping h_v136 hinv25 s25 v136
  store_step with Store.apply_rep s26 v135 v137 _ _ hinv26 h64 h_v135 h_v137 (by ns_tac) (by ns_tac) as ⟨v138, s27, hinv27, h_v138⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v134 dropping h_v135 h_v137 hinv26 s26 v135 v137
  step as ⟨e_v139, he_v139⟩
  store_step with CtorSpec.eo_sign_5fextend.construct s27 e_v139 (by rw [he_v139]; rfl) h_a1 hinv27 h64 as ⟨v139, s28, hinv28, h_v139⟩ growing hG carrying h_a0 h_a2 h_a3 h_a4 h_v134 h_v138 dropping h_a1 he_v139 hinv27 e_v139 s27
  store_step with Store.apply_rep s28 v139 a0 _ _ hinv28 h64 h_v139 h_a0 (by ns_tac) (by ns_tac) as ⟨v140, s29, hinv29, h_v140⟩ growing hG carrying h_a0 h_a2 h_a3 h_a4 h_v134 h_v138 dropping h_v139 hinv28 s28 v139
  store_step with Store.apply_rep s29 v138 v140 _ _ hinv29 h64 h_v138 h_v140 (by ns_tac) (by ns_tac) as ⟨v141, s30, hinv30, h_v141⟩ growing hG carrying h_a0 h_a2 h_a3 h_a4 h_v134 dropping h_v138 h_v140 hinv29 s29 v138 v140
  store_step with Store.apply_rep s30 v134 v141 _ _ hinv30 h64 h_v134 h_v141 (by ns_tac) (by ns_tac) as ⟨v142, s31, hinv31, h_v142⟩ growing hG carrying h_a0 h_a2 h_a3 h_a4 dropping h_v134 h_v141 hinv30 s30 v134 v141
  step as ⟨e_v143, he_v143⟩
  store_step with CtorSpec.eo_bvult.construct s31 e_v143 (by rw [he_v143]; exact empty_args) hinv31 h64 as ⟨v143, s32, hinv32, h_v143⟩ growing hG carrying h_a0 h_a2 h_a3 h_a4 h_v142 dropping he_v143 hinv31 e_v143 s31
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s32 0#u32 (0) (by scalar_tac) hinv32 h64 as ⟨v144, s33, hinv33, h_v144⟩ growing hG carrying h_a0 h_a2 h_a3 h_a4 h_v142 h_v143 dropping hinv32 s32
  step as ⟨e_v145, he_v145⟩
  store_step with CtorSpec.eo_extract.construct s33 e_v145 (by rw [he_v145]; rfl) h_a4 h_v144 hinv33 h64 as ⟨v145, s34, hinv34, h_v145⟩ growing hG carrying h_a0 h_a2 h_a3 h_v142 h_v143 dropping h_a4 h_v144 he_v145 hinv33 e_v145 s33 v144
  step as ⟨e_v146, he_v146⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s34 e_v146 (by rw [he_v146]; rfl) h_a3 hinv34 h64 as ⟨v146, s35, hinv35, h_v146⟩ growing hG carrying h_a0 h_a2 h_v142 h_v143 h_v145 dropping h_a3 he_v146 hinv34 e_v146 s34
  store_step with Store.apply_rep s35 v146 a2 _ _ hinv35 h64 h_v146 h_a2 (by ns_tac) (by ns_tac) as ⟨v147, s36, hinv36, h_v147⟩ growing hG carrying h_a0 h_v142 h_v143 h_v145 dropping h_a2 h_v146 hinv35 s35 v146
  store_step with Store.apply_rep s36 v145 v147 _ _ hinv36 h64 h_v145 h_v147 (by ns_tac) (by ns_tac) as ⟨v148, s37, hinv37, h_v148⟩ growing hG carrying h_a0 h_v142 h_v143 dropping h_v145 h_v147 hinv36 s36 v145 v147
  store_step with Store.apply_rep s37 v143 v148 _ _ hinv37 h64 h_v143 h_v148 (by ns_tac) (by ns_tac) as ⟨v149, s38, hinv38, h_v149⟩ growing hG carrying h_a0 h_v142 dropping h_v143 h_v148 hinv37 s37 v143 v148
  store_step with Store.apply_rep s38 v149 a0 _ _ hinv38 h64 h_v149 h_a0 (by ns_tac) (by ns_tac) as ⟨v150, s39, hinv39, h_v150⟩ growing hG carrying h_v142 dropping h_a0 h_v149 hinv38 s38 v149
  store_step with Store.apply_rep s39 v142 v150 _ _ hinv39 h64 h_v142 h_v150 (by ns_tac) (by ns_tac) as ⟨v151, s40, hinv40, h_v151⟩ growing hG carrying dropping h_v142 h_v150 hinv39 s39 v142 v150
  case_done hinv40 hG with h_v151 in EoCases.__eo_prog_bv_sign_extend_ult_const_3.case_0 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v13 hn_v14 hn_v17 hn_v18 hn_v20 hn_v21 hn_v24 hn_v25 hn_v27 hn_v29 hn_v30 hn_v32 hn_v33 hn_v36 hn_v37 hn_v39 hn_v42 hn_v43 hn_v45 hn_v47 hn_v48 hn_v50 hn_v51 hn_v54 hn_v55 hn_v59 hn_v60 hn_v62 hn_v63 hn_v66 hn_v67 hn_v69 hn_v70 hn_v73 hn_v74 hn_v76 hn_v78 hn_v79 hn_v82 hn_v83 hn_v85 hn_v86 hn_v89 hn_v90 hn_v92 hn_v95 hn_v96 hn_v98 hn_v100 hn_v101 hn_v103 hn_v104 hn_v107 hn_v108 hn_v116 hn_v117 hn_v119 hn_v120 hn_v123 hn_v124 hn_v126 hn_v127 hn_v130 hn_v131

set_option maxHeartbeats 20000000 in
/-- logos's `__eo_prog_bv_sign_extend_ult_const_3` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d3.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) (hw_a4 : Valid.valid x_a4) (hw_a5 : Valid.valid x_a5) (hw_a6 : Valid.valid x_a6) :
    __eo_prog_bv_sign_extend_ult_const_3 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else if x_a4 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_bv_sign_extend_ult_const_3.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_bv_sign_extend_ult_const_3
  unfold EoCases.__eo_prog_bv_sign_extend_ult_const_3.case_0
  logos_eq

set_option maxHeartbeats 20000000 in
theorem body_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d3_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 a6 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) (h_a6 : Represents.rep s a6 x_a6) :
    body_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d3 s a0 a1 a2 a3 a4 a5 a6 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_sign_extend_ult_const_3 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d3.rust_eq x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3) (by valid_tac hinv h_a4) (by valid_tac hinv h_a5) (by valid_tac hinv h_a6)]
  unfold body_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d3
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  stuck_check h_a3 : x_a3 as hn_a3 else hinv hG
  stuck_check h_a4 : x_a4 as hn_a4 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d3_spec n ih s a0 a1 a2 a3 a4 a5 a6 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 hn_a0 hn_a1 hn_a2 hn_a3 hn_a4
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hc0 in EoCases.__eo_prog_bv_sign_extend_ult_const_3.case_0

set_option maxHeartbeats 20000000 in
theorem eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d3_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d3.Spec n := by
  intro s a0 a1 a2 a3 a4 a5 a6 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6
  unfold eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d3
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d3 s1 a0 a1 a2 a3 a4 a5 a6) (fun s' t => Represents.rep s' t (__eo_prog_bv_sign_extend_ult_const_3 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d3_spec m (ih m hm) s1 a0 a1 a2 a3 a4 a5 a6 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn) (by congr_one h_a4 hn) (by congr_one h_a5 hn) (by congr_one h_a6 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

end pathos_compiled_checker
