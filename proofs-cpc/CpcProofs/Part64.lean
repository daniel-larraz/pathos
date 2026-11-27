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
theorem case_0_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d4_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 a6 a7 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _) (x_a7 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) (h_a6 : Represents.rep s a6 x_a6) (h_a7 : Represents.rep s a7 x_a7) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) (hn_a4 : x_a4 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d4 s a0 a1 a2 a3 a4 a5 a6 a7 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_bv_sign_extend_ult_const_4.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_bv_sign_extend_ult_const_4.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d4
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a5 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_bv_sign_extend_ult_const_4.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_sign_extend_ult_const_4.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_sign_extend_ult_const_4.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a6 h_a7 h_v4 h_v6 h_v7 dropping h_a5 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_4.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_4.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_4.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo_bvule.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a6 h_a7 h_v4 h_v11 h_v13 h_v14 dropping h_v10 h_v6 h_v7 h_v8 he_v15 hinv1 e_v15 s1 v10 v6 v7 v8
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_4.case_0
  pat_unapply h_v14 as ⟨v17, v18, x_v17, x_v18, h_v17, h_v18, hn_v17, hn_v18⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_4.case_0
  step as ⟨e_v19, he_v19⟩
  store_step with CtorSpec.eo_bvnot.construct s2 e_v19 (by rw [he_v19]; exact empty_args) hinv2 h64 as ⟨v19, s3, hinv3, h_v19⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a6 h_a7 h_v4 h_v11 h_v17 h_v18 dropping h_v13 h_v14 h_v15 he_v19 hinv2 e_v19 s2 v13 v14 v15
  pat_same v17 v19 with h_v17 h_v19 using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_4.case_0
  pat_unapply h_v18 as ⟨v21, v22, x_v21, x_v22, h_v21, h_v22, hn_v21, hn_v22⟩ using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_4.case_0
  pat_unapply h_v21 as ⟨v24, v25, x_v24, x_v25, h_v24, h_v25, hn_v24, hn_v25⟩ using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_4.case_0
  step as ⟨e_v26, he_v26⟩
  store_step with CtorSpec.eo_bvshl.construct s3 e_v26 (by rw [he_v26]; exact empty_args) hinv3 h64 as ⟨v26, s4, hinv4, h_v26⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a6 h_a7 h_v4 h_v11 h_v22 h_v24 h_v25 dropping h_v17 h_v18 h_v19 h_v21 he_v26 hinv3 e_v26 s3 v17 v18 v19 v21
  pat_same v24 v26 with h_v24 h_v26 using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_4.case_0
  pat_unapply h_v25 as ⟨v28, v29, x_v28, x_v29, h_v28, h_v29, hn_v28, hn_v29⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_4.case_0
  step as ⟨e_v30, he_v30⟩
  store_step with CtorSpec.eo_bvnot.construct s4 e_v30 (by rw [he_v30]; exact empty_args) hinv4 h64 as ⟨v30, s5, hinv5, h_v30⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a6 h_a7 h_v4 h_v11 h_v22 h_v28 h_v29 dropping h_v24 h_v25 h_v26 he_v30 hinv4 e_v30 s4 v24 v25 v26
  pat_same v28 v30 with h_v28 h_v30 using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_4.case_0
  pat_unapply h_v29 as ⟨v32, v33, x_v32, x_v33, h_v32, h_v33, hn_v32, hn_v33⟩ using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_4.case_0
  pat_destruct CtorSpec.eo_int_5fto_5fbv.destruct h_v32 as ⟨v35, x_v35, h_v35⟩ else hinv5 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_4.case_0
  obtain hn_v35 := CtorSpec.eo_int_5fto_5fbv.fields_ne_stuck hinv5 h_v32
  pat_same v35 a3 with h_v35 h_a3 using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_4.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s5 0#u32 (0) (by scalar_tac) hinv5 h64 as ⟨v36, s6, hinv6, h_v36⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a6 h_a7 h_v4 h_v11 h_v22 h_v33 dropping h_v28 h_v29 h_v30 h_v32 h_v35 hinv5 s5 v28 v29 v30 v32 v35
  pat_same v33 v36 with h_v33 h_v36 using hinv6 else hinv6 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_4.case_0
  pat_unapply h_v22 as ⟨v38, v39, x_v38, x_v39, h_v38, h_v39, hn_v38, hn_v39⟩ using hinv6 else hinv6 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_4.case_0
  pat_destruct CtorSpec.eo_int_5fto_5fbv.destruct h_v38 as ⟨v41, x_v41, h_v41⟩ else hinv6 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_4.case_0
  obtain hn_v41 := CtorSpec.eo_int_5fto_5fbv.fields_ne_stuck hinv6 h_v38
  pat_same v41 a3 with h_v41 h_a3 using hinv6 else hinv6 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_4.case_0
  pat_unapply h_v39 as ⟨v43, v44, x_v43, x_v44, h_v43, h_v44, hn_v43, hn_v44⟩ using hinv6 else hinv6 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_4.case_0
  pat_unapply h_v43 as ⟨v46, v47, x_v46, x_v47, h_v46, h_v47, hn_v46, hn_v47⟩ using hinv6 else hinv6 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_4.case_0
  step as ⟨e_v48, he_v48⟩
  store_step with CtorSpec.eo__2d.construct s6 e_v48 (by rw [he_v48]; exact empty_args) hinv6 h64 as ⟨v48, s7, hinv7, h_v48⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a6 h_a7 h_v4 h_v11 h_v44 h_v46 h_v47 dropping h_v22 h_v33 h_v36 h_v38 h_v39 h_v41 h_v43 he_v48 hinv6 e_v48 s6 v22 v33 v36 v38 v39 v41 v43
  pat_same v46 v48 with h_v46 h_v48 using hinv7 else hinv7 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_4.case_0
  pat_unapply h_v47 as ⟨v50, v51, x_v50, x_v51, h_v50, h_v51, hn_v50, hn_v51⟩ using hinv7 else hinv7 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_4.case_0
  step as ⟨e_v52, he_v52⟩
  store_step with CtorSpec.eo__40bvsize.construct s7 e_v52 (by rw [he_v52]; exact empty_args) hinv7 h64 as ⟨v52, s8, hinv8, h_v52⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a6 h_a7 h_v4 h_v11 h_v44 h_v50 h_v51 dropping h_v46 h_v47 h_v48 he_v52 hinv7 e_v52 s7 v46 v47 v48
  pat_same v50 v52 with h_v50 h_v52 using hinv8 else hinv8 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_4.case_0
  pat_same v51 a0 with h_v51 h_a0 using hinv8 else hinv8 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_4.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s8 1#u32 (1) (by scalar_tac) hinv8 h64 as ⟨v53, s9, hinv9, h_v53⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a6 h_a7 h_v4 h_v11 h_v44 dropping h_v50 h_v51 h_v52 hinv8 s8 v50 v51 v52
  pat_same v44 v53 with h_v44 h_v53 using hinv9 else hinv9 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_4.case_0
  pat_unapply h_v11 as ⟨v55, v56, x_v55, x_v56, h_v55, h_v56, hn_v55, hn_v56⟩ using hinv9 else hinv9 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_4.case_0
  pat_destruct CtorSpec.eo_int_5fto_5fbv.destruct h_v55 as ⟨v58, x_v58, h_v58⟩ else hinv9 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_4.case_0
  obtain hn_v58 := CtorSpec.eo_int_5fto_5fbv.fields_ne_stuck hinv9 h_v55
  pat_same v58 a3 with h_v58 h_a3 using hinv9 else hinv9 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_4.case_0
  pat_same v56 a2 with h_v56 h_a2 using hinv9 else hinv9 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_4.case_0
  store_step with Store.literal_boolean_spec s9 true hinv9 h64 as ⟨v59, s10, hinv10, h_v59⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a6 h_a7 h_v4 dropping h_v11 h_v44 h_v53 h_v55 h_v56 h_v58 hinv9 s9 v11 v44 v53 v55 v56 v58
  pat_same v4 v59 with h_v4 h_v59 using hinv10 else hinv10 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_4.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a6 as ⟨v61, x_v61, h_v61⟩ else hinv10 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_4.case_0
  pat_unapply h_v61 as ⟨v63, v64, x_v63, x_v64, h_v63, h_v64, hn_v63, hn_v64⟩ using hinv10 else hinv10 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_4.case_0
  pat_unapply h_v63 as ⟨v66, v67, x_v66, x_v67, h_v66, h_v67, hn_v66, hn_v67⟩ using hinv10 else hinv10 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_4.case_0
  step as ⟨e_v68, he_v68⟩
  store_step with CtorSpec.eo__3d.construct s10 e_v68 (by rw [he_v68]; exact empty_args) hinv10 h64 as ⟨v68, s11, hinv11, h_v68⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a7 h_v64 h_v66 h_v67 dropping h_a6 h_v4 h_v59 h_v61 h_v63 he_v68 hinv10 e_v68 s10 v4 v59 v61 v63
  pat_same v66 v68 with h_v66 h_v68 using hinv11 else hinv11 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_4.case_0
  pat_unapply h_v67 as ⟨v70, v71, x_v70, x_v71, h_v70, h_v71, hn_v70, hn_v71⟩ using hinv11 else hinv11 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_4.case_0
  pat_unapply h_v70 as ⟨v73, v74, x_v73, x_v74, h_v73, h_v74, hn_v73, hn_v74⟩ using hinv11 else hinv11 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_4.case_0
  step as ⟨e_v75, he_v75⟩
  store_step with CtorSpec.eo_bvule.construct s11 e_v75 (by rw [he_v75]; exact empty_args) hinv11 h64 as ⟨v75, s12, hinv12, h_v75⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a7 h_v64 h_v71 h_v73 h_v74 dropping h_v66 h_v67 h_v68 h_v70 he_v75 hinv11 e_v75 s11 v66 v67 v68 v70
  pat_same v73 v75 with h_v73 h_v75 using hinv12 else hinv12 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_4.case_0
  pat_unapply h_v74 as ⟨v77, v78, x_v77, x_v78, h_v77, h_v78, hn_v77, hn_v78⟩ using hinv12 else hinv12 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_4.case_0
  pat_destruct CtorSpec.eo_int_5fto_5fbv.destruct h_v77 as ⟨v80, x_v80, h_v80⟩ else hinv12 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_4.case_0
  obtain hn_v80 := CtorSpec.eo_int_5fto_5fbv.fields_ne_stuck hinv12 h_v77
  pat_same v80 a3 with h_v80 h_a3 using hinv12 else hinv12 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_4.case_0
  pat_same v78 a2 with h_v78 h_a2 using hinv12 else hinv12 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_4.case_0
  pat_unapply h_v71 as ⟨v82, v83, x_v82, x_v83, h_v82, h_v83, hn_v82, hn_v83⟩ using hinv12 else hinv12 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_4.case_0
  step as ⟨e_v84, he_v84⟩
  store_step with CtorSpec.eo_bvnot.construct s12 e_v84 (by rw [he_v84]; exact empty_args) hinv12 h64 as ⟨v84, s13, hinv13, h_v84⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a7 h_v64 h_v82 h_v83 dropping h_v71 h_v73 h_v74 h_v75 h_v77 h_v78 h_v80 he_v84 hinv12 e_v84 s12 v71 v73 v74 v75 v77 v78 v80
  pat_same v82 v84 with h_v82 h_v84 using hinv13 else hinv13 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_4.case_0
  pat_unapply h_v83 as ⟨v86, v87, x_v86, x_v87, h_v86, h_v87, hn_v86, hn_v87⟩ using hinv13 else hinv13 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_4.case_0
  pat_unapply h_v86 as ⟨v89, v90, x_v89, x_v90, h_v89, h_v90, hn_v89, hn_v90⟩ using hinv13 else hinv13 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_4.case_0
  step as ⟨e_v91, he_v91⟩
  store_step with CtorSpec.eo_bvshl.construct s13 e_v91 (by rw [he_v91]; exact empty_args) hinv13 h64 as ⟨v91, s14, hinv14, h_v91⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a7 h_v64 h_v87 h_v89 h_v90 dropping h_v82 h_v83 h_v84 h_v86 he_v91 hinv13 e_v91 s13 v82 v83 v84 v86
  pat_same v89 v91 with h_v89 h_v91 using hinv14 else hinv14 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_4.case_0
  pat_unapply h_v90 as ⟨v93, v94, x_v93, x_v94, h_v93, h_v94, hn_v93, hn_v94⟩ using hinv14 else hinv14 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_4.case_0
  pat_destruct CtorSpec.eo_int_5fto_5fbv.destruct h_v93 as ⟨v96, x_v96, h_v96⟩ else hinv14 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_4.case_0
  obtain hn_v96 := CtorSpec.eo_int_5fto_5fbv.fields_ne_stuck hinv14 h_v93
  pat_same v96 a3 with h_v96 h_a3 using hinv14 else hinv14 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_4.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s14 1#u32 (1) (by scalar_tac) hinv14 h64 as ⟨v97, s15, hinv15, h_v97⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a7 h_v64 h_v87 h_v94 dropping h_v89 h_v90 h_v91 h_v93 h_v96 hinv14 s14 v89 v90 v91 v93 v96
  pat_same v94 v97 with h_v94 h_v97 using hinv15 else hinv15 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_4.case_0
  pat_unapply h_v87 as ⟨v99, v100, x_v99, x_v100, h_v99, h_v100, hn_v99, hn_v100⟩ using hinv15 else hinv15 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_4.case_0
  pat_destruct CtorSpec.eo_int_5fto_5fbv.destruct h_v99 as ⟨v102, x_v102, h_v102⟩ else hinv15 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_4.case_0
  obtain hn_v102 := CtorSpec.eo_int_5fto_5fbv.fields_ne_stuck hinv15 h_v99
  pat_same v102 a3 with h_v102 h_a3 using hinv15 else hinv15 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_4.case_0
  pat_unapply h_v100 as ⟨v104, v105, x_v104, x_v105, h_v104, h_v105, hn_v104, hn_v105⟩ using hinv15 else hinv15 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_4.case_0
  pat_unapply h_v104 as ⟨v107, v108, x_v107, x_v108, h_v107, h_v108, hn_v107, hn_v108⟩ using hinv15 else hinv15 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_4.case_0
  step as ⟨e_v109, he_v109⟩
  store_step with CtorSpec.eo__2d.construct s15 e_v109 (by rw [he_v109]; exact empty_args) hinv15 h64 as ⟨v109, s16, hinv16, h_v109⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a7 h_v64 h_v105 h_v107 h_v108 dropping h_v100 h_v102 h_v104 h_v87 h_v94 h_v97 h_v99 he_v109 hinv15 e_v109 s15 v100 v102 v104 v87 v94 v97 v99
  pat_same v107 v109 with h_v107 h_v109 using hinv16 else hinv16 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_4.case_0
  pat_unapply h_v108 as ⟨v111, v112, x_v111, x_v112, h_v111, h_v112, hn_v111, hn_v112⟩ using hinv16 else hinv16 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_4.case_0
  step as ⟨e_v113, he_v113⟩
  store_step with CtorSpec.eo__40bvsize.construct s16 e_v113 (by rw [he_v113]; exact empty_args) hinv16 h64 as ⟨v113, s17, hinv17, h_v113⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a7 h_v64 h_v105 h_v111 h_v112 dropping h_v107 h_v108 h_v109 he_v113 hinv16 e_v113 s16 v107 v108 v109
  pat_same v111 v113 with h_v111 h_v113 using hinv17 else hinv17 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_4.case_0
  pat_same v112 a0 with h_v112 h_a0 using hinv17 else hinv17 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_4.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s17 1#u32 (1) (by scalar_tac) hinv17 h64 as ⟨v114, s18, hinv18, h_v114⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a7 h_v64 h_v105 dropping h_v111 h_v112 h_v113 hinv17 s17 v111 v112 v113
  pat_same v105 v114 with h_v105 h_v114 using hinv18 else hinv18 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_4.case_0
  store_step with Store.literal_boolean_spec s18 true hinv18 h64 as ⟨v115, s19, hinv19, h_v115⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a7 h_v64 dropping h_v105 h_v114 hinv18 s18 v105 v114
  pat_same v64 v115 with h_v64 h_v115 using hinv19 else hinv19 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_4.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a7 as ⟨v117, x_v117, h_v117⟩ else hinv19 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_4.case_0
  pat_unapply h_v117 as ⟨v119, v120, x_v119, x_v120, h_v119, h_v120, hn_v119, hn_v120⟩ using hinv19 else hinv19 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_4.case_0
  pat_unapply h_v119 as ⟨v122, v123, x_v122, x_v123, h_v122, h_v123, hn_v122, hn_v123⟩ using hinv19 else hinv19 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_4.case_0
  step as ⟨e_v124, he_v124⟩
  store_step with CtorSpec.eo__3d.construct s19 e_v124 (by rw [he_v124]; exact empty_args) hinv19 h64 as ⟨v124, s20, hinv20, h_v124⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v120 h_v122 h_v123 dropping h_a7 h_v115 h_v117 h_v119 h_v64 he_v124 hinv19 e_v124 s19 v115 v117 v119 v64
  pat_same v122 v124 with h_v122 h_v124 using hinv20 else hinv20 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_4.case_0
  pat_same v123 a4 with h_v123 h_a4 using hinv20 else hinv20 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_4.case_0
  pat_unapply h_v120 as ⟨v126, v127, x_v126, x_v127, h_v126, h_v127, hn_v126, hn_v127⟩ using hinv20 else hinv20 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_4.case_0
  pat_unapply h_v126 as ⟨v129, v130, x_v129, x_v130, h_v129, h_v130, hn_v129, hn_v130⟩ using hinv20 else hinv20 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_4.case_0
  step as ⟨e_v131, he_v131⟩
  store_step with CtorSpec.eo__2d.construct s20 e_v131 (by rw [he_v131]; exact empty_args) hinv20 h64 as ⟨v131, s21, hinv21, h_v131⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v127 h_v129 h_v130 dropping h_v120 h_v122 h_v123 h_v124 h_v126 he_v131 hinv20 e_v131 s20 v120 v122 v123 v124 v126
  pat_same v129 v131 with h_v129 h_v131 using hinv21 else hinv21 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_4.case_0
  pat_unapply h_v130 as ⟨v133, v134, x_v133, x_v134, h_v133, h_v134, hn_v133, hn_v134⟩ using hinv21 else hinv21 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_4.case_0
  step as ⟨e_v135, he_v135⟩
  store_step with CtorSpec.eo__40bvsize.construct s21 e_v135 (by rw [he_v135]; exact empty_args) hinv21 h64 as ⟨v135, s22, hinv22, h_v135⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v127 h_v133 h_v134 dropping h_v129 h_v130 h_v131 he_v135 hinv21 e_v135 s21 v129 v130 v131
  pat_same v133 v135 with h_v133 h_v135 using hinv22 else hinv22 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_4.case_0
  pat_same v134 a0 with h_v134 h_a0 using hinv22 else hinv22 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_4.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s22 1#u32 (1) (by scalar_tac) hinv22 h64 as ⟨v136, s23, hinv23, h_v136⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v127 dropping h_v133 h_v134 h_v135 hinv22 s22 v133 v134 v135
  pat_same v127 v136 with h_v127 h_v136 using hinv23 else hinv23 hG in EoCases.__eo_prog_bv_sign_extend_ult_const_4.case_0
  step as ⟨e_v137, he_v137⟩
  store_step with CtorSpec.eo__3d.construct s23 e_v137 (by rw [he_v137]; exact empty_args) hinv23 h64 as ⟨v137, s24, hinv24, h_v137⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 dropping h_v127 h_v136 he_v137 hinv23 e_v137 s23 v127 v136
  step as ⟨e_v138, he_v138⟩
  store_step with CtorSpec.eo_bvult.construct s24 e_v138 (by rw [he_v138]; exact empty_args) hinv24 h64 as ⟨v138, s25, hinv25, h_v138⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v137 dropping he_v138 hinv24 e_v138 s24
  step as ⟨e_v139, he_v139⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s25 e_v139 (by rw [he_v139]; rfl) h_a3 hinv25 h64 as ⟨v139, s26, hinv26, h_v139⟩ growing hG carrying h_a0 h_a1 h_a2 h_a4 h_v137 h_v138 dropping h_a3 he_v139 hinv25 e_v139 s25
  store_step with Store.apply_rep s26 v139 a2 _ _ hinv26 h64 h_v139 h_a2 (by ns_tac) (by ns_tac) as ⟨v140, s27, hinv27, h_v140⟩ growing hG carrying h_a0 h_a1 h_a4 h_v137 h_v138 dropping h_a2 h_v139 hinv26 s26 v139
  store_step with Store.apply_rep s27 v138 v140 _ _ hinv27 h64 h_v138 h_v140 (by ns_tac) (by ns_tac) as ⟨v141, s28, hinv28, h_v141⟩ growing hG carrying h_a0 h_a1 h_a4 h_v137 dropping h_v138 h_v140 hinv27 s27 v138 v140
  step as ⟨e_v142, he_v142⟩
  store_step with CtorSpec.eo_sign_5fextend.construct s28 e_v142 (by rw [he_v142]; rfl) h_a1 hinv28 h64 as ⟨v142, s29, hinv29, h_v142⟩ growing hG carrying h_a0 h_a4 h_v137 h_v141 dropping h_a1 he_v142 hinv28 e_v142 s28
  store_step with Store.apply_rep s29 v142 a0 _ _ hinv29 h64 h_v142 h_a0 (by ns_tac) (by ns_tac) as ⟨v143, s30, hinv30, h_v143⟩ growing hG carrying h_a0 h_a4 h_v137 h_v141 dropping h_v142 hinv29 s29 v142
  store_step with Store.apply_rep s30 v141 v143 _ _ hinv30 h64 h_v141 h_v143 (by ns_tac) (by ns_tac) as ⟨v144, s31, hinv31, h_v144⟩ growing hG carrying h_a0 h_a4 h_v137 dropping h_v141 h_v143 hinv30 s30 v141 v143
  store_step with Store.apply_rep s31 v137 v144 _ _ hinv31 h64 h_v137 h_v144 (by ns_tac) (by ns_tac) as ⟨v145, s32, hinv32, h_v145⟩ growing hG carrying h_a0 h_a4 dropping h_v137 h_v144 hinv31 s31 v137 v144
  step as ⟨e_v146, he_v146⟩
  store_step with CtorSpec.eo__3d.construct s32 e_v146 (by rw [he_v146]; exact empty_args) hinv32 h64 as ⟨v146, s33, hinv33, h_v146⟩ growing hG carrying h_a0 h_a4 h_v145 dropping he_v146 hinv32 e_v146 s32
  step as ⟨e_v147, he_v147⟩
  store_step with CtorSpec.eo_extract.construct s33 e_v147 (by rw [he_v147]; rfl) h_a4 h_a4 hinv33 h64 as ⟨v147, s34, hinv34, h_v147⟩ growing hG carrying h_a0 h_v145 h_v146 dropping h_a4 he_v147 hinv33 e_v147 s33
  store_step with Store.apply_rep s34 v147 a0 _ _ hinv34 h64 h_v147 h_a0 (by ns_tac) (by ns_tac) as ⟨v148, s35, hinv35, h_v148⟩ growing hG carrying h_v145 h_v146 dropping h_a0 h_v147 hinv34 s34 v147
  store_step with Store.apply_rep s35 v146 v148 _ _ hinv35 h64 h_v146 h_v148 (by ns_tac) (by ns_tac) as ⟨v149, s36, hinv36, h_v149⟩ growing hG carrying h_v145 dropping h_v146 h_v148 hinv35 s35 v146 v148
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s36 1#u32 (1) (by scalar_tac) hinv36 h64 as ⟨v150, s37, hinv37, h_v150⟩ growing hG carrying h_v145 h_v149 dropping hinv36 s36
  step as ⟨e_v151, he_v151⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s37 e_v151 (by rw [he_v151]; rfl) h_v150 hinv37 h64 as ⟨v151, s38, hinv38, h_v151⟩ growing hG carrying h_v145 h_v149 dropping h_v150 he_v151 hinv37 e_v151 s37 v150
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s38 1#u32 (1) (by scalar_tac) hinv38 h64 as ⟨v152, s39, hinv39, h_v152⟩ growing hG carrying h_v145 h_v149 h_v151 dropping hinv38 s38
  store_step with Store.apply_rep s39 v151 v152 _ _ hinv39 h64 h_v151 h_v152 (by ns_tac) (by ns_tac) as ⟨v153, s40, hinv40, h_v153⟩ growing hG carrying h_v145 h_v149 dropping h_v151 h_v152 hinv39 s39 v151 v152
  store_step with Store.apply_rep s40 v149 v153 _ _ hinv40 h64 h_v149 h_v153 (by ns_tac) (by ns_tac) as ⟨v154, s41, hinv41, h_v154⟩ growing hG carrying h_v145 dropping h_v149 h_v153 hinv40 s40 v149 v153
  store_step with Store.apply_rep s41 v145 v154 _ _ hinv41 h64 h_v145 h_v154 (by ns_tac) (by ns_tac) as ⟨v155, s42, hinv42, h_v155⟩ growing hG carrying dropping h_v145 h_v154 hinv41 s41 v145 v154
  case_done hinv42 hG with h_v155 in EoCases.__eo_prog_bv_sign_extend_ult_const_4.case_0 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v13 hn_v14 hn_v17 hn_v18 hn_v21 hn_v22 hn_v24 hn_v25 hn_v28 hn_v29 hn_v32 hn_v33 hn_v35 hn_v38 hn_v39 hn_v41 hn_v43 hn_v44 hn_v46 hn_v47 hn_v50 hn_v51 hn_v55 hn_v56 hn_v58 hn_v63 hn_v64 hn_v66 hn_v67 hn_v70 hn_v71 hn_v73 hn_v74 hn_v77 hn_v78 hn_v80 hn_v82 hn_v83 hn_v86 hn_v87 hn_v89 hn_v90 hn_v93 hn_v94 hn_v96 hn_v99 hn_v100 hn_v102 hn_v104 hn_v105 hn_v107 hn_v108 hn_v111 hn_v112 hn_v119 hn_v120 hn_v122 hn_v123 hn_v126 hn_v127 hn_v129 hn_v130 hn_v133 hn_v134

set_option maxHeartbeats 20000000 in
/-- logos's `__eo_prog_bv_sign_extend_ult_const_4` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d4.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _) (x_a7 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) (hw_a4 : Valid.valid x_a4) (hw_a5 : Valid.valid x_a5) (hw_a6 : Valid.valid x_a6) (hw_a7 : Valid.valid x_a7) :
    __eo_prog_bv_sign_extend_ult_const_4 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else if x_a4 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_bv_sign_extend_ult_const_4.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_bv_sign_extend_ult_const_4
  unfold EoCases.__eo_prog_bv_sign_extend_ult_const_4.case_0
  logos_eq

set_option maxHeartbeats 20000000 in
theorem body_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d4_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 a6 a7 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _) (x_a7 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) (h_a6 : Represents.rep s a6 x_a6) (h_a7 : Represents.rep s a7 x_a7) :
    body_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d4 s a0 a1 a2 a3 a4 a5 a6 a7 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_sign_extend_ult_const_4 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d4.rust_eq x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3) (by valid_tac hinv h_a4) (by valid_tac hinv h_a5) (by valid_tac hinv h_a6) (by valid_tac hinv h_a7)]
  unfold body_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d4
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  stuck_check h_a3 : x_a3 as hn_a3 else hinv hG
  stuck_check h_a4 : x_a4 as hn_a4 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d4_spec n ih s a0 a1 a2 a3 a4 a5 a6 a7 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 hn_a0 hn_a1 hn_a2 hn_a3 hn_a4
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hc0 in EoCases.__eo_prog_bv_sign_extend_ult_const_4.case_0

set_option maxHeartbeats 20000000 in
theorem eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d4_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d4.Spec n := by
  intro s a0 a1 a2 a3 a4 a5 a6 a7 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7
  unfold eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d4
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d4 s1 a0 a1 a2 a3 a4 a5 a6 a7) (fun s' t => Represents.rep s' t (__eo_prog_bv_sign_extend_ult_const_4 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d4_spec m (ih m hm) s1 a0 a1 a2 a3 a4 a5 a6 a7 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn) (by congr_one h_a4 hn) (by congr_one h_a5 hn) (by congr_one h_a6 hn) (by congr_one h_a7 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

end pathos_compiled_checker
