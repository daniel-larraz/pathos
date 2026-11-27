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
theorem case_0_eo__24eo_5fprog_5fbv_2dextract_2dsign_2dextend_2d2_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _) (x_a7 : _) (x_a8 : _) (x_a9 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) (h_a6 : Represents.rep s a6 x_a6) (h_a7 : Represents.rep s a7 x_a7) (h_a8 : Represents.rep s a8 x_a8) (h_a9 : Represents.rep s a9 x_a9) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) (hn_a4 : x_a4 ≠ Eo.Term.Stuck) (hn_a5 : x_a5 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fbv_2dextract_2dsign_2dextend_2d2 s a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_bv_extract_sign_extend_2.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 x_a9 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_bv_extract_sign_extend_2.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 x_a9 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fbv_2dextract_2dsign_2dextend_2d2
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a6 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_bv_extract_sign_extend_2.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_extract_sign_extend_2.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_extract_sign_extend_2.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a7 h_a8 h_a9 h_v4 h_v6 h_v7 dropping h_a6 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_extract_sign_extend_2.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_extract_sign_extend_2.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_extract_sign_extend_2.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__3c.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a7 h_a8 h_a9 h_v4 h_v11 h_v13 h_v14 dropping h_v10 h_v6 h_v7 h_v8 he_v15 hinv1 e_v15 s1 v10 v6 v7 v8
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_extract_sign_extend_2.case_0
  pat_same v14 a1 with h_v14 h_a1 using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_extract_sign_extend_2.case_0
  pat_unapply h_v11 as ⟨v17, v18, x_v17, x_v18, h_v17, h_v18, hn_v17, hn_v18⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_extract_sign_extend_2.case_0
  step as ⟨e_v19, he_v19⟩
  store_step with CtorSpec.eo__40bvsize.construct s2 e_v19 (by rw [he_v19]; exact empty_args) hinv2 h64 as ⟨v19, s3, hinv3, h_v19⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a7 h_a8 h_a9 h_v4 h_v17 h_v18 dropping h_v11 h_v13 h_v14 h_v15 he_v19 hinv2 e_v19 s2 v11 v13 v14 v15
  pat_same v17 v19 with h_v17 h_v19 using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_extract_sign_extend_2.case_0
  pat_same v18 a0 with h_v18 h_a0 using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_extract_sign_extend_2.case_0
  store_step with Store.literal_boolean_spec s3 true hinv3 h64 as ⟨v20, s4, hinv4, h_v20⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a7 h_a8 h_a9 h_v4 dropping h_v17 h_v18 h_v19 hinv3 s3 v17 v18 v19
  pat_same v4 v20 with h_v4 h_v20 using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_extract_sign_extend_2.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a7 as ⟨v22, x_v22, h_v22⟩ else hinv4 hG in EoCases.__eo_prog_bv_extract_sign_extend_2.case_0
  pat_unapply h_v22 as ⟨v24, v25, x_v24, x_v25, h_v24, h_v25, hn_v24, hn_v25⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_extract_sign_extend_2.case_0
  pat_unapply h_v24 as ⟨v27, v28, x_v27, x_v28, h_v27, h_v28, hn_v27, hn_v28⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_extract_sign_extend_2.case_0
  step as ⟨e_v29, he_v29⟩
  store_step with CtorSpec.eo__3d.construct s4 e_v29 (by rw [he_v29]; exact empty_args) hinv4 h64 as ⟨v29, s5, hinv5, h_v29⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a8 h_a9 h_v25 h_v27 h_v28 dropping h_a7 h_v20 h_v22 h_v24 h_v4 he_v29 hinv4 e_v29 s4 v20 v22 v24 v4
  pat_same v27 v29 with h_v27 h_v29 using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_extract_sign_extend_2.case_0
  pat_unapply h_v28 as ⟨v31, v32, x_v31, x_v32, h_v31, h_v32, hn_v31, hn_v32⟩ using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_extract_sign_extend_2.case_0
  pat_unapply h_v31 as ⟨v34, v35, x_v34, x_v35, h_v34, h_v35, hn_v34, hn_v35⟩ using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_extract_sign_extend_2.case_0
  step as ⟨e_v36, he_v36⟩
  store_step with CtorSpec.eo__3e_3d.construct s5 e_v36 (by rw [he_v36]; exact empty_args) hinv5 h64 as ⟨v36, s6, hinv6, h_v36⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a8 h_a9 h_v25 h_v32 h_v34 h_v35 dropping h_v27 h_v28 h_v29 h_v31 he_v36 hinv5 e_v36 s5 v27 v28 v29 v31
  pat_same v34 v36 with h_v34 h_v36 using hinv6 else hinv6 hG in EoCases.__eo_prog_bv_extract_sign_extend_2.case_0
  pat_same v35 a2 with h_v35 h_a2 using hinv6 else hinv6 hG in EoCases.__eo_prog_bv_extract_sign_extend_2.case_0
  pat_unapply h_v32 as ⟨v38, v39, x_v38, x_v39, h_v38, h_v39, hn_v38, hn_v39⟩ using hinv6 else hinv6 hG in EoCases.__eo_prog_bv_extract_sign_extend_2.case_0
  step as ⟨e_v40, he_v40⟩
  store_step with CtorSpec.eo__40bvsize.construct s6 e_v40 (by rw [he_v40]; exact empty_args) hinv6 h64 as ⟨v40, s7, hinv7, h_v40⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a8 h_a9 h_v25 h_v38 h_v39 dropping h_v32 h_v34 h_v35 h_v36 he_v40 hinv6 e_v40 s6 v32 v34 v35 v36
  pat_same v38 v40 with h_v38 h_v40 using hinv7 else hinv7 hG in EoCases.__eo_prog_bv_extract_sign_extend_2.case_0
  pat_same v39 a0 with h_v39 h_a0 using hinv7 else hinv7 hG in EoCases.__eo_prog_bv_extract_sign_extend_2.case_0
  store_step with Store.literal_boolean_spec s7 true hinv7 h64 as ⟨v41, s8, hinv8, h_v41⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a8 h_a9 h_v25 dropping h_v38 h_v39 h_v40 hinv7 s7 v38 v39 v40
  pat_same v25 v41 with h_v25 h_v41 using hinv8 else hinv8 hG in EoCases.__eo_prog_bv_extract_sign_extend_2.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a8 as ⟨v43, x_v43, h_v43⟩ else hinv8 hG in EoCases.__eo_prog_bv_extract_sign_extend_2.case_0
  pat_unapply h_v43 as ⟨v45, v46, x_v45, x_v46, h_v45, h_v46, hn_v45, hn_v46⟩ using hinv8 else hinv8 hG in EoCases.__eo_prog_bv_extract_sign_extend_2.case_0
  pat_unapply h_v45 as ⟨v48, v49, x_v48, x_v49, h_v48, h_v49, hn_v48, hn_v49⟩ using hinv8 else hinv8 hG in EoCases.__eo_prog_bv_extract_sign_extend_2.case_0
  step as ⟨e_v50, he_v50⟩
  store_step with CtorSpec.eo__3d.construct s8 e_v50 (by rw [he_v50]; exact empty_args) hinv8 h64 as ⟨v50, s9, hinv9, h_v50⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a9 h_v46 h_v48 h_v49 dropping h_a8 h_v25 h_v41 h_v43 h_v45 he_v50 hinv8 e_v50 s8 v25 v41 v43 v45
  pat_same v48 v50 with h_v48 h_v50 using hinv9 else hinv9 hG in EoCases.__eo_prog_bv_extract_sign_extend_2.case_0
  pat_same v49 a4 with h_v49 h_a4 using hinv9 else hinv9 hG in EoCases.__eo_prog_bv_extract_sign_extend_2.case_0
  pat_unapply h_v46 as ⟨v52, v53, x_v52, x_v53, h_v52, h_v53, hn_v52, hn_v53⟩ using hinv9 else hinv9 hG in EoCases.__eo_prog_bv_extract_sign_extend_2.case_0
  pat_unapply h_v52 as ⟨v55, v56, x_v55, x_v56, h_v55, h_v56, hn_v55, hn_v56⟩ using hinv9 else hinv9 hG in EoCases.__eo_prog_bv_extract_sign_extend_2.case_0
  step as ⟨e_v57, he_v57⟩
  store_step with CtorSpec.eo__2d.construct s9 e_v57 (by rw [he_v57]; exact empty_args) hinv9 h64 as ⟨v57, s10, hinv10, h_v57⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a9 h_v53 h_v55 h_v56 dropping h_v46 h_v48 h_v49 h_v50 h_v52 he_v57 hinv9 e_v57 s9 v46 v48 v49 v50 v52
  pat_same v55 v57 with h_v55 h_v57 using hinv10 else hinv10 hG in EoCases.__eo_prog_bv_extract_sign_extend_2.case_0
  pat_unapply h_v56 as ⟨v59, v60, x_v59, x_v60, h_v59, h_v60, hn_v59, hn_v60⟩ using hinv10 else hinv10 hG in EoCases.__eo_prog_bv_extract_sign_extend_2.case_0
  step as ⟨e_v61, he_v61⟩
  store_step with CtorSpec.eo__40bvsize.construct s10 e_v61 (by rw [he_v61]; exact empty_args) hinv10 h64 as ⟨v61, s11, hinv11, h_v61⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a9 h_v53 h_v59 h_v60 dropping h_v55 h_v56 h_v57 he_v61 hinv10 e_v61 s10 v55 v56 v57
  pat_same v59 v61 with h_v59 h_v61 using hinv11 else hinv11 hG in EoCases.__eo_prog_bv_extract_sign_extend_2.case_0
  pat_same v60 a0 with h_v60 h_a0 using hinv11 else hinv11 hG in EoCases.__eo_prog_bv_extract_sign_extend_2.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s11 1#u32 (1) (by scalar_tac) hinv11 h64 as ⟨v62, s12, hinv12, h_v62⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a9 h_v53 dropping h_v59 h_v60 h_v61 hinv11 s11 v59 v60 v61
  pat_same v53 v62 with h_v53 h_v62 using hinv12 else hinv12 hG in EoCases.__eo_prog_bv_extract_sign_extend_2.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a9 as ⟨v64, x_v64, h_v64⟩ else hinv12 hG in EoCases.__eo_prog_bv_extract_sign_extend_2.case_0
  pat_unapply h_v64 as ⟨v66, v67, x_v66, x_v67, h_v66, h_v67, hn_v66, hn_v67⟩ using hinv12 else hinv12 hG in EoCases.__eo_prog_bv_extract_sign_extend_2.case_0
  pat_unapply h_v66 as ⟨v69, v70, x_v69, x_v70, h_v69, h_v70, hn_v69, hn_v70⟩ using hinv12 else hinv12 hG in EoCases.__eo_prog_bv_extract_sign_extend_2.case_0
  step as ⟨e_v71, he_v71⟩
  store_step with CtorSpec.eo__3d.construct s12 e_v71 (by rw [he_v71]; exact empty_args) hinv12 h64 as ⟨v71, s13, hinv13, h_v71⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v67 h_v69 h_v70 dropping h_a9 h_v53 h_v62 h_v64 h_v66 he_v71 hinv12 e_v71 s12 v53 v62 v64 v66
  pat_same v69 v71 with h_v69 h_v71 using hinv13 else hinv13 hG in EoCases.__eo_prog_bv_extract_sign_extend_2.case_0
  pat_same v70 a5 with h_v70 h_a5 using hinv13 else hinv13 hG in EoCases.__eo_prog_bv_extract_sign_extend_2.case_0
  pat_unapply h_v67 as ⟨v73, v74, x_v73, x_v74, h_v73, h_v74, hn_v73, hn_v74⟩ using hinv13 else hinv13 hG in EoCases.__eo_prog_bv_extract_sign_extend_2.case_0
  pat_unapply h_v73 as ⟨v76, v77, x_v76, x_v77, h_v76, h_v77, hn_v76, hn_v77⟩ using hinv13 else hinv13 hG in EoCases.__eo_prog_bv_extract_sign_extend_2.case_0
  step as ⟨e_v78, he_v78⟩
  store_step with CtorSpec.eo__2b.construct s13 e_v78 (by rw [he_v78]; exact empty_args) hinv13 h64 as ⟨v78, s14, hinv14, h_v78⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v74 h_v76 h_v77 dropping h_v67 h_v69 h_v70 h_v71 h_v73 he_v78 hinv13 e_v78 s13 v67 v69 v70 v71 v73
  pat_same v76 v78 with h_v76 h_v78 using hinv14 else hinv14 hG in EoCases.__eo_prog_bv_extract_sign_extend_2.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s14 1#u32 (1) (by scalar_tac) hinv14 h64 as ⟨v79, s15, hinv15, h_v79⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v74 h_v77 dropping h_v76 h_v78 hinv14 s14 v76 v78
  pat_same v77 v79 with h_v77 h_v79 using hinv15 else hinv15 hG in EoCases.__eo_prog_bv_extract_sign_extend_2.case_0
  pat_unapply h_v74 as ⟨v81, v82, x_v81, x_v82, h_v81, h_v82, hn_v81, hn_v82⟩ using hinv15 else hinv15 hG in EoCases.__eo_prog_bv_extract_sign_extend_2.case_0
  pat_unapply h_v81 as ⟨v84, v85, x_v84, x_v85, h_v84, h_v85, hn_v84, hn_v85⟩ using hinv15 else hinv15 hG in EoCases.__eo_prog_bv_extract_sign_extend_2.case_0
  step as ⟨e_v86, he_v86⟩
  store_step with CtorSpec.eo__2b.construct s15 e_v86 (by rw [he_v86]; exact empty_args) hinv15 h64 as ⟨v86, s16, hinv16, h_v86⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v82 h_v84 h_v85 dropping h_v74 h_v77 h_v79 h_v81 he_v86 hinv15 e_v86 s15 v74 v77 v79 v81
  pat_same v84 v86 with h_v84 h_v86 using hinv16 else hinv16 hG in EoCases.__eo_prog_bv_extract_sign_extend_2.case_0
  pat_unapply h_v85 as ⟨v88, v89, x_v88, x_v89, h_v88, h_v89, hn_v88, hn_v89⟩ using hinv16 else hinv16 hG in EoCases.__eo_prog_bv_extract_sign_extend_2.case_0
  pat_unapply h_v88 as ⟨v91, v92, x_v91, x_v92, h_v91, h_v92, hn_v91, hn_v92⟩ using hinv16 else hinv16 hG in EoCases.__eo_prog_bv_extract_sign_extend_2.case_0
  step as ⟨e_v93, he_v93⟩
  store_step with CtorSpec.eo__2d.construct s16 e_v93 (by rw [he_v93]; exact empty_args) hinv16 h64 as ⟨v93, s17, hinv17, h_v93⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v82 h_v89 h_v91 h_v92 dropping h_v84 h_v85 h_v86 h_v88 he_v93 hinv16 e_v93 s16 v84 v85 v86 v88
  pat_same v91 v93 with h_v91 h_v93 using hinv17 else hinv17 hG in EoCases.__eo_prog_bv_extract_sign_extend_2.case_0
  pat_same v92 a2 with h_v92 h_a2 using hinv17 else hinv17 hG in EoCases.__eo_prog_bv_extract_sign_extend_2.case_0
  pat_unapply h_v89 as ⟨v95, v96, x_v95, x_v96, h_v95, h_v96, hn_v95, hn_v96⟩ using hinv17 else hinv17 hG in EoCases.__eo_prog_bv_extract_sign_extend_2.case_0
  step as ⟨e_v97, he_v97⟩
  store_step with CtorSpec.eo__40bvsize.construct s17 e_v97 (by rw [he_v97]; exact empty_args) hinv17 h64 as ⟨v97, s18, hinv18, h_v97⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v82 h_v95 h_v96 dropping h_v89 h_v91 h_v92 h_v93 he_v97 hinv17 e_v97 s17 v89 v91 v92 v93
  pat_same v95 v97 with h_v95 h_v97 using hinv18 else hinv18 hG in EoCases.__eo_prog_bv_extract_sign_extend_2.case_0
  pat_same v96 a0 with h_v96 h_a0 using hinv18 else hinv18 hG in EoCases.__eo_prog_bv_extract_sign_extend_2.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s18 0#u32 (0) (by scalar_tac) hinv18 h64 as ⟨v98, s19, hinv19, h_v98⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v82 dropping h_v95 h_v96 h_v97 hinv18 s18 v95 v96 v97
  pat_same v82 v98 with h_v82 h_v98 using hinv19 else hinv19 hG in EoCases.__eo_prog_bv_extract_sign_extend_2.case_0
  step as ⟨e_v99, he_v99⟩
  store_step with CtorSpec.eo__3d.construct s19 e_v99 (by rw [he_v99]; exact empty_args) hinv19 h64 as ⟨v99, s20, hinv20, h_v99⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 dropping h_v82 h_v98 he_v99 hinv19 e_v99 s19 v82 v98
  step as ⟨e_v100, he_v100⟩
  store_step with CtorSpec.eo_extract.construct s20 e_v100 (by rw [he_v100]; rfl) h_a2 h_a1 hinv20 h64 as ⟨v100, s21, hinv21, h_v100⟩ growing hG carrying h_a0 h_a1 h_a3 h_a4 h_a5 h_v99 dropping h_a2 he_v100 hinv20 e_v100 s20
  step as ⟨e_v101, he_v101⟩
  store_step with CtorSpec.eo_sign_5fextend.construct s21 e_v101 (by rw [he_v101]; rfl) h_a3 hinv21 h64 as ⟨v101, s22, hinv22, h_v101⟩ growing hG carrying h_a0 h_a1 h_a4 h_a5 h_v99 h_v100 dropping h_a3 he_v101 hinv21 e_v101 s21
  store_step with Store.apply_rep s22 v101 a0 _ _ hinv22 h64 h_v101 h_a0 (by ns_tac) (by ns_tac) as ⟨v102, s23, hinv23, h_v102⟩ growing hG carrying h_a0 h_a1 h_a4 h_a5 h_v99 h_v100 dropping h_v101 hinv22 s22 v101
  store_step with Store.apply_rep s23 v100 v102 _ _ hinv23 h64 h_v100 h_v102 (by ns_tac) (by ns_tac) as ⟨v103, s24, hinv24, h_v103⟩ growing hG carrying h_a0 h_a1 h_a4 h_a5 h_v99 dropping h_v100 h_v102 hinv23 s23 v100 v102
  store_step with Store.apply_rep s24 v99 v103 _ _ hinv24 h64 h_v99 h_v103 (by ns_tac) (by ns_tac) as ⟨v104, s25, hinv25, h_v104⟩ growing hG carrying h_a0 h_a1 h_a4 h_a5 dropping h_v103 h_v99 hinv24 s24 v103 v99
  step as ⟨e_v105, he_v105⟩
  store_step with CtorSpec.eo_sign_5fextend.construct s25 e_v105 (by rw [he_v105]; rfl) h_a5 hinv25 h64 as ⟨v105, s26, hinv26, h_v105⟩ growing hG carrying h_a0 h_a1 h_a4 h_v104 dropping h_a5 he_v105 hinv25 e_v105 s25
  step as ⟨e_v106, he_v106⟩
  store_step with CtorSpec.eo_extract.construct s26 e_v106 (by rw [he_v106]; rfl) h_a4 h_a1 hinv26 h64 as ⟨v106, s27, hinv27, h_v106⟩ growing hG carrying h_a0 h_v104 h_v105 dropping h_a1 h_a4 he_v106 hinv26 e_v106 s26
  store_step with Store.apply_rep s27 v106 a0 _ _ hinv27 h64 h_v106 h_a0 (by ns_tac) (by ns_tac) as ⟨v107, s28, hinv28, h_v107⟩ growing hG carrying h_v104 h_v105 dropping h_a0 h_v106 hinv27 s27 v106
  store_step with Store.apply_rep s28 v105 v107 _ _ hinv28 h64 h_v105 h_v107 (by ns_tac) (by ns_tac) as ⟨v108, s29, hinv29, h_v108⟩ growing hG carrying h_v104 dropping h_v105 h_v107 hinv28 s28 v105 v107
  store_step with Store.apply_rep s29 v104 v108 _ _ hinv29 h64 h_v104 h_v108 (by ns_tac) (by ns_tac) as ⟨v109, s30, hinv30, h_v109⟩ growing hG carrying dropping h_v104 h_v108 hinv29 s29 v104 v108
  case_done hinv30 hG with h_v109 in EoCases.__eo_prog_bv_extract_sign_extend_2.case_0 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_a5 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v13 hn_v14 hn_v17 hn_v18 hn_v24 hn_v25 hn_v27 hn_v28 hn_v31 hn_v32 hn_v34 hn_v35 hn_v38 hn_v39 hn_v45 hn_v46 hn_v48 hn_v49 hn_v52 hn_v53 hn_v55 hn_v56 hn_v59 hn_v60 hn_v66 hn_v67 hn_v69 hn_v70 hn_v73 hn_v74 hn_v76 hn_v77 hn_v81 hn_v82 hn_v84 hn_v85 hn_v88 hn_v89 hn_v91 hn_v92 hn_v95 hn_v96

set_option maxHeartbeats 4000000 in
/-- logos's `__eo_prog_bv_extract_sign_extend_2` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fbv_2dextract_2dsign_2dextend_2d2.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _) (x_a7 : _) (x_a8 : _) (x_a9 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) (hw_a4 : Valid.valid x_a4) (hw_a5 : Valid.valid x_a5) (hw_a6 : Valid.valid x_a6) (hw_a7 : Valid.valid x_a7) (hw_a8 : Valid.valid x_a8) (hw_a9 : Valid.valid x_a9) :
    __eo_prog_bv_extract_sign_extend_2 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 x_a9 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else if x_a4 = Eo.Term.Stuck then HasStuck.stuck else if x_a5 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_bv_extract_sign_extend_2.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 x_a9] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_bv_extract_sign_extend_2
  unfold EoCases.__eo_prog_bv_extract_sign_extend_2.case_0
  logos_eq

set_option maxHeartbeats 4000000 in
theorem body_eo__24eo_5fprog_5fbv_2dextract_2dsign_2dextend_2d2_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _) (x_a7 : _) (x_a8 : _) (x_a9 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) (h_a6 : Represents.rep s a6 x_a6) (h_a7 : Represents.rep s a7 x_a7) (h_a8 : Represents.rep s a8 x_a8) (h_a9 : Represents.rep s a9 x_a9) :
    body_eo__24eo_5fprog_5fbv_2dextract_2dsign_2dextend_2d2 s a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_extract_sign_extend_2 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 x_a9)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fbv_2dextract_2dsign_2dextend_2d2.rust_eq x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 x_a9 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3) (by valid_tac hinv h_a4) (by valid_tac hinv h_a5) (by valid_tac hinv h_a6) (by valid_tac hinv h_a7) (by valid_tac hinv h_a8) (by valid_tac hinv h_a9)]
  unfold body_eo__24eo_5fprog_5fbv_2dextract_2dsign_2dextend_2d2
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  stuck_check h_a3 : x_a3 as hn_a3 else hinv hG
  stuck_check h_a4 : x_a4 as hn_a4 else hinv hG
  stuck_check h_a5 : x_a5 as hn_a5 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fbv_2dextract_2dsign_2dextend_2d2_spec n ih s a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 x_a9 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 h_a9 hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_a5
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 h_a9 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_a5
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_a5 hc0 in EoCases.__eo_prog_bv_extract_sign_extend_2.case_0

set_option maxHeartbeats 4000000 in
theorem eo__24eo_5fprog_5fbv_2dextract_2dsign_2dextend_2d2_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fbv_2dextract_2dsign_2dextend_2d2.Spec n := by
  intro s a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 x_a9 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 h_a9
  unfold eo__24eo_5fprog_5fbv_2dextract_2dsign_2dextend_2d2
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fbv_2dextract_2dsign_2dextend_2d2 s1 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9) (fun s' t => Represents.rep s' t (__eo_prog_bv_extract_sign_extend_2 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 x_a9))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fbv_2dextract_2dsign_2dextend_2d2_spec m (ih m hm) s1 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 x_a9 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn) (by congr_one h_a4 hn) (by congr_one h_a5 hn) (by congr_one h_a6 hn) (by congr_one h_a7 hn) (by congr_one h_a8 hn) (by congr_one h_a9 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

end pathos_compiled_checker
