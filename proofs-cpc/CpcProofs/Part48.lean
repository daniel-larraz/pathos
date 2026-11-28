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
theorem case_0_eo__24eo_5fprog_5fbv_2drotate_2dright_2deliminate_2d1_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 a6 a7 a8 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _) (x_a7 : _) (x_a8 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) (h_a6 : Represents.rep s a6 x_a6) (h_a7 : Represents.rep s a7 x_a7) (h_a8 : Represents.rep s a8 x_a8) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) (hn_a4 : x_a4 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fbv_2drotate_2dright_2deliminate_2d1 s a0 a1 a2 a3 a4 a5 a6 a7 a8 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_bv_rotate_right_eliminate_1.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_bv_rotate_right_eliminate_1.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fbv_2drotate_2dright_2deliminate_2d1
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a5 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_bv_rotate_right_eliminate_1.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_rotate_right_eliminate_1.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_rotate_right_eliminate_1.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a6 h_a7 h_a8 h_v4 h_v6 h_v7 dropping h_a5 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_rotate_right_eliminate_1.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_rotate_right_eliminate_1.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_rotate_right_eliminate_1.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__3d.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a6 h_a7 h_a8 h_v4 h_v11 h_v13 h_v14 dropping h_v10 h_v6 h_v7 h_v8 he_v15 hinv1 e_v15 s1 v10 v6 v7 v8
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_rotate_right_eliminate_1.case_0
  pat_unapply h_v14 as ⟨v17, v18, x_v17, x_v18, h_v17, h_v18, hn_v17, hn_v18⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_rotate_right_eliminate_1.case_0
  pat_unapply h_v17 as ⟨v20, v21, x_v20, x_v21, h_v20, h_v21, hn_v20, hn_v21⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_rotate_right_eliminate_1.case_0
  step as ⟨e_v22, he_v22⟩
  store_step with CtorSpec.eo_mod.construct s2 e_v22 (by rw [he_v22]; exact empty_args) hinv2 h64 as ⟨v22, s3, hinv3, h_v22⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a6 h_a7 h_a8 h_v4 h_v11 h_v18 h_v20 h_v21 dropping h_v13 h_v14 h_v15 h_v17 he_v22 hinv2 e_v22 s2 v13 v14 v15 v17
  pat_same v20 v22 with h_v20 h_v22 using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_rotate_right_eliminate_1.case_0
  pat_same v21 a1 with h_v21 h_a1 using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_rotate_right_eliminate_1.case_0
  pat_unapply h_v18 as ⟨v24, v25, x_v24, x_v25, h_v24, h_v25, hn_v24, hn_v25⟩ using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_rotate_right_eliminate_1.case_0
  step as ⟨e_v26, he_v26⟩
  store_step with CtorSpec.eo__40bvsize.construct s3 e_v26 (by rw [he_v26]; exact empty_args) hinv3 h64 as ⟨v26, s4, hinv4, h_v26⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a6 h_a7 h_a8 h_v4 h_v11 h_v24 h_v25 dropping h_v18 h_v20 h_v21 h_v22 he_v26 hinv3 e_v26 s3 v18 v20 v21 v22
  pat_same v24 v26 with h_v24 h_v26 using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_rotate_right_eliminate_1.case_0
  pat_same v25 a0 with h_v25 h_a0 using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_rotate_right_eliminate_1.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s4 0#u32 (0) (by scalar_tac) hinv4 h64 as ⟨v27, s5, hinv5, h_v27⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a6 h_a7 h_a8 h_v4 h_v11 dropping h_v24 h_v25 h_v26 hinv4 s4 v24 v25 v26
  pat_same v11 v27 with h_v11 h_v27 using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_rotate_right_eliminate_1.case_0
  store_step with Store.literal_boolean_spec s5 false hinv5 h64 as ⟨v28, s6, hinv6, h_v28⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a6 h_a7 h_a8 h_v4 dropping h_v11 h_v27 hinv5 s5 v11 v27
  pat_same v4 v28 with h_v4 h_v28 using hinv6 else hinv6 hG in EoCases.__eo_prog_bv_rotate_right_eliminate_1.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a6 as ⟨v30, x_v30, h_v30⟩ else hinv6 hG in EoCases.__eo_prog_bv_rotate_right_eliminate_1.case_0
  pat_unapply h_v30 as ⟨v32, v33, x_v32, x_v33, h_v32, h_v33, hn_v32, hn_v33⟩ using hinv6 else hinv6 hG in EoCases.__eo_prog_bv_rotate_right_eliminate_1.case_0
  pat_unapply h_v32 as ⟨v35, v36, x_v35, x_v36, h_v35, h_v36, hn_v35, hn_v36⟩ using hinv6 else hinv6 hG in EoCases.__eo_prog_bv_rotate_right_eliminate_1.case_0
  step as ⟨e_v37, he_v37⟩
  store_step with CtorSpec.eo__3d.construct s6 e_v37 (by rw [he_v37]; exact empty_args) hinv6 h64 as ⟨v37, s7, hinv7, h_v37⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a7 h_a8 h_v33 h_v35 h_v36 dropping h_a6 h_v28 h_v30 h_v32 h_v4 he_v37 hinv6 e_v37 s6 v28 v30 v32 v4
  pat_same v35 v37 with h_v35 h_v37 using hinv7 else hinv7 hG in EoCases.__eo_prog_bv_rotate_right_eliminate_1.case_0
  pat_same v36 a2 with h_v36 h_a2 using hinv7 else hinv7 hG in EoCases.__eo_prog_bv_rotate_right_eliminate_1.case_0
  pat_unapply h_v33 as ⟨v39, v40, x_v39, x_v40, h_v39, h_v40, hn_v39, hn_v40⟩ using hinv7 else hinv7 hG in EoCases.__eo_prog_bv_rotate_right_eliminate_1.case_0
  pat_unapply h_v39 as ⟨v42, v43, x_v42, x_v43, h_v42, h_v43, hn_v42, hn_v43⟩ using hinv7 else hinv7 hG in EoCases.__eo_prog_bv_rotate_right_eliminate_1.case_0
  step as ⟨e_v44, he_v44⟩
  store_step with CtorSpec.eo__2d.construct s7 e_v44 (by rw [he_v44]; exact empty_args) hinv7 h64 as ⟨v44, s8, hinv8, h_v44⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a7 h_a8 h_v40 h_v42 h_v43 dropping h_v33 h_v35 h_v36 h_v37 h_v39 he_v44 hinv7 e_v44 s7 v33 v35 v36 v37 v39
  pat_same v42 v44 with h_v42 h_v44 using hinv8 else hinv8 hG in EoCases.__eo_prog_bv_rotate_right_eliminate_1.case_0
  pat_unapply h_v43 as ⟨v46, v47, x_v46, x_v47, h_v46, h_v47, hn_v46, hn_v47⟩ using hinv8 else hinv8 hG in EoCases.__eo_prog_bv_rotate_right_eliminate_1.case_0
  pat_unapply h_v46 as ⟨v49, v50, x_v49, x_v50, h_v49, h_v50, hn_v49, hn_v50⟩ using hinv8 else hinv8 hG in EoCases.__eo_prog_bv_rotate_right_eliminate_1.case_0
  step as ⟨e_v51, he_v51⟩
  store_step with CtorSpec.eo_mod.construct s8 e_v51 (by rw [he_v51]; exact empty_args) hinv8 h64 as ⟨v51, s9, hinv9, h_v51⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a7 h_a8 h_v40 h_v47 h_v49 h_v50 dropping h_v42 h_v43 h_v44 h_v46 he_v51 hinv8 e_v51 s8 v42 v43 v44 v46
  pat_same v49 v51 with h_v49 h_v51 using hinv9 else hinv9 hG in EoCases.__eo_prog_bv_rotate_right_eliminate_1.case_0
  pat_same v50 a1 with h_v50 h_a1 using hinv9 else hinv9 hG in EoCases.__eo_prog_bv_rotate_right_eliminate_1.case_0
  pat_unapply h_v47 as ⟨v53, v54, x_v53, x_v54, h_v53, h_v54, hn_v53, hn_v54⟩ using hinv9 else hinv9 hG in EoCases.__eo_prog_bv_rotate_right_eliminate_1.case_0
  step as ⟨e_v55, he_v55⟩
  store_step with CtorSpec.eo__40bvsize.construct s9 e_v55 (by rw [he_v55]; exact empty_args) hinv9 h64 as ⟨v55, s10, hinv10, h_v55⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a7 h_a8 h_v40 h_v53 h_v54 dropping h_v47 h_v49 h_v50 h_v51 he_v55 hinv9 e_v55 s9 v47 v49 v50 v51
  pat_same v53 v55 with h_v53 h_v55 using hinv10 else hinv10 hG in EoCases.__eo_prog_bv_rotate_right_eliminate_1.case_0
  pat_same v54 a0 with h_v54 h_a0 using hinv10 else hinv10 hG in EoCases.__eo_prog_bv_rotate_right_eliminate_1.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s10 1#u32 (1) (by scalar_tac) hinv10 h64 as ⟨v56, s11, hinv11, h_v56⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a7 h_a8 h_v40 dropping h_v53 h_v54 h_v55 hinv10 s10 v53 v54 v55
  pat_same v40 v56 with h_v40 h_v56 using hinv11 else hinv11 hG in EoCases.__eo_prog_bv_rotate_right_eliminate_1.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a7 as ⟨v58, x_v58, h_v58⟩ else hinv11 hG in EoCases.__eo_prog_bv_rotate_right_eliminate_1.case_0
  pat_unapply h_v58 as ⟨v60, v61, x_v60, x_v61, h_v60, h_v61, hn_v60, hn_v61⟩ using hinv11 else hinv11 hG in EoCases.__eo_prog_bv_rotate_right_eliminate_1.case_0
  pat_unapply h_v60 as ⟨v63, v64, x_v63, x_v64, h_v63, h_v64, hn_v63, hn_v64⟩ using hinv11 else hinv11 hG in EoCases.__eo_prog_bv_rotate_right_eliminate_1.case_0
  step as ⟨e_v65, he_v65⟩
  store_step with CtorSpec.eo__3d.construct s11 e_v65 (by rw [he_v65]; exact empty_args) hinv11 h64 as ⟨v65, s12, hinv12, h_v65⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a8 h_v61 h_v63 h_v64 dropping h_a7 h_v40 h_v56 h_v58 h_v60 he_v65 hinv11 e_v65 s11 v40 v56 v58 v60
  pat_same v63 v65 with h_v63 h_v65 using hinv12 else hinv12 hG in EoCases.__eo_prog_bv_rotate_right_eliminate_1.case_0
  pat_same v64 a3 with h_v64 h_a3 using hinv12 else hinv12 hG in EoCases.__eo_prog_bv_rotate_right_eliminate_1.case_0
  pat_unapply h_v61 as ⟨v67, v68, x_v67, x_v68, h_v67, h_v68, hn_v67, hn_v68⟩ using hinv12 else hinv12 hG in EoCases.__eo_prog_bv_rotate_right_eliminate_1.case_0
  pat_unapply h_v67 as ⟨v70, v71, x_v70, x_v71, h_v70, h_v71, hn_v70, hn_v71⟩ using hinv12 else hinv12 hG in EoCases.__eo_prog_bv_rotate_right_eliminate_1.case_0
  step as ⟨e_v72, he_v72⟩
  store_step with CtorSpec.eo__2d.construct s12 e_v72 (by rw [he_v72]; exact empty_args) hinv12 h64 as ⟨v72, s13, hinv13, h_v72⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a8 h_v68 h_v70 h_v71 dropping h_v61 h_v63 h_v64 h_v65 h_v67 he_v72 hinv12 e_v72 s12 v61 v63 v64 v65 v67
  pat_same v70 v72 with h_v70 h_v72 using hinv13 else hinv13 hG in EoCases.__eo_prog_bv_rotate_right_eliminate_1.case_0
  pat_unapply h_v71 as ⟨v74, v75, x_v74, x_v75, h_v74, h_v75, hn_v74, hn_v75⟩ using hinv13 else hinv13 hG in EoCases.__eo_prog_bv_rotate_right_eliminate_1.case_0
  step as ⟨e_v76, he_v76⟩
  store_step with CtorSpec.eo__40bvsize.construct s13 e_v76 (by rw [he_v76]; exact empty_args) hinv13 h64 as ⟨v76, s14, hinv14, h_v76⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a8 h_v68 h_v74 h_v75 dropping h_v70 h_v71 h_v72 he_v76 hinv13 e_v76 s13 v70 v71 v72
  pat_same v74 v76 with h_v74 h_v76 using hinv14 else hinv14 hG in EoCases.__eo_prog_bv_rotate_right_eliminate_1.case_0
  pat_same v75 a0 with h_v75 h_a0 using hinv14 else hinv14 hG in EoCases.__eo_prog_bv_rotate_right_eliminate_1.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s14 1#u32 (1) (by scalar_tac) hinv14 h64 as ⟨v77, s15, hinv15, h_v77⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a8 h_v68 dropping h_v74 h_v75 h_v76 hinv14 s14 v74 v75 v76
  pat_same v68 v77 with h_v68 h_v77 using hinv15 else hinv15 hG in EoCases.__eo_prog_bv_rotate_right_eliminate_1.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a8 as ⟨v79, x_v79, h_v79⟩ else hinv15 hG in EoCases.__eo_prog_bv_rotate_right_eliminate_1.case_0
  pat_unapply h_v79 as ⟨v81, v82, x_v81, x_v82, h_v81, h_v82, hn_v81, hn_v82⟩ using hinv15 else hinv15 hG in EoCases.__eo_prog_bv_rotate_right_eliminate_1.case_0
  pat_unapply h_v81 as ⟨v84, v85, x_v84, x_v85, h_v84, h_v85, hn_v84, hn_v85⟩ using hinv15 else hinv15 hG in EoCases.__eo_prog_bv_rotate_right_eliminate_1.case_0
  step as ⟨e_v86, he_v86⟩
  store_step with CtorSpec.eo__3d.construct s15 e_v86 (by rw [he_v86]; exact empty_args) hinv15 h64 as ⟨v86, s16, hinv16, h_v86⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v82 h_v84 h_v85 dropping h_a8 h_v68 h_v77 h_v79 h_v81 he_v86 hinv15 e_v86 s15 v68 v77 v79 v81
  pat_same v84 v86 with h_v84 h_v86 using hinv16 else hinv16 hG in EoCases.__eo_prog_bv_rotate_right_eliminate_1.case_0
  pat_same v85 a4 with h_v85 h_a4 using hinv16 else hinv16 hG in EoCases.__eo_prog_bv_rotate_right_eliminate_1.case_0
  pat_unapply h_v82 as ⟨v88, v89, x_v88, x_v89, h_v88, h_v89, hn_v88, hn_v89⟩ using hinv16 else hinv16 hG in EoCases.__eo_prog_bv_rotate_right_eliminate_1.case_0
  pat_unapply h_v88 as ⟨v91, v92, x_v91, x_v92, h_v91, h_v92, hn_v91, hn_v92⟩ using hinv16 else hinv16 hG in EoCases.__eo_prog_bv_rotate_right_eliminate_1.case_0
  step as ⟨e_v93, he_v93⟩
  store_step with CtorSpec.eo_mod.construct s16 e_v93 (by rw [he_v93]; exact empty_args) hinv16 h64 as ⟨v93, s17, hinv17, h_v93⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v89 h_v91 h_v92 dropping h_v82 h_v84 h_v85 h_v86 h_v88 he_v93 hinv16 e_v93 s16 v82 v84 v85 v86 v88
  pat_same v91 v93 with h_v91 h_v93 using hinv17 else hinv17 hG in EoCases.__eo_prog_bv_rotate_right_eliminate_1.case_0
  pat_same v92 a1 with h_v92 h_a1 using hinv17 else hinv17 hG in EoCases.__eo_prog_bv_rotate_right_eliminate_1.case_0
  pat_unapply h_v89 as ⟨v95, v96, x_v95, x_v96, h_v95, h_v96, hn_v95, hn_v96⟩ using hinv17 else hinv17 hG in EoCases.__eo_prog_bv_rotate_right_eliminate_1.case_0
  step as ⟨e_v97, he_v97⟩
  store_step with CtorSpec.eo__40bvsize.construct s17 e_v97 (by rw [he_v97]; exact empty_args) hinv17 h64 as ⟨v97, s18, hinv18, h_v97⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v95 h_v96 dropping h_v89 h_v91 h_v92 h_v93 he_v97 hinv17 e_v97 s17 v89 v91 v92 v93
  pat_same v95 v97 with h_v95 h_v97 using hinv18 else hinv18 hG in EoCases.__eo_prog_bv_rotate_right_eliminate_1.case_0
  pat_same v96 a0 with h_v96 h_a0 using hinv18 else hinv18 hG in EoCases.__eo_prog_bv_rotate_right_eliminate_1.case_0
  step as ⟨e_v98, he_v98⟩
  store_step with CtorSpec.eo__3d.construct s18 e_v98 (by rw [he_v98]; exact empty_args) hinv18 h64 as ⟨v98, s19, hinv19, h_v98⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 dropping h_v95 h_v96 h_v97 he_v98 hinv18 e_v98 s18 v95 v96 v97
  step as ⟨e_v99, he_v99⟩
  store_step with CtorSpec.eo_rotate_5fright.construct s19 e_v99 (by rw [he_v99]; rfl) h_a1 hinv19 h64 as ⟨v99, s20, hinv20, h_v99⟩ growing hG carrying h_a0 h_a2 h_a3 h_a4 h_v98 dropping h_a1 he_v99 hinv19 e_v99 s19
  store_step with Store.apply_rep s20 v99 a0 _ _ hinv20 h64 h_v99 h_a0 (by ns_tac) (by ns_tac) as ⟨v100, s21, hinv21, h_v100⟩ growing hG carrying h_a0 h_a2 h_a3 h_a4 h_v98 dropping h_v99 hinv20 s20 v99
  store_step with Store.apply_rep s21 v98 v100 _ _ hinv21 h64 h_v98 h_v100 (by ns_tac) (by ns_tac) as ⟨v101, s22, hinv22, h_v101⟩ growing hG carrying h_a0 h_a2 h_a3 h_a4 dropping h_v100 h_v98 hinv21 s21 v100 v98
  step as ⟨e_v102, he_v102⟩
  store_step with CtorSpec.eo_concat.construct s22 e_v102 (by rw [he_v102]; exact empty_args) hinv22 h64 as ⟨v102, s23, hinv23, h_v102⟩ growing hG carrying h_a0 h_a2 h_a3 h_a4 h_v101 dropping he_v102 hinv22 e_v102 s22
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s23 0#u32 (0) (by scalar_tac) hinv23 h64 as ⟨v103, s24, hinv24, h_v103⟩ growing hG carrying h_a0 h_a2 h_a3 h_a4 h_v101 h_v102 dropping hinv23 s23
  step as ⟨e_v104, he_v104⟩
  store_step with CtorSpec.eo_extract.construct s24 e_v104 (by rw [he_v104]; rfl) h_a2 h_v103 hinv24 h64 as ⟨v104, s25, hinv25, h_v104⟩ growing hG carrying h_a0 h_a3 h_a4 h_v101 h_v102 dropping h_a2 h_v103 he_v104 hinv24 e_v104 s24 v103
  store_step with Store.apply_rep s25 v104 a0 _ _ hinv25 h64 h_v104 h_a0 (by ns_tac) (by ns_tac) as ⟨v105, s26, hinv26, h_v105⟩ growing hG carrying h_a0 h_a3 h_a4 h_v101 h_v102 dropping h_v104 hinv25 s25 v104
  store_step with Store.apply_rep s26 v102 v105 _ _ hinv26 h64 h_v102 h_v105 (by ns_tac) (by ns_tac) as ⟨v106, s27, hinv27, h_v106⟩ growing hG carrying h_a0 h_a3 h_a4 h_v101 dropping h_v102 h_v105 hinv26 s26 v102 v105
  step as ⟨e_v107, he_v107⟩
  store_step with CtorSpec.eo_concat.construct s27 e_v107 (by rw [he_v107]; exact empty_args) hinv27 h64 as ⟨v107, s28, hinv28, h_v107⟩ growing hG carrying h_a0 h_a3 h_a4 h_v101 h_v106 dropping he_v107 hinv27 e_v107 s27
  step as ⟨e_v108, he_v108⟩
  store_step with CtorSpec.eo_extract.construct s28 e_v108 (by rw [he_v108]; rfl) h_a3 h_a4 hinv28 h64 as ⟨v108, s29, hinv29, h_v108⟩ growing hG carrying h_a0 h_v101 h_v106 h_v107 dropping h_a3 h_a4 he_v108 hinv28 e_v108 s28
  store_step with Store.apply_rep s29 v108 a0 _ _ hinv29 h64 h_v108 h_a0 (by ns_tac) (by ns_tac) as ⟨v109, s30, hinv30, h_v109⟩ growing hG carrying h_v101 h_v106 h_v107 dropping h_a0 h_v108 hinv29 s29 v108
  store_step with Store.apply_rep s30 v107 v109 _ _ hinv30 h64 h_v107 h_v109 (by ns_tac) (by ns_tac) as ⟨v110, s31, hinv31, h_v110⟩ growing hG carrying h_v101 h_v106 dropping h_v107 h_v109 hinv30 s30 v107 v109
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s31 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv31 h64 as ⟨v111, s32, hinv32, h_v111⟩ growing hG carrying h_v101 h_v106 h_v110 dropping hinv31 s31
  store_step with Store.apply_rep s32 v110 v111 _ _ hinv32 h64 h_v110 h_v111 (by ns_tac) (by ns_tac) as ⟨v112, s33, hinv33, h_v112⟩ growing hG carrying h_v101 h_v106 dropping h_v110 h_v111 hinv32 s32 v110 v111
  store_step with Store.apply_rep s33 v106 v112 _ _ hinv33 h64 h_v106 h_v112 (by ns_tac) (by ns_tac) as ⟨v113, s34, hinv34, h_v113⟩ growing hG carrying h_v101 dropping h_v106 h_v112 hinv33 s33 v106 v112
  store_step with Store.apply_rep s34 v101 v113 _ _ hinv34 h64 h_v101 h_v113 (by ns_tac) (by ns_tac) as ⟨v114, s35, hinv35, h_v114⟩ growing hG carrying dropping h_v101 h_v113 hinv34 s34 v101 v113
  case_done hinv35 hG with h_v114 in EoCases.__eo_prog_bv_rotate_right_eliminate_1.case_0 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v13 hn_v14 hn_v17 hn_v18 hn_v20 hn_v21 hn_v24 hn_v25 hn_v32 hn_v33 hn_v35 hn_v36 hn_v39 hn_v40 hn_v42 hn_v43 hn_v46 hn_v47 hn_v49 hn_v50 hn_v53 hn_v54 hn_v60 hn_v61 hn_v63 hn_v64 hn_v67 hn_v68 hn_v70 hn_v71 hn_v74 hn_v75 hn_v81 hn_v82 hn_v84 hn_v85 hn_v88 hn_v89 hn_v91 hn_v92 hn_v95 hn_v96

set_option maxHeartbeats 4000000 in
/-- logos's `__eo_prog_bv_rotate_right_eliminate_1` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fbv_2drotate_2dright_2deliminate_2d1.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _) (x_a7 : _) (x_a8 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) (hw_a4 : Valid.valid x_a4) (hw_a5 : Valid.valid x_a5) (hw_a6 : Valid.valid x_a6) (hw_a7 : Valid.valid x_a7) (hw_a8 : Valid.valid x_a8) :
    __eo_prog_bv_rotate_right_eliminate_1 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else if x_a4 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_bv_rotate_right_eliminate_1.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_bv_rotate_right_eliminate_1
  unfold EoCases.__eo_prog_bv_rotate_right_eliminate_1.case_0
  logos_eq

set_option maxHeartbeats 4000000 in
theorem body_eo__24eo_5fprog_5fbv_2drotate_2dright_2deliminate_2d1_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 a6 a7 a8 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _) (x_a7 : _) (x_a8 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) (h_a6 : Represents.rep s a6 x_a6) (h_a7 : Represents.rep s a7 x_a7) (h_a8 : Represents.rep s a8 x_a8) :
    body_eo__24eo_5fprog_5fbv_2drotate_2dright_2deliminate_2d1 s a0 a1 a2 a3 a4 a5 a6 a7 a8 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_rotate_right_eliminate_1 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fbv_2drotate_2dright_2deliminate_2d1.rust_eq x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3) (by valid_tac hinv h_a4) (by valid_tac hinv h_a5) (by valid_tac hinv h_a6) (by valid_tac hinv h_a7) (by valid_tac hinv h_a8)]
  unfold body_eo__24eo_5fprog_5fbv_2drotate_2dright_2deliminate_2d1
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  stuck_check h_a3 : x_a3 as hn_a3 else hinv hG
  stuck_check h_a4 : x_a4 as hn_a4 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fbv_2drotate_2dright_2deliminate_2d1_spec n ih s a0 a1 a2 a3 a4 a5 a6 a7 a8 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 hn_a0 hn_a1 hn_a2 hn_a3 hn_a4
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hc0 in EoCases.__eo_prog_bv_rotate_right_eliminate_1.case_0

set_option maxHeartbeats 4000000 in
theorem eo__24eo_5fprog_5fbv_2drotate_2dright_2deliminate_2d1_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fbv_2drotate_2dright_2deliminate_2d1.Spec n := by
  intro s a0 a1 a2 a3 a4 a5 a6 a7 a8 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8
  unfold eo__24eo_5fprog_5fbv_2drotate_2dright_2deliminate_2d1
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fbv_2drotate_2dright_2deliminate_2d1 s1 a0 a1 a2 a3 a4 a5 a6 a7 a8) (fun s' t => Represents.rep s' t (__eo_prog_bv_rotate_right_eliminate_1 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fbv_2drotate_2dright_2deliminate_2d1_spec m (ih m hm) s1 a0 a1 a2 a3 a4 a5 a6 a7 a8 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn) (by congr_one h_a4 hn) (by congr_one h_a5 hn) (by congr_one h_a6 hn) (by congr_one h_a7 hn) (by congr_one h_a8 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

end pathos_compiled_checker
