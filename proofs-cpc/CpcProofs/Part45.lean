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
theorem case_0_eo__24eo_5fprog_5fbv_2deq_2dextract_2delim1_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _) (x_a7 : _) (x_a8 : _) (x_a9 : _) (x_a10 : _) (x_a11 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) (h_a6 : Represents.rep s a6 x_a6) (h_a7 : Represents.rep s a7 x_a7) (h_a8 : Represents.rep s a8 x_a8) (h_a9 : Represents.rep s a9 x_a9) (h_a10 : Represents.rep s a10 x_a10) (h_a11 : Represents.rep s a11 x_a11) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) (hn_a4 : x_a4 ≠ Eo.Term.Stuck) (hn_a5 : x_a5 ≠ Eo.Term.Stuck) (hn_a6 : x_a6 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fbv_2deq_2dextract_2delim1 s a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_bv_eq_extract_elim1.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 x_a9 x_a10 x_a11 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_bv_eq_extract_elim1.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 x_a9 x_a10 x_a11 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fbv_2deq_2dextract_2delim1
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a7 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_bv_eq_extract_elim1.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_eq_extract_elim1.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_eq_extract_elim1.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a8 h_a9 h_a10 h_a11 h_v4 h_v6 h_v7 dropping h_a7 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_eq_extract_elim1.case_0
  pat_same v7 a4 with h_v7 h_a4 using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_eq_extract_elim1.case_0
  pat_unapply h_v4 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_eq_extract_elim1.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_eq_extract_elim1.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__2d.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a8 h_a9 h_a10 h_a11 h_v11 h_v13 h_v14 dropping h_v10 h_v4 h_v6 h_v7 h_v8 he_v15 hinv1 e_v15 s1 v10 v4 v6 v7 v8
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_eq_extract_elim1.case_0
  pat_unapply h_v14 as ⟨v17, v18, x_v17, x_v18, h_v17, h_v18, hn_v17, hn_v18⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_eq_extract_elim1.case_0
  step as ⟨e_v19, he_v19⟩
  store_step with CtorSpec.eo__40bvsize.construct s2 e_v19 (by rw [he_v19]; exact empty_args) hinv2 h64 as ⟨v19, s3, hinv3, h_v19⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a8 h_a9 h_a10 h_a11 h_v11 h_v17 h_v18 dropping h_v13 h_v14 h_v15 he_v19 hinv2 e_v19 s2 v13 v14 v15
  pat_same v17 v19 with h_v17 h_v19 using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_eq_extract_elim1.case_0
  pat_same v18 a0 with h_v18 h_a0 using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_eq_extract_elim1.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s3 1#u32 (1) (by scalar_tac) hinv3 h64 as ⟨v20, s4, hinv4, h_v20⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a8 h_a9 h_a10 h_a11 h_v11 dropping h_v17 h_v18 h_v19 hinv3 s3 v17 v18 v19
  pat_same v11 v20 with h_v11 h_v20 using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_eq_extract_elim1.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a8 as ⟨v22, x_v22, h_v22⟩ else hinv4 hG in EoCases.__eo_prog_bv_eq_extract_elim1.case_0
  pat_unapply h_v22 as ⟨v24, v25, x_v24, x_v25, h_v24, h_v25, hn_v24, hn_v25⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_eq_extract_elim1.case_0
  pat_unapply h_v24 as ⟨v27, v28, x_v27, x_v28, h_v27, h_v28, hn_v27, hn_v28⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_eq_extract_elim1.case_0
  step as ⟨e_v29, he_v29⟩
  store_step with CtorSpec.eo__3d.construct s4 e_v29 (by rw [he_v29]; exact empty_args) hinv4 h64 as ⟨v29, s5, hinv5, h_v29⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a9 h_a10 h_a11 h_v25 h_v27 h_v28 dropping h_a8 h_v11 h_v20 h_v22 h_v24 he_v29 hinv4 e_v29 s4 v11 v20 v22 v24
  pat_same v27 v29 with h_v27 h_v29 using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_eq_extract_elim1.case_0
  pat_same v28 a5 with h_v28 h_a5 using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_eq_extract_elim1.case_0
  pat_unapply h_v25 as ⟨v31, v32, x_v31, x_v32, h_v31, h_v32, hn_v31, hn_v32⟩ using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_eq_extract_elim1.case_0
  pat_unapply h_v31 as ⟨v34, v35, x_v34, x_v35, h_v34, h_v35, hn_v34, hn_v35⟩ using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_eq_extract_elim1.case_0
  step as ⟨e_v36, he_v36⟩
  store_step with CtorSpec.eo__2b.construct s5 e_v36 (by rw [he_v36]; exact empty_args) hinv5 h64 as ⟨v36, s6, hinv6, h_v36⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a9 h_a10 h_a11 h_v32 h_v34 h_v35 dropping h_v25 h_v27 h_v28 h_v29 h_v31 he_v36 hinv5 e_v36 s5 v25 v27 v28 v29 v31
  pat_same v34 v36 with h_v34 h_v36 using hinv6 else hinv6 hG in EoCases.__eo_prog_bv_eq_extract_elim1.case_0
  pat_same v35 a3 with h_v35 h_a3 using hinv6 else hinv6 hG in EoCases.__eo_prog_bv_eq_extract_elim1.case_0
  pat_unapply h_v32 as ⟨v38, v39, x_v38, x_v39, h_v38, h_v39, hn_v38, hn_v39⟩ using hinv6 else hinv6 hG in EoCases.__eo_prog_bv_eq_extract_elim1.case_0
  pat_unapply h_v38 as ⟨v41, v42, x_v41, x_v42, h_v41, h_v42, hn_v41, hn_v42⟩ using hinv6 else hinv6 hG in EoCases.__eo_prog_bv_eq_extract_elim1.case_0
  step as ⟨e_v43, he_v43⟩
  store_step with CtorSpec.eo__2b.construct s6 e_v43 (by rw [he_v43]; exact empty_args) hinv6 h64 as ⟨v43, s7, hinv7, h_v43⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a9 h_a10 h_a11 h_v39 h_v41 h_v42 dropping h_v32 h_v34 h_v35 h_v36 h_v38 he_v43 hinv6 e_v43 s6 v32 v34 v35 v36 v38
  pat_same v41 v43 with h_v41 h_v43 using hinv7 else hinv7 hG in EoCases.__eo_prog_bv_eq_extract_elim1.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s7 1#u32 (1) (by scalar_tac) hinv7 h64 as ⟨v44, s8, hinv8, h_v44⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a9 h_a10 h_a11 h_v39 h_v42 dropping h_v41 h_v43 hinv7 s7 v41 v43
  pat_same v42 v44 with h_v42 h_v44 using hinv8 else hinv8 hG in EoCases.__eo_prog_bv_eq_extract_elim1.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s8 0#u32 (0) (by scalar_tac) hinv8 h64 as ⟨v45, s9, hinv9, h_v45⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a9 h_a10 h_a11 h_v39 dropping h_v42 h_v44 hinv8 s8 v42 v44
  pat_same v39 v45 with h_v39 h_v45 using hinv9 else hinv9 hG in EoCases.__eo_prog_bv_eq_extract_elim1.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a9 as ⟨v47, x_v47, h_v47⟩ else hinv9 hG in EoCases.__eo_prog_bv_eq_extract_elim1.case_0
  pat_unapply h_v47 as ⟨v49, v50, x_v49, x_v50, h_v49, h_v50, hn_v49, hn_v50⟩ using hinv9 else hinv9 hG in EoCases.__eo_prog_bv_eq_extract_elim1.case_0
  pat_unapply h_v49 as ⟨v52, v53, x_v52, x_v53, h_v52, h_v53, hn_v52, hn_v53⟩ using hinv9 else hinv9 hG in EoCases.__eo_prog_bv_eq_extract_elim1.case_0
  step as ⟨e_v54, he_v54⟩
  store_step with CtorSpec.eo__3d.construct s9 e_v54 (by rw [he_v54]; exact empty_args) hinv9 h64 as ⟨v54, s10, hinv10, h_v54⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a10 h_a11 h_v50 h_v52 h_v53 dropping h_a9 h_v39 h_v45 h_v47 h_v49 he_v54 hinv9 e_v54 s9 v39 v45 v47 v49
  pat_same v52 v54 with h_v52 h_v54 using hinv10 else hinv10 hG in EoCases.__eo_prog_bv_eq_extract_elim1.case_0
  pat_same v53 a6 with h_v53 h_a6 using hinv10 else hinv10 hG in EoCases.__eo_prog_bv_eq_extract_elim1.case_0
  pat_unapply h_v50 as ⟨v56, v57, x_v56, x_v57, h_v56, h_v57, hn_v56, hn_v57⟩ using hinv10 else hinv10 hG in EoCases.__eo_prog_bv_eq_extract_elim1.case_0
  pat_unapply h_v56 as ⟨v59, v60, x_v59, x_v60, h_v59, h_v60, hn_v59, hn_v60⟩ using hinv10 else hinv10 hG in EoCases.__eo_prog_bv_eq_extract_elim1.case_0
  step as ⟨e_v61, he_v61⟩
  store_step with CtorSpec.eo__2d.construct s10 e_v61 (by rw [he_v61]; exact empty_args) hinv10 h64 as ⟨v61, s11, hinv11, h_v61⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a10 h_a11 h_v57 h_v59 h_v60 dropping h_v50 h_v52 h_v53 h_v54 h_v56 he_v61 hinv10 e_v61 s10 v50 v52 v53 v54 v56
  pat_same v59 v61 with h_v59 h_v61 using hinv11 else hinv11 hG in EoCases.__eo_prog_bv_eq_extract_elim1.case_0
  pat_same v60 a2 with h_v60 h_a2 using hinv11 else hinv11 hG in EoCases.__eo_prog_bv_eq_extract_elim1.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s11 1#u32 (1) (by scalar_tac) hinv11 h64 as ⟨v62, s12, hinv12, h_v62⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a10 h_a11 h_v57 dropping h_v59 h_v60 h_v61 hinv11 s11 v59 v60 v61
  pat_same v57 v62 with h_v57 h_v62 using hinv12 else hinv12 hG in EoCases.__eo_prog_bv_eq_extract_elim1.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a10 as ⟨v64, x_v64, h_v64⟩ else hinv12 hG in EoCases.__eo_prog_bv_eq_extract_elim1.case_0
  pat_unapply h_v64 as ⟨v66, v67, x_v66, x_v67, h_v66, h_v67, hn_v66, hn_v67⟩ using hinv12 else hinv12 hG in EoCases.__eo_prog_bv_eq_extract_elim1.case_0
  pat_unapply h_v66 as ⟨v69, v70, x_v69, x_v70, h_v69, h_v70, hn_v69, hn_v70⟩ using hinv12 else hinv12 hG in EoCases.__eo_prog_bv_eq_extract_elim1.case_0
  step as ⟨e_v71, he_v71⟩
  store_step with CtorSpec.eo__3d.construct s12 e_v71 (by rw [he_v71]; exact empty_args) hinv12 h64 as ⟨v71, s13, hinv13, h_v71⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a11 h_v67 h_v69 h_v70 dropping h_a10 h_v57 h_v62 h_v64 h_v66 he_v71 hinv12 e_v71 s12 v57 v62 v64 v66
  pat_same v69 v71 with h_v69 h_v71 using hinv13 else hinv13 hG in EoCases.__eo_prog_bv_eq_extract_elim1.case_0
  pat_unapply h_v70 as ⟨v73, v74, x_v73, x_v74, h_v73, h_v74, hn_v73, hn_v74⟩ using hinv13 else hinv13 hG in EoCases.__eo_prog_bv_eq_extract_elim1.case_0
  pat_unapply h_v73 as ⟨v76, v77, x_v76, x_v77, h_v76, h_v77, hn_v76, hn_v77⟩ using hinv13 else hinv13 hG in EoCases.__eo_prog_bv_eq_extract_elim1.case_0
  step as ⟨e_v78, he_v78⟩
  store_step with CtorSpec.eo__3e.construct s13 e_v78 (by rw [he_v78]; exact empty_args) hinv13 h64 as ⟨v78, s14, hinv14, h_v78⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a11 h_v67 h_v74 h_v76 h_v77 dropping h_v69 h_v70 h_v71 h_v73 he_v78 hinv13 e_v78 s13 v69 v70 v71 v73
  pat_same v76 v78 with h_v76 h_v78 using hinv14 else hinv14 hG in EoCases.__eo_prog_bv_eq_extract_elim1.case_0
  pat_same v77 a4 with h_v77 h_a4 using hinv14 else hinv14 hG in EoCases.__eo_prog_bv_eq_extract_elim1.case_0
  pat_same v74 a3 with h_v74 h_a3 using hinv14 else hinv14 hG in EoCases.__eo_prog_bv_eq_extract_elim1.case_0
  store_step with Store.literal_boolean_spec s14 true hinv14 h64 as ⟨v79, s15, hinv15, h_v79⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a11 h_v67 dropping h_v74 h_v76 h_v77 h_v78 hinv14 s14 v74 v76 v77 v78
  pat_same v67 v79 with h_v67 h_v79 using hinv15 else hinv15 hG in EoCases.__eo_prog_bv_eq_extract_elim1.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a11 as ⟨v81, x_v81, h_v81⟩ else hinv15 hG in EoCases.__eo_prog_bv_eq_extract_elim1.case_0
  pat_unapply h_v81 as ⟨v83, v84, x_v83, x_v84, h_v83, h_v84, hn_v83, hn_v84⟩ using hinv15 else hinv15 hG in EoCases.__eo_prog_bv_eq_extract_elim1.case_0
  pat_unapply h_v83 as ⟨v86, v87, x_v86, x_v87, h_v86, h_v87, hn_v86, hn_v87⟩ using hinv15 else hinv15 hG in EoCases.__eo_prog_bv_eq_extract_elim1.case_0
  step as ⟨e_v88, he_v88⟩
  store_step with CtorSpec.eo__3d.construct s15 e_v88 (by rw [he_v88]; exact empty_args) hinv15 h64 as ⟨v88, s16, hinv16, h_v88⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v84 h_v86 h_v87 dropping h_a11 h_v67 h_v79 h_v81 h_v83 he_v88 hinv15 e_v88 s15 v67 v79 v81 v83
  pat_same v86 v88 with h_v86 h_v88 using hinv16 else hinv16 hG in EoCases.__eo_prog_bv_eq_extract_elim1.case_0
  pat_unapply h_v87 as ⟨v90, v91, x_v90, x_v91, h_v90, h_v91, hn_v90, hn_v91⟩ using hinv16 else hinv16 hG in EoCases.__eo_prog_bv_eq_extract_elim1.case_0
  pat_unapply h_v90 as ⟨v93, v94, x_v93, x_v94, h_v93, h_v94, hn_v93, hn_v94⟩ using hinv16 else hinv16 hG in EoCases.__eo_prog_bv_eq_extract_elim1.case_0
  step as ⟨e_v95, he_v95⟩
  store_step with CtorSpec.eo__3e.construct s16 e_v95 (by rw [he_v95]; exact empty_args) hinv16 h64 as ⟨v95, s17, hinv17, h_v95⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v84 h_v91 h_v93 h_v94 dropping h_v86 h_v87 h_v88 h_v90 he_v95 hinv16 e_v95 s16 v86 v87 v88 v90
  pat_same v93 v95 with h_v93 h_v95 using hinv17 else hinv17 hG in EoCases.__eo_prog_bv_eq_extract_elim1.case_0
  pat_same v94 a2 with h_v94 h_a2 using hinv17 else hinv17 hG in EoCases.__eo_prog_bv_eq_extract_elim1.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s17 0#u32 (0) (by scalar_tac) hinv17 h64 as ⟨v96, s18, hinv18, h_v96⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v84 h_v91 dropping h_v93 h_v94 h_v95 hinv17 s17 v93 v94 v95
  pat_same v91 v96 with h_v91 h_v96 using hinv18 else hinv18 hG in EoCases.__eo_prog_bv_eq_extract_elim1.case_0
  store_step with Store.literal_boolean_spec s18 true hinv18 h64 as ⟨v97, s19, hinv19, h_v97⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v84 dropping h_v91 h_v96 hinv18 s18 v91 v96
  pat_same v84 v97 with h_v84 h_v97 using hinv19 else hinv19 hG in EoCases.__eo_prog_bv_eq_extract_elim1.case_0
  step as ⟨e_v98, he_v98⟩
  store_step with CtorSpec.eo__3d.construct s19 e_v98 (by rw [he_v98]; exact empty_args) hinv19 h64 as ⟨v98, s20, hinv20, h_v98⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 dropping h_v84 h_v97 he_v98 hinv19 e_v98 s19 v84 v97
  step as ⟨e_v99, he_v99⟩
  store_step with CtorSpec.eo__3d.construct s20 e_v99 (by rw [he_v99]; exact empty_args) hinv20 h64 as ⟨v99, s21, hinv21, h_v99⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v98 dropping he_v99 hinv20 e_v99 s20
  step as ⟨e_v100, he_v100⟩
  store_step with CtorSpec.eo_extract.construct s21 e_v100 (by rw [he_v100]; rfl) h_a3 h_a2 hinv21 h64 as ⟨v100, s22, hinv22, h_v100⟩ growing hG carrying h_a0 h_a1 h_a4 h_a5 h_a6 h_v98 h_v99 dropping h_a2 h_a3 he_v100 hinv21 e_v100 s21
  store_step with Store.apply_rep s22 v100 a0 _ _ hinv22 h64 h_v100 h_a0 (by ns_tac) (by ns_tac) as ⟨v101, s23, hinv23, h_v101⟩ growing hG carrying h_a0 h_a1 h_a4 h_a5 h_a6 h_v98 h_v99 dropping h_v100 hinv22 s22 v100
  store_step with Store.apply_rep s23 v99 v101 _ _ hinv23 h64 h_v99 h_v101 (by ns_tac) (by ns_tac) as ⟨v102, s24, hinv24, h_v102⟩ growing hG carrying h_a0 h_a1 h_a4 h_a5 h_a6 h_v98 dropping h_v101 h_v99 hinv23 s23 v101 v99
  store_step with Store.apply_rep s24 v102 a1 _ _ hinv24 h64 h_v102 h_a1 (by ns_tac) (by ns_tac) as ⟨v103, s25, hinv25, h_v103⟩ growing hG carrying h_a0 h_a1 h_a4 h_a5 h_a6 h_v98 dropping h_v102 hinv24 s24 v102
  store_step with Store.apply_rep s25 v98 v103 _ _ hinv25 h64 h_v98 h_v103 (by ns_tac) (by ns_tac) as ⟨v104, s26, hinv26, h_v104⟩ growing hG carrying h_a0 h_a1 h_a4 h_a5 h_a6 dropping h_v103 h_v98 hinv25 s25 v103 v98
  step as ⟨e_v105, he_v105⟩
  store_step with CtorSpec.eo__3d.construct s26 e_v105 (by rw [he_v105]; exact empty_args) hinv26 h64 as ⟨v105, s27, hinv27, h_v105⟩ growing hG carrying h_a0 h_a1 h_a4 h_a5 h_a6 h_v104 dropping he_v105 hinv26 e_v105 s26
  store_step with Store.apply_rep s27 v105 a0 _ _ hinv27 h64 h_v105 h_a0 (by ns_tac) (by ns_tac) as ⟨v106, s28, hinv28, h_v106⟩ growing hG carrying h_a0 h_a1 h_a4 h_a5 h_a6 h_v104 dropping h_v105 hinv27 s27 v105
  step as ⟨e_v107, he_v107⟩
  store_step with CtorSpec.eo_concat.construct s28 e_v107 (by rw [he_v107]; exact empty_args) hinv28 h64 as ⟨v107, s29, hinv29, h_v107⟩ growing hG carrying h_a0 h_a1 h_a4 h_a5 h_a6 h_v104 h_v106 dropping he_v107 hinv28 e_v107 s28
  step as ⟨e_v108, he_v108⟩
  store_step with CtorSpec.eo_extract.construct s29 e_v108 (by rw [he_v108]; rfl) h_a4 h_a5 hinv29 h64 as ⟨v108, s30, hinv30, h_v108⟩ growing hG carrying h_a0 h_a1 h_a6 h_v104 h_v106 h_v107 dropping h_a4 h_a5 he_v108 hinv29 e_v108 s29
  store_step with Store.apply_rep s30 v108 a0 _ _ hinv30 h64 h_v108 h_a0 (by ns_tac) (by ns_tac) as ⟨v109, s31, hinv31, h_v109⟩ growing hG carrying h_a0 h_a1 h_a6 h_v104 h_v106 h_v107 dropping h_v108 hinv30 s30 v108
  store_step with Store.apply_rep s31 v107 v109 _ _ hinv31 h64 h_v107 h_v109 (by ns_tac) (by ns_tac) as ⟨v110, s32, hinv32, h_v110⟩ growing hG carrying h_a0 h_a1 h_a6 h_v104 h_v106 dropping h_v107 h_v109 hinv31 s31 v107 v109
  step as ⟨e_v111, he_v111⟩
  store_step with CtorSpec.eo_concat.construct s32 e_v111 (by rw [he_v111]; exact empty_args) hinv32 h64 as ⟨v111, s33, hinv33, h_v111⟩ growing hG carrying h_a0 h_a1 h_a6 h_v104 h_v106 h_v110 dropping he_v111 hinv32 e_v111 s32
  store_step with Store.apply_rep s33 v111 a1 _ _ hinv33 h64 h_v111 h_a1 (by ns_tac) (by ns_tac) as ⟨v112, s34, hinv34, h_v112⟩ growing hG carrying h_a0 h_a6 h_v104 h_v106 h_v110 dropping h_a1 h_v111 hinv33 s33 v111
  step as ⟨e_v113, he_v113⟩
  store_step with CtorSpec.eo_concat.construct s34 e_v113 (by rw [he_v113]; exact empty_args) hinv34 h64 as ⟨v113, s35, hinv35, h_v113⟩ growing hG carrying h_a0 h_a6 h_v104 h_v106 h_v110 h_v112 dropping he_v113 hinv34 e_v113 s34
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s35 0#u32 (0) (by scalar_tac) hinv35 h64 as ⟨v114, s36, hinv36, h_v114⟩ growing hG carrying h_a0 h_a6 h_v104 h_v106 h_v110 h_v112 h_v113 dropping hinv35 s35
  step as ⟨e_v115, he_v115⟩
  store_step with CtorSpec.eo_extract.construct s36 e_v115 (by rw [he_v115]; rfl) h_a6 h_v114 hinv36 h64 as ⟨v115, s37, hinv37, h_v115⟩ growing hG carrying h_a0 h_v104 h_v106 h_v110 h_v112 h_v113 dropping h_a6 h_v114 he_v115 hinv36 e_v115 s36 v114
  store_step with Store.apply_rep s37 v115 a0 _ _ hinv37 h64 h_v115 h_a0 (by ns_tac) (by ns_tac) as ⟨v116, s38, hinv38, h_v116⟩ growing hG carrying h_v104 h_v106 h_v110 h_v112 h_v113 dropping h_a0 h_v115 hinv37 s37 v115
  store_step with Store.apply_rep s38 v113 v116 _ _ hinv38 h64 h_v113 h_v116 (by ns_tac) (by ns_tac) as ⟨v117, s39, hinv39, h_v117⟩ growing hG carrying h_v104 h_v106 h_v110 h_v112 dropping h_v113 h_v116 hinv38 s38 v113 v116
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s39 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv39 h64 as ⟨v118, s40, hinv40, h_v118⟩ growing hG carrying h_v104 h_v106 h_v110 h_v112 h_v117 dropping hinv39 s39
  store_step with Store.apply_rep s40 v117 v118 _ _ hinv40 h64 h_v117 h_v118 (by ns_tac) (by ns_tac) as ⟨v119, s41, hinv41, h_v119⟩ growing hG carrying h_v104 h_v106 h_v110 h_v112 dropping h_v117 h_v118 hinv40 s40 v117 v118
  store_step with Store.apply_rep s41 v112 v119 _ _ hinv41 h64 h_v112 h_v119 (by ns_tac) (by ns_tac) as ⟨v120, s42, hinv42, h_v120⟩ growing hG carrying h_v104 h_v106 h_v110 dropping h_v112 h_v119 hinv41 s41 v112 v119
  store_step with Store.apply_rep s42 v110 v120 _ _ hinv42 h64 h_v110 h_v120 (by ns_tac) (by ns_tac) as ⟨v121, s43, hinv43, h_v121⟩ growing hG carrying h_v104 h_v106 dropping h_v110 h_v120 hinv42 s42 v110 v120
  store_step with Store.apply_rep s43 v106 v121 _ _ hinv43 h64 h_v106 h_v121 (by ns_tac) (by ns_tac) as ⟨v122, s44, hinv44, h_v122⟩ growing hG carrying h_v104 dropping h_v106 h_v121 hinv43 s43 v106 v121
  store_step with Store.apply_rep s44 v104 v122 _ _ hinv44 h64 h_v104 h_v122 (by ns_tac) (by ns_tac) as ⟨v123, s45, hinv45, h_v123⟩ growing hG carrying dropping h_v104 h_v122 hinv44 s44 v104 v122
  case_done hinv45 hG with h_v123 in EoCases.__eo_prog_bv_eq_extract_elim1.case_0 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_a5 hn_a6 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v13 hn_v14 hn_v17 hn_v18 hn_v24 hn_v25 hn_v27 hn_v28 hn_v31 hn_v32 hn_v34 hn_v35 hn_v38 hn_v39 hn_v41 hn_v42 hn_v49 hn_v50 hn_v52 hn_v53 hn_v56 hn_v57 hn_v59 hn_v60 hn_v66 hn_v67 hn_v69 hn_v70 hn_v73 hn_v74 hn_v76 hn_v77 hn_v83 hn_v84 hn_v86 hn_v87 hn_v90 hn_v91 hn_v93 hn_v94

set_option maxHeartbeats 4000000 in
/-- logos's `__eo_prog_bv_eq_extract_elim1` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fbv_2deq_2dextract_2delim1.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _) (x_a7 : _) (x_a8 : _) (x_a9 : _) (x_a10 : _) (x_a11 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) (hw_a4 : Valid.valid x_a4) (hw_a5 : Valid.valid x_a5) (hw_a6 : Valid.valid x_a6) (hw_a7 : Valid.valid x_a7) (hw_a8 : Valid.valid x_a8) (hw_a9 : Valid.valid x_a9) (hw_a10 : Valid.valid x_a10) (hw_a11 : Valid.valid x_a11) :
    __eo_prog_bv_eq_extract_elim1 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 x_a9 x_a10 x_a11 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else if x_a4 = Eo.Term.Stuck then HasStuck.stuck else if x_a5 = Eo.Term.Stuck then HasStuck.stuck else if x_a6 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_bv_eq_extract_elim1.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 x_a9 x_a10 x_a11] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_bv_eq_extract_elim1
  unfold EoCases.__eo_prog_bv_eq_extract_elim1.case_0
  logos_eq

set_option maxHeartbeats 4000000 in
theorem body_eo__24eo_5fprog_5fbv_2deq_2dextract_2delim1_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _) (x_a7 : _) (x_a8 : _) (x_a9 : _) (x_a10 : _) (x_a11 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) (h_a6 : Represents.rep s a6 x_a6) (h_a7 : Represents.rep s a7 x_a7) (h_a8 : Represents.rep s a8 x_a8) (h_a9 : Represents.rep s a9 x_a9) (h_a10 : Represents.rep s a10 x_a10) (h_a11 : Represents.rep s a11 x_a11) :
    body_eo__24eo_5fprog_5fbv_2deq_2dextract_2delim1 s a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_eq_extract_elim1 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 x_a9 x_a10 x_a11)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fbv_2deq_2dextract_2delim1.rust_eq x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 x_a9 x_a10 x_a11 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3) (by valid_tac hinv h_a4) (by valid_tac hinv h_a5) (by valid_tac hinv h_a6) (by valid_tac hinv h_a7) (by valid_tac hinv h_a8) (by valid_tac hinv h_a9) (by valid_tac hinv h_a10) (by valid_tac hinv h_a11)]
  unfold body_eo__24eo_5fprog_5fbv_2deq_2dextract_2delim1
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  stuck_check h_a3 : x_a3 as hn_a3 else hinv hG
  stuck_check h_a4 : x_a4 as hn_a4 else hinv hG
  stuck_check h_a5 : x_a5 as hn_a5 else hinv hG
  stuck_check h_a6 : x_a6 as hn_a6 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fbv_2deq_2dextract_2delim1_spec n ih s a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 x_a9 x_a10 x_a11 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 h_a9 h_a10 h_a11 hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_a5 hn_a6
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 h_a9 h_a10 h_a11 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_a5 hn_a6
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_a5 hn_a6 hc0 in EoCases.__eo_prog_bv_eq_extract_elim1.case_0

set_option maxHeartbeats 4000000 in
theorem eo__24eo_5fprog_5fbv_2deq_2dextract_2delim1_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fbv_2deq_2dextract_2delim1.Spec n := by
  intro s a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 x_a9 x_a10 x_a11 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 h_a9 h_a10 h_a11
  unfold eo__24eo_5fprog_5fbv_2deq_2dextract_2delim1
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fbv_2deq_2dextract_2delim1 s1 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11) (fun s' t => Represents.rep s' t (__eo_prog_bv_eq_extract_elim1 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 x_a9 x_a10 x_a11))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fbv_2deq_2dextract_2delim1_spec m (ih m hm) s1 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 x_a9 x_a10 x_a11 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn) (by congr_one h_a4 hn) (by congr_one h_a5 hn) (by congr_one h_a6 hn) (by congr_one h_a7 hn) (by congr_one h_a8 hn) (by congr_one h_a9 hn) (by congr_one h_a10 hn) (by congr_one h_a11 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

end pathos_compiled_checker
