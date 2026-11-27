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

set_option maxHeartbeats 24000000 in
theorem case_0_eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d2_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _) (x_a7 : _) (x_a8 : _) (x_a9 : _) (x_a10 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) (h_a6 : Represents.rep s a6 x_a6) (h_a7 : Represents.rep s a7 x_a7) (h_a8 : Represents.rep s a8 x_a8) (h_a9 : Represents.rep s a9 x_a9) (h_a10 : Represents.rep s a10 x_a10) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) (hn_a4 : x_a4 ≠ Eo.Term.Stuck) (hn_a5 : x_a5 ≠ Eo.Term.Stuck) (hn_a6 : x_a6 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d2 s a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_bv_extract_concat_2.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 x_a9 x_a10 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_bv_extract_concat_2.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 x_a9 x_a10 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d2
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a7 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_bv_extract_concat_2.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_extract_concat_2.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_extract_concat_2.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a8 h_a9 h_a10 h_v4 h_v6 h_v7 dropping h_a7 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_extract_concat_2.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_extract_concat_2.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_extract_concat_2.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__3c.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a8 h_a9 h_a10 h_v4 h_v11 h_v13 h_v14 dropping h_v10 h_v6 h_v7 h_v8 he_v15 hinv1 e_v15 s1 v10 v6 v7 v8
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_extract_concat_2.case_0
  pat_same v14 a3 with h_v14 h_a3 using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_extract_concat_2.case_0
  pat_unapply h_v11 as ⟨v17, v18, x_v17, x_v18, h_v17, h_v18, hn_v17, hn_v18⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_extract_concat_2.case_0
  step as ⟨e_v19, he_v19⟩
  store_step with CtorSpec.eo__40bvsize.construct s2 e_v19 (by rw [he_v19]; exact empty_args) hinv2 h64 as ⟨v19, s3, hinv3, h_v19⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a8 h_a9 h_a10 h_v4 h_v17 h_v18 dropping h_v11 h_v13 h_v14 h_v15 he_v19 hinv2 e_v19 s2 v11 v13 v14 v15
  pat_same v17 v19 with h_v17 h_v19 using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_extract_concat_2.case_0
  pat_same v18 a0 with h_v18 h_a0 using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_extract_concat_2.case_0
  store_step with Store.literal_boolean_spec s3 true hinv3 h64 as ⟨v20, s4, hinv4, h_v20⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a8 h_a9 h_a10 h_v4 dropping h_v17 h_v18 h_v19 hinv3 s3 v17 v18 v19
  pat_same v4 v20 with h_v4 h_v20 using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_extract_concat_2.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a8 as ⟨v22, x_v22, h_v22⟩ else hinv4 hG in EoCases.__eo_prog_bv_extract_concat_2.case_0
  pat_unapply h_v22 as ⟨v24, v25, x_v24, x_v25, h_v24, h_v25, hn_v24, hn_v25⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_extract_concat_2.case_0
  pat_unapply h_v24 as ⟨v27, v28, x_v27, x_v28, h_v27, h_v28, hn_v27, hn_v28⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_extract_concat_2.case_0
  step as ⟨e_v29, he_v29⟩
  store_step with CtorSpec.eo__3d.construct s4 e_v29 (by rw [he_v29]; exact empty_args) hinv4 h64 as ⟨v29, s5, hinv5, h_v29⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a9 h_a10 h_v25 h_v27 h_v28 dropping h_a8 h_v20 h_v22 h_v24 h_v4 he_v29 hinv4 e_v29 s4 v20 v22 v24 v4
  pat_same v27 v29 with h_v27 h_v29 using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_extract_concat_2.case_0
  pat_unapply h_v28 as ⟨v31, v32, x_v31, x_v32, h_v31, h_v32, hn_v31, hn_v32⟩ using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_extract_concat_2.case_0
  pat_unapply h_v31 as ⟨v34, v35, x_v34, x_v35, h_v34, h_v35, hn_v34, hn_v35⟩ using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_extract_concat_2.case_0
  step as ⟨e_v36, he_v36⟩
  store_step with CtorSpec.eo__3e_3d.construct s5 e_v36 (by rw [he_v36]; exact empty_args) hinv5 h64 as ⟨v36, s6, hinv6, h_v36⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a9 h_a10 h_v25 h_v32 h_v34 h_v35 dropping h_v27 h_v28 h_v29 h_v31 he_v36 hinv5 e_v36 s5 v27 v28 v29 v31
  pat_same v34 v36 with h_v34 h_v36 using hinv6 else hinv6 hG in EoCases.__eo_prog_bv_extract_concat_2.case_0
  pat_same v35 a4 with h_v35 h_a4 using hinv6 else hinv6 hG in EoCases.__eo_prog_bv_extract_concat_2.case_0
  pat_unapply h_v32 as ⟨v38, v39, x_v38, x_v39, h_v38, h_v39, hn_v38, hn_v39⟩ using hinv6 else hinv6 hG in EoCases.__eo_prog_bv_extract_concat_2.case_0
  step as ⟨e_v40, he_v40⟩
  store_step with CtorSpec.eo__40bvsize.construct s6 e_v40 (by rw [he_v40]; exact empty_args) hinv6 h64 as ⟨v40, s7, hinv7, h_v40⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a9 h_a10 h_v25 h_v38 h_v39 dropping h_v32 h_v34 h_v35 h_v36 he_v40 hinv6 e_v40 s6 v32 v34 v35 v36
  pat_same v38 v40 with h_v38 h_v40 using hinv7 else hinv7 hG in EoCases.__eo_prog_bv_extract_concat_2.case_0
  pat_same v39 a0 with h_v39 h_a0 using hinv7 else hinv7 hG in EoCases.__eo_prog_bv_extract_concat_2.case_0
  store_step with Store.literal_boolean_spec s7 true hinv7 h64 as ⟨v41, s8, hinv8, h_v41⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a9 h_a10 h_v25 dropping h_v38 h_v39 h_v40 hinv7 s7 v38 v39 v40
  pat_same v25 v41 with h_v25 h_v41 using hinv8 else hinv8 hG in EoCases.__eo_prog_bv_extract_concat_2.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a9 as ⟨v43, x_v43, h_v43⟩ else hinv8 hG in EoCases.__eo_prog_bv_extract_concat_2.case_0
  pat_unapply h_v43 as ⟨v45, v46, x_v45, x_v46, h_v45, h_v46, hn_v45, hn_v46⟩ using hinv8 else hinv8 hG in EoCases.__eo_prog_bv_extract_concat_2.case_0
  pat_unapply h_v45 as ⟨v48, v49, x_v48, x_v49, h_v48, h_v49, hn_v48, hn_v49⟩ using hinv8 else hinv8 hG in EoCases.__eo_prog_bv_extract_concat_2.case_0
  step as ⟨e_v50, he_v50⟩
  store_step with CtorSpec.eo__3d.construct s8 e_v50 (by rw [he_v50]; exact empty_args) hinv8 h64 as ⟨v50, s9, hinv9, h_v50⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a10 h_v46 h_v48 h_v49 dropping h_a9 h_v25 h_v41 h_v43 h_v45 he_v50 hinv8 e_v50 s8 v25 v41 v43 v45
  pat_same v48 v50 with h_v48 h_v50 using hinv9 else hinv9 hG in EoCases.__eo_prog_bv_extract_concat_2.case_0
  pat_same v49 a5 with h_v49 h_a5 using hinv9 else hinv9 hG in EoCases.__eo_prog_bv_extract_concat_2.case_0
  pat_unapply h_v46 as ⟨v52, v53, x_v52, x_v53, h_v52, h_v53, hn_v52, hn_v53⟩ using hinv9 else hinv9 hG in EoCases.__eo_prog_bv_extract_concat_2.case_0
  pat_unapply h_v52 as ⟨v55, v56, x_v55, x_v56, h_v55, h_v56, hn_v55, hn_v56⟩ using hinv9 else hinv9 hG in EoCases.__eo_prog_bv_extract_concat_2.case_0
  step as ⟨e_v57, he_v57⟩
  store_step with CtorSpec.eo__2d.construct s9 e_v57 (by rw [he_v57]; exact empty_args) hinv9 h64 as ⟨v57, s10, hinv10, h_v57⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a10 h_v53 h_v55 h_v56 dropping h_v46 h_v48 h_v49 h_v50 h_v52 he_v57 hinv9 e_v57 s9 v46 v48 v49 v50 v52
  pat_same v55 v57 with h_v55 h_v57 using hinv10 else hinv10 hG in EoCases.__eo_prog_bv_extract_concat_2.case_0
  pat_same v56 a4 with h_v56 h_a4 using hinv10 else hinv10 hG in EoCases.__eo_prog_bv_extract_concat_2.case_0
  pat_unapply h_v53 as ⟨v59, v60, x_v59, x_v60, h_v59, h_v60, hn_v59, hn_v60⟩ using hinv10 else hinv10 hG in EoCases.__eo_prog_bv_extract_concat_2.case_0
  step as ⟨e_v61, he_v61⟩
  store_step with CtorSpec.eo__40bvsize.construct s10 e_v61 (by rw [he_v61]; exact empty_args) hinv10 h64 as ⟨v61, s11, hinv11, h_v61⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a10 h_v59 h_v60 dropping h_v53 h_v55 h_v56 h_v57 he_v61 hinv10 e_v61 s10 v53 v55 v56 v57
  pat_same v59 v61 with h_v59 h_v61 using hinv11 else hinv11 hG in EoCases.__eo_prog_bv_extract_concat_2.case_0
  pat_same v60 a0 with h_v60 h_a0 using hinv11 else hinv11 hG in EoCases.__eo_prog_bv_extract_concat_2.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a10 as ⟨v63, x_v63, h_v63⟩ else hinv11 hG in EoCases.__eo_prog_bv_extract_concat_2.case_0
  pat_unapply h_v63 as ⟨v65, v66, x_v65, x_v66, h_v65, h_v66, hn_v65, hn_v66⟩ using hinv11 else hinv11 hG in EoCases.__eo_prog_bv_extract_concat_2.case_0
  pat_unapply h_v65 as ⟨v68, v69, x_v68, x_v69, h_v68, h_v69, hn_v68, hn_v69⟩ using hinv11 else hinv11 hG in EoCases.__eo_prog_bv_extract_concat_2.case_0
  step as ⟨e_v70, he_v70⟩
  store_step with CtorSpec.eo__3d.construct s11 e_v70 (by rw [he_v70]; exact empty_args) hinv11 h64 as ⟨v70, s12, hinv12, h_v70⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v66 h_v68 h_v69 dropping h_a10 h_v59 h_v60 h_v61 h_v63 h_v65 he_v70 hinv11 e_v70 s11 v59 v60 v61 v63 v65
  pat_same v68 v70 with h_v68 h_v70 using hinv12 else hinv12 hG in EoCases.__eo_prog_bv_extract_concat_2.case_0
  pat_same v69 a6 with h_v69 h_a6 using hinv12 else hinv12 hG in EoCases.__eo_prog_bv_extract_concat_2.case_0
  pat_unapply h_v66 as ⟨v72, v73, x_v72, x_v73, h_v72, h_v73, hn_v72, hn_v73⟩ using hinv12 else hinv12 hG in EoCases.__eo_prog_bv_extract_concat_2.case_0
  pat_unapply h_v72 as ⟨v75, v76, x_v75, x_v76, h_v75, h_v76, hn_v75, hn_v76⟩ using hinv12 else hinv12 hG in EoCases.__eo_prog_bv_extract_concat_2.case_0
  step as ⟨e_v77, he_v77⟩
  store_step with CtorSpec.eo__2d.construct s12 e_v77 (by rw [he_v77]; exact empty_args) hinv12 h64 as ⟨v77, s13, hinv13, h_v77⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v73 h_v75 h_v76 dropping h_v66 h_v68 h_v69 h_v70 h_v72 he_v77 hinv12 e_v77 s12 v66 v68 v69 v70 v72
  pat_same v75 v77 with h_v75 h_v77 using hinv13 else hinv13 hG in EoCases.__eo_prog_bv_extract_concat_2.case_0
  pat_unapply h_v76 as ⟨v79, v80, x_v79, x_v80, h_v79, h_v80, hn_v79, hn_v80⟩ using hinv13 else hinv13 hG in EoCases.__eo_prog_bv_extract_concat_2.case_0
  step as ⟨e_v81, he_v81⟩
  store_step with CtorSpec.eo__40bvsize.construct s13 e_v81 (by rw [he_v81]; exact empty_args) hinv13 h64 as ⟨v81, s14, hinv14, h_v81⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v73 h_v79 h_v80 dropping h_v75 h_v76 h_v77 he_v81 hinv13 e_v81 s13 v75 v76 v77
  pat_same v79 v81 with h_v79 h_v81 using hinv14 else hinv14 hG in EoCases.__eo_prog_bv_extract_concat_2.case_0
  pat_same v80 a0 with h_v80 h_a0 using hinv14 else hinv14 hG in EoCases.__eo_prog_bv_extract_concat_2.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s14 1#u32 (1) (by scalar_tac) hinv14 h64 as ⟨v82, s15, hinv15, h_v82⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v73 dropping h_v79 h_v80 h_v81 hinv14 s14 v79 v80 v81
  pat_same v73 v82 with h_v73 h_v82 using hinv15 else hinv15 hG in EoCases.__eo_prog_bv_extract_concat_2.case_0
  step as ⟨e_v83, he_v83⟩
  store_step with CtorSpec.eo__3d.construct s15 e_v83 (by rw [he_v83]; exact empty_args) hinv15 h64 as ⟨v83, s16, hinv16, h_v83⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 dropping h_v73 h_v82 he_v83 hinv15 e_v83 s15 v73 v82
  step as ⟨e_v84, he_v84⟩
  store_step with CtorSpec.eo_extract.construct s16 e_v84 (by rw [he_v84]; rfl) h_a4 h_a3 hinv16 h64 as ⟨v84, s17, hinv17, h_v84⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a5 h_a6 h_v83 dropping h_a4 he_v84 hinv16 e_v84 s16
  step as ⟨e_v85, he_v85⟩
  store_step with CtorSpec.eo_concat.construct s17 e_v85 (by rw [he_v85]; exact empty_args) hinv17 h64 as ⟨v85, s18, hinv18, h_v85⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a5 h_a6 h_v83 h_v84 dropping he_v85 hinv17 e_v85 s17
  step as ⟨e_v86, he_v86⟩
  store_step with CtorSpec.eo_concat.construct s18 e_v86 (by rw [he_v86]; exact empty_args) hinv18 h64 as ⟨v86, s19, hinv19, h_v86⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a5 h_a6 h_v83 h_v84 h_v85 dropping he_v86 hinv18 e_v86 s18
  store_step with Store.apply_rep s19 v86 a2 _ _ hinv19 h64 h_v86 h_a2 (by ns_tac) (by ns_tac) as ⟨v87, s20, hinv20, h_v87⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a5 h_a6 h_v83 h_v84 h_v85 dropping h_v86 hinv19 s19 v86
  step as ⟨e_v88, he_v88⟩
  store_step with CtorSpec.eo_concat.construct s20 e_v88 (by rw [he_v88]; exact empty_args) hinv20 h64 as ⟨v88, s21, hinv21, h_v88⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a5 h_a6 h_v83 h_v84 h_v85 h_v87 dropping he_v88 hinv20 e_v88 s20
  store_step with Store.apply_rep s21 v88 a0 _ _ hinv21 h64 h_v88 h_a0 (by ns_tac) (by ns_tac) as ⟨v89, s22, hinv22, h_v89⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a5 h_a6 h_v83 h_v84 h_v85 h_v87 dropping h_v88 hinv21 s21 v88
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s22 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv22 h64 as ⟨v90, s23, hinv23, h_v90⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a5 h_a6 h_v83 h_v84 h_v85 h_v87 h_v89 dropping hinv22 s22
  store_step with Store.apply_rep s23 v89 v90 _ _ hinv23 h64 h_v89 h_v90 (by ns_tac) (by ns_tac) as ⟨v91, s24, hinv24, h_v91⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a5 h_a6 h_v83 h_v84 h_v85 h_v87 dropping h_v89 h_v90 hinv23 s23 v89 v90
  store_step with Store.apply_rep s24 v87 v91 _ _ hinv24 h64 h_v87 h_v91 (by ns_tac) (by ns_tac) as ⟨v92, s25, hinv25, h_v92⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a5 h_a6 h_v83 h_v84 h_v85 dropping h_v87 h_v91 hinv24 s24 v87 v91
  step as ⟨e_v93, he_v93⟩
  store_step with Store.builtin_spec_list_concat n ih.eo__24eo_5fis_5flist_5fnil s25 e_v93 (by rw [he_v93]; rfl) h_v85 h_a1 h_v92 hinv25 h64 (hG.rem hrem) op_not_left_eo_concat op_unique_nil_eo_concat as ⟨v93, s26, hinv26, h_v93⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a5 h_a6 h_v83 h_v84 dropping h_v85 h_v92 he_v93 hinv25 e_v93 s25 v85 v92
  store_step with Store.apply_mk_rep s26 v84 v93 _ _ hinv26 h64 h_v84 h_v93 as ⟨v94, s27, hinv27, h_v94⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a5 h_a6 h_v83 dropping h_v84 h_v93 hinv26 s26 v84 v93
  store_step with Store.apply_mk_rep s27 v83 v94 _ _ hinv27 h64 h_v83 h_v94 as ⟨v95, s28, hinv28, h_v95⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a5 h_a6 dropping h_v83 h_v94 hinv27 s27 v83 v94
  step as ⟨e_v96, he_v96⟩
  store_step with CtorSpec.eo_concat.construct s28 e_v96 (by rw [he_v96]; exact empty_args) hinv28 h64 as ⟨v96, s29, hinv29, h_v96⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a5 h_a6 h_v95 dropping he_v96 hinv28 e_v96 s28
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s29 0#u32 (0) (by scalar_tac) hinv29 h64 as ⟨v97, s30, hinv30, h_v97⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a5 h_a6 h_v95 h_v96 dropping hinv29 s29
  step as ⟨e_v98, he_v98⟩
  store_step with CtorSpec.eo_extract.construct s30 e_v98 (by rw [he_v98]; rfl) h_a5 h_v97 hinv30 h64 as ⟨v98, s31, hinv31, h_v98⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a6 h_v95 h_v96 dropping h_a5 h_v97 he_v98 hinv30 e_v98 s30 v97
  step as ⟨e_v99, he_v99⟩
  store_step with CtorSpec.eo_concat.construct s31 e_v99 (by rw [he_v99]; exact empty_args) hinv31 h64 as ⟨v99, s32, hinv32, h_v99⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a6 h_v95 h_v96 h_v98 dropping he_v99 hinv31 e_v99 s31
  step as ⟨e_v100, he_v100⟩
  store_step with CtorSpec.eo_concat.construct s32 e_v100 (by rw [he_v100]; exact empty_args) hinv32 h64 as ⟨v100, s33, hinv33, h_v100⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a6 h_v95 h_v96 h_v98 h_v99 dropping he_v100 hinv32 e_v100 s32
  step as ⟨e_v101, he_v101⟩
  store_step with CtorSpec.eo_concat.construct s33 e_v101 (by rw [he_v101]; exact empty_args) hinv33 h64 as ⟨v101, s34, hinv34, h_v101⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a6 h_v95 h_v96 h_v98 h_v99 h_v100 dropping he_v101 hinv33 e_v101 s33
  store_step with Store.apply_rep s34 v101 a2 _ _ hinv34 h64 h_v101 h_a2 (by ns_tac) (by ns_tac) as ⟨v102, s35, hinv35, h_v102⟩ growing hG carrying h_a0 h_a1 h_a3 h_a6 h_v95 h_v96 h_v98 h_v99 h_v100 dropping h_a2 h_v101 hinv34 s34 v101
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s35 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv35 h64 as ⟨v103, s36, hinv36, h_v103⟩ growing hG carrying h_a0 h_a1 h_a3 h_a6 h_v95 h_v96 h_v98 h_v99 h_v100 h_v102 dropping hinv35 s35
  store_step with Store.apply_rep s36 v102 v103 _ _ hinv36 h64 h_v102 h_v103 (by ns_tac) (by ns_tac) as ⟨v104, s37, hinv37, h_v104⟩ growing hG carrying h_a0 h_a1 h_a3 h_a6 h_v95 h_v96 h_v98 h_v99 h_v100 dropping h_v102 h_v103 hinv36 s36 v102 v103
  step as ⟨e_v105, he_v105⟩
  store_step with Store.builtin_spec_list_concat n ih.eo__24eo_5fis_5flist_5fnil s37 e_v105 (by rw [he_v105]; rfl) h_v100 h_a1 h_v104 hinv37 h64 (hG.rem hrem) op_not_left_eo_concat op_unique_nil_eo_concat as ⟨v105, s38, hinv38, h_v105⟩ growing hG carrying h_a0 h_a3 h_a6 h_v95 h_v96 h_v98 h_v99 dropping h_a1 h_v100 h_v104 he_v105 hinv37 e_v105 s37 v100 v104
  step as ⟨e_v106, he_v106⟩
  store_step with Store.builtin_spec_list_singleton_elim n ih.eo__24eo_5fis_5flist_5fnil s38 e_v106 (by rw [he_v106]; rfl) h_v99 h_v105 hinv38 h64 (hG.rem hrem) op_not_left_eo_concat op_nil_apply_eo_concat as ⟨v106, s39, hinv39, h_v106⟩ growing hG carrying h_a0 h_a3 h_a6 h_v95 h_v96 h_v98 dropping h_v105 h_v99 he_v106 hinv38 e_v106 s38 v105 v99
  store_step with Store.apply_mk_rep s39 v98 v106 _ _ hinv39 h64 h_v98 h_v106 as ⟨v107, s40, hinv40, h_v107⟩ growing hG carrying h_a0 h_a3 h_a6 h_v95 h_v96 dropping h_v106 h_v98 hinv39 s39 v106 v98
  store_step with Store.apply_mk_rep s40 v96 v107 _ _ hinv40 h64 h_v96 h_v107 as ⟨v108, s41, hinv41, h_v108⟩ growing hG carrying h_a0 h_a3 h_a6 h_v95 dropping h_v107 h_v96 hinv40 s40 v107 v96
  step as ⟨e_v109, he_v109⟩
  store_step with CtorSpec.eo_concat.construct s41 e_v109 (by rw [he_v109]; exact empty_args) hinv41 h64 as ⟨v109, s42, hinv42, h_v109⟩ growing hG carrying h_a0 h_a3 h_a6 h_v95 h_v108 dropping he_v109 hinv41 e_v109 s41
  step as ⟨e_v110, he_v110⟩
  store_step with CtorSpec.eo_extract.construct s42 e_v110 (by rw [he_v110]; rfl) h_a6 h_a3 hinv42 h64 as ⟨v110, s43, hinv43, h_v110⟩ growing hG carrying h_a0 h_v95 h_v108 h_v109 dropping h_a3 h_a6 he_v110 hinv42 e_v110 s42
  store_step with Store.apply_rep s43 v110 a0 _ _ hinv43 h64 h_v110 h_a0 (by ns_tac) (by ns_tac) as ⟨v111, s44, hinv44, h_v111⟩ growing hG carrying h_v95 h_v108 h_v109 dropping h_a0 h_v110 hinv43 s43 v110
  store_step with Store.apply_rep s44 v109 v111 _ _ hinv44 h64 h_v109 h_v111 (by ns_tac) (by ns_tac) as ⟨v112, s45, hinv45, h_v112⟩ growing hG carrying h_v95 h_v108 dropping h_v109 h_v111 hinv44 s44 v109 v111
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s45 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv45 h64 as ⟨v113, s46, hinv46, h_v113⟩ growing hG carrying h_v95 h_v108 h_v112 dropping hinv45 s45
  store_step with Store.apply_rep s46 v112 v113 _ _ hinv46 h64 h_v112 h_v113 (by ns_tac) (by ns_tac) as ⟨v114, s47, hinv47, h_v114⟩ growing hG carrying h_v95 h_v108 dropping h_v112 h_v113 hinv46 s46 v112 v113
  store_step with Store.apply_mk_rep s47 v108 v114 _ _ hinv47 h64 h_v108 h_v114 as ⟨v115, s48, hinv48, h_v115⟩ growing hG carrying h_v95 dropping h_v108 h_v114 hinv47 s47 v108 v114
  store_step with Store.apply_mk_rep s48 v95 v115 _ _ hinv48 h64 h_v95 h_v115 as ⟨v116, s49, hinv49, h_v116⟩ growing hG carrying dropping h_v115 h_v95 hinv48 s48 v115 v95
  case_done hinv49 hG with h_v116 in EoCases.__eo_prog_bv_extract_concat_2.case_0 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_a5 hn_a6 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v13 hn_v14 hn_v17 hn_v18 hn_v24 hn_v25 hn_v27 hn_v28 hn_v31 hn_v32 hn_v34 hn_v35 hn_v38 hn_v39 hn_v45 hn_v46 hn_v48 hn_v49 hn_v52 hn_v53 hn_v55 hn_v56 hn_v59 hn_v60 hn_v65 hn_v66 hn_v68 hn_v69 hn_v72 hn_v73 hn_v75 hn_v76 hn_v79 hn_v80

set_option maxHeartbeats 24000000 in
/-- logos's `__eo_prog_bv_extract_concat_2` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d2.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _) (x_a7 : _) (x_a8 : _) (x_a9 : _) (x_a10 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) (hw_a4 : Valid.valid x_a4) (hw_a5 : Valid.valid x_a5) (hw_a6 : Valid.valid x_a6) (hw_a7 : Valid.valid x_a7) (hw_a8 : Valid.valid x_a8) (hw_a9 : Valid.valid x_a9) (hw_a10 : Valid.valid x_a10) :
    __eo_prog_bv_extract_concat_2 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 x_a9 x_a10 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else if x_a4 = Eo.Term.Stuck then HasStuck.stuck else if x_a5 = Eo.Term.Stuck then HasStuck.stuck else if x_a6 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_bv_extract_concat_2.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 x_a9 x_a10] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_bv_extract_concat_2
  unfold EoCases.__eo_prog_bv_extract_concat_2.case_0
  logos_eq

set_option maxHeartbeats 24000000 in
theorem body_eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d2_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _) (x_a7 : _) (x_a8 : _) (x_a9 : _) (x_a10 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) (h_a6 : Represents.rep s a6 x_a6) (h_a7 : Represents.rep s a7 x_a7) (h_a8 : Represents.rep s a8 x_a8) (h_a9 : Represents.rep s a9 x_a9) (h_a10 : Represents.rep s a10 x_a10) :
    body_eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d2 s a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_extract_concat_2 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 x_a9 x_a10)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d2.rust_eq x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 x_a9 x_a10 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3) (by valid_tac hinv h_a4) (by valid_tac hinv h_a5) (by valid_tac hinv h_a6) (by valid_tac hinv h_a7) (by valid_tac hinv h_a8) (by valid_tac hinv h_a9) (by valid_tac hinv h_a10)]
  unfold body_eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d2
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  stuck_check h_a3 : x_a3 as hn_a3 else hinv hG
  stuck_check h_a4 : x_a4 as hn_a4 else hinv hG
  stuck_check h_a5 : x_a5 as hn_a5 else hinv hG
  stuck_check h_a6 : x_a6 as hn_a6 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d2_spec n ih s a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 x_a9 x_a10 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 h_a9 h_a10 hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_a5 hn_a6
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 h_a9 h_a10 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_a5 hn_a6
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_a5 hn_a6 hc0 in EoCases.__eo_prog_bv_extract_concat_2.case_0

set_option maxHeartbeats 24000000 in
theorem eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d2_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d2.Spec n := by
  intro s a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 x_a9 x_a10 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 h_a9 h_a10
  unfold eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d2
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d2 s1 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10) (fun s' t => Represents.rep s' t (__eo_prog_bv_extract_concat_2 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 x_a9 x_a10))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d2_spec m (ih m hm) s1 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 x_a9 x_a10 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn) (by congr_one h_a4 hn) (by congr_one h_a5 hn) (by congr_one h_a6 hn) (by congr_one h_a7 hn) (by congr_one h_a8 hn) (by congr_one h_a9 hn) (by congr_one h_a10 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

end pathos_compiled_checker
