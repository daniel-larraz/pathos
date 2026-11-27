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
theorem case_0_eo__24eo_5fprog_5fstr_2dreplace_2dall_2dfind_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 a6 a7 a8 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _) (x_a7 : _) (x_a8 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) (h_a6 : Represents.rep s a6 x_a6) (h_a7 : Represents.rep s a7 x_a7) (h_a8 : Represents.rep s a8 x_a8) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) (hn_a4 : x_a4 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstr_2dreplace_2dall_2dfind s a0 a1 a2 a3 a4 a5 a6 a7 a8 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_str_replace_all_find.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_str_replace_all_find.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstr_2dreplace_2dall_2dfind
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a5 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_str_replace_all_find.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_str_replace_all_find.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_str_replace_all_find.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a6 h_a7 h_a8 h_v4 h_v6 h_v7 dropping h_a5 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_str_replace_all_find.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_str_replace_all_find.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_str_replace_all_find.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__3e_3d.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a6 h_a7 h_a8 h_v4 h_v11 h_v13 h_v14 dropping h_v10 h_v6 h_v7 h_v8 he_v15 hinv1 e_v15 s1 v10 v6 v7 v8
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_replace_all_find.case_0
  pat_unapply h_v14 as ⟨v17, v18, x_v17, x_v18, h_v17, h_v18, hn_v17, hn_v18⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_str_replace_all_find.case_0
  pat_unapply h_v17 as ⟨v20, v21, x_v20, x_v21, h_v20, h_v21, hn_v20, hn_v21⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_str_replace_all_find.case_0
  pat_unapply h_v20 as ⟨v23, v24, x_v23, x_v24, h_v23, h_v24, hn_v23, hn_v24⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_str_replace_all_find.case_0
  step as ⟨e_v25, he_v25⟩
  store_step with CtorSpec.eo_str_2eindexof.construct s2 e_v25 (by rw [he_v25]; exact empty_args) hinv2 h64 as ⟨v25, s3, hinv3, h_v25⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a6 h_a7 h_a8 h_v4 h_v11 h_v18 h_v21 h_v23 h_v24 dropping h_v13 h_v14 h_v15 h_v17 h_v20 he_v25 hinv2 e_v25 s2 v13 v14 v15 v17 v20
  pat_same v23 v25 with h_v23 h_v25 using hinv3 else hinv3 hG in EoCases.__eo_prog_str_replace_all_find.case_0
  pat_same v24 a0 with h_v24 h_a0 using hinv3 else hinv3 hG in EoCases.__eo_prog_str_replace_all_find.case_0
  pat_same v21 a1 with h_v21 h_a1 using hinv3 else hinv3 hG in EoCases.__eo_prog_str_replace_all_find.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s3 0#u32 (0) (by scalar_tac) hinv3 h64 as ⟨v26, s4, hinv4, h_v26⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a6 h_a7 h_a8 h_v4 h_v11 h_v18 dropping h_v21 h_v23 h_v24 h_v25 hinv3 s3 v21 v23 v24 v25
  pat_same v18 v26 with h_v18 h_v26 using hinv4 else hinv4 hG in EoCases.__eo_prog_str_replace_all_find.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s4 0#u32 (0) (by scalar_tac) hinv4 h64 as ⟨v27, s5, hinv5, h_v27⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a6 h_a7 h_a8 h_v4 h_v11 dropping h_v18 h_v26 hinv4 s4 v18 v26
  pat_same v11 v27 with h_v11 h_v27 using hinv5 else hinv5 hG in EoCases.__eo_prog_str_replace_all_find.case_0
  store_step with Store.literal_boolean_spec s5 true hinv5 h64 as ⟨v28, s6, hinv6, h_v28⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a6 h_a7 h_a8 h_v4 dropping h_v11 h_v27 hinv5 s5 v11 v27
  pat_same v4 v28 with h_v4 h_v28 using hinv6 else hinv6 hG in EoCases.__eo_prog_str_replace_all_find.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a6 as ⟨v30, x_v30, h_v30⟩ else hinv6 hG in EoCases.__eo_prog_str_replace_all_find.case_0
  pat_unapply h_v30 as ⟨v32, v33, x_v32, x_v33, h_v32, h_v33, hn_v32, hn_v33⟩ using hinv6 else hinv6 hG in EoCases.__eo_prog_str_replace_all_find.case_0
  pat_unapply h_v32 as ⟨v35, v36, x_v35, x_v36, h_v35, h_v36, hn_v35, hn_v36⟩ using hinv6 else hinv6 hG in EoCases.__eo_prog_str_replace_all_find.case_0
  step as ⟨e_v37, he_v37⟩
  store_step with CtorSpec.eo__3d.construct s6 e_v37 (by rw [he_v37]; exact empty_args) hinv6 h64 as ⟨v37, s7, hinv7, h_v37⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a7 h_a8 h_v33 h_v35 h_v36 dropping h_a6 h_v28 h_v30 h_v32 h_v4 he_v37 hinv6 e_v37 s6 v28 v30 v32 v4
  pat_same v35 v37 with h_v35 h_v37 using hinv7 else hinv7 hG in EoCases.__eo_prog_str_replace_all_find.case_0
  pat_unapply h_v36 as ⟨v39, v40, x_v39, x_v40, h_v39, h_v40, hn_v39, hn_v40⟩ using hinv7 else hinv7 hG in EoCases.__eo_prog_str_replace_all_find.case_0
  pat_unapply h_v39 as ⟨v42, v43, x_v42, x_v43, h_v42, h_v43, hn_v42, hn_v43⟩ using hinv7 else hinv7 hG in EoCases.__eo_prog_str_replace_all_find.case_0
  step as ⟨e_v44, he_v44⟩
  store_step with CtorSpec.eo__3e.construct s7 e_v44 (by rw [he_v44]; exact empty_args) hinv7 h64 as ⟨v44, s8, hinv8, h_v44⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a7 h_a8 h_v33 h_v40 h_v42 h_v43 dropping h_v35 h_v36 h_v37 h_v39 he_v44 hinv7 e_v44 s7 v35 v36 v37 v39
  pat_same v42 v44 with h_v42 h_v44 using hinv8 else hinv8 hG in EoCases.__eo_prog_str_replace_all_find.case_0
  pat_unapply h_v43 as ⟨v46, v47, x_v46, x_v47, h_v46, h_v47, hn_v46, hn_v47⟩ using hinv8 else hinv8 hG in EoCases.__eo_prog_str_replace_all_find.case_0
  step as ⟨e_v48, he_v48⟩
  store_step with CtorSpec.eo_str_2elen.construct s8 e_v48 (by rw [he_v48]; exact empty_args) hinv8 h64 as ⟨v48, s9, hinv9, h_v48⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a7 h_a8 h_v33 h_v40 h_v46 h_v47 dropping h_v42 h_v43 h_v44 he_v48 hinv8 e_v48 s8 v42 v43 v44
  pat_same v46 v48 with h_v46 h_v48 using hinv9 else hinv9 hG in EoCases.__eo_prog_str_replace_all_find.case_0
  pat_same v47 a1 with h_v47 h_a1 using hinv9 else hinv9 hG in EoCases.__eo_prog_str_replace_all_find.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s9 0#u32 (0) (by scalar_tac) hinv9 h64 as ⟨v49, s10, hinv10, h_v49⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a7 h_a8 h_v33 h_v40 dropping h_v46 h_v47 h_v48 hinv9 s9 v46 v47 v48
  pat_same v40 v49 with h_v40 h_v49 using hinv10 else hinv10 hG in EoCases.__eo_prog_str_replace_all_find.case_0
  store_step with Store.literal_boolean_spec s10 true hinv10 h64 as ⟨v50, s11, hinv11, h_v50⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a7 h_a8 h_v33 dropping h_v40 h_v49 hinv10 s10 v40 v49
  pat_same v33 v50 with h_v33 h_v50 using hinv11 else hinv11 hG in EoCases.__eo_prog_str_replace_all_find.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a7 as ⟨v52, x_v52, h_v52⟩ else hinv11 hG in EoCases.__eo_prog_str_replace_all_find.case_0
  pat_unapply h_v52 as ⟨v54, v55, x_v54, x_v55, h_v54, h_v55, hn_v54, hn_v55⟩ using hinv11 else hinv11 hG in EoCases.__eo_prog_str_replace_all_find.case_0
  pat_unapply h_v54 as ⟨v57, v58, x_v57, x_v58, h_v57, h_v58, hn_v57, hn_v58⟩ using hinv11 else hinv11 hG in EoCases.__eo_prog_str_replace_all_find.case_0
  step as ⟨e_v59, he_v59⟩
  store_step with CtorSpec.eo__3d.construct s11 e_v59 (by rw [he_v59]; exact empty_args) hinv11 h64 as ⟨v59, s12, hinv12, h_v59⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a8 h_v55 h_v57 h_v58 dropping h_a7 h_v33 h_v50 h_v52 h_v54 he_v59 hinv11 e_v59 s11 v33 v50 v52 v54
  pat_same v57 v59 with h_v57 h_v59 using hinv12 else hinv12 hG in EoCases.__eo_prog_str_replace_all_find.case_0
  pat_same v58 a3 with h_v58 h_a3 using hinv12 else hinv12 hG in EoCases.__eo_prog_str_replace_all_find.case_0
  pat_unapply h_v55 as ⟨v61, v62, x_v61, x_v62, h_v61, h_v62, hn_v61, hn_v62⟩ using hinv12 else hinv12 hG in EoCases.__eo_prog_str_replace_all_find.case_0
  pat_unapply h_v61 as ⟨v64, v65, x_v64, x_v65, h_v64, h_v65, hn_v64, hn_v65⟩ using hinv12 else hinv12 hG in EoCases.__eo_prog_str_replace_all_find.case_0
  pat_unapply h_v64 as ⟨v67, v68, x_v67, x_v68, h_v67, h_v68, hn_v67, hn_v68⟩ using hinv12 else hinv12 hG in EoCases.__eo_prog_str_replace_all_find.case_0
  step as ⟨e_v69, he_v69⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s12 e_v69 (by rw [he_v69]; exact empty_args) hinv12 h64 as ⟨v69, s13, hinv13, h_v69⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a8 h_v62 h_v65 h_v67 h_v68 dropping h_v55 h_v57 h_v58 h_v59 h_v61 h_v64 he_v69 hinv12 e_v69 s12 v55 v57 v58 v59 v61 v64
  pat_same v67 v69 with h_v67 h_v69 using hinv13 else hinv13 hG in EoCases.__eo_prog_str_replace_all_find.case_0
  pat_same v68 a0 with h_v68 h_a0 using hinv13 else hinv13 hG in EoCases.__eo_prog_str_replace_all_find.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s13 0#u32 (0) (by scalar_tac) hinv13 h64 as ⟨v70, s14, hinv14, h_v70⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a8 h_v62 h_v65 dropping h_v67 h_v68 h_v69 hinv13 s13 v67 v68 v69
  pat_same v65 v70 with h_v65 h_v70 using hinv14 else hinv14 hG in EoCases.__eo_prog_str_replace_all_find.case_0
  pat_unapply h_v62 as ⟨v72, v73, x_v72, x_v73, h_v72, h_v73, hn_v72, hn_v73⟩ using hinv14 else hinv14 hG in EoCases.__eo_prog_str_replace_all_find.case_0
  pat_unapply h_v72 as ⟨v75, v76, x_v75, x_v76, h_v75, h_v76, hn_v75, hn_v76⟩ using hinv14 else hinv14 hG in EoCases.__eo_prog_str_replace_all_find.case_0
  pat_unapply h_v75 as ⟨v78, v79, x_v78, x_v79, h_v78, h_v79, hn_v78, hn_v79⟩ using hinv14 else hinv14 hG in EoCases.__eo_prog_str_replace_all_find.case_0
  step as ⟨e_v80, he_v80⟩
  store_step with CtorSpec.eo_str_2eindexof.construct s14 e_v80 (by rw [he_v80]; exact empty_args) hinv14 h64 as ⟨v80, s15, hinv15, h_v80⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a8 h_v73 h_v76 h_v78 h_v79 dropping h_v62 h_v65 h_v70 h_v72 h_v75 he_v80 hinv14 e_v80 s14 v62 v65 v70 v72 v75
  pat_same v78 v80 with h_v78 h_v80 using hinv15 else hinv15 hG in EoCases.__eo_prog_str_replace_all_find.case_0
  pat_same v79 a0 with h_v79 h_a0 using hinv15 else hinv15 hG in EoCases.__eo_prog_str_replace_all_find.case_0
  pat_same v76 a1 with h_v76 h_a1 using hinv15 else hinv15 hG in EoCases.__eo_prog_str_replace_all_find.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s15 0#u32 (0) (by scalar_tac) hinv15 h64 as ⟨v81, s16, hinv16, h_v81⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a8 h_v73 dropping h_v76 h_v78 h_v79 h_v80 hinv15 s15 v76 v78 v79 v80
  pat_same v73 v81 with h_v73 h_v81 using hinv16 else hinv16 hG in EoCases.__eo_prog_str_replace_all_find.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a8 as ⟨v83, x_v83, h_v83⟩ else hinv16 hG in EoCases.__eo_prog_str_replace_all_find.case_0
  pat_unapply h_v83 as ⟨v85, v86, x_v85, x_v86, h_v85, h_v86, hn_v85, hn_v86⟩ using hinv16 else hinv16 hG in EoCases.__eo_prog_str_replace_all_find.case_0
  pat_unapply h_v85 as ⟨v88, v89, x_v88, x_v89, h_v88, h_v89, hn_v88, hn_v89⟩ using hinv16 else hinv16 hG in EoCases.__eo_prog_str_replace_all_find.case_0
  step as ⟨e_v90, he_v90⟩
  store_step with CtorSpec.eo__3d.construct s16 e_v90 (by rw [he_v90]; exact empty_args) hinv16 h64 as ⟨v90, s17, hinv17, h_v90⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v86 h_v88 h_v89 dropping h_a8 h_v73 h_v81 h_v83 h_v85 he_v90 hinv16 e_v90 s16 v73 v81 v83 v85
  pat_same v88 v90 with h_v88 h_v90 using hinv17 else hinv17 hG in EoCases.__eo_prog_str_replace_all_find.case_0
  pat_same v89 a4 with h_v89 h_a4 using hinv17 else hinv17 hG in EoCases.__eo_prog_str_replace_all_find.case_0
  pat_unapply h_v86 as ⟨v92, v93, x_v92, x_v93, h_v92, h_v93, hn_v92, hn_v93⟩ using hinv17 else hinv17 hG in EoCases.__eo_prog_str_replace_all_find.case_0
  pat_unapply h_v92 as ⟨v95, v96, x_v95, x_v96, h_v95, h_v96, hn_v95, hn_v96⟩ using hinv17 else hinv17 hG in EoCases.__eo_prog_str_replace_all_find.case_0
  pat_unapply h_v95 as ⟨v98, v99, x_v98, x_v99, h_v98, h_v99, hn_v98, hn_v99⟩ using hinv17 else hinv17 hG in EoCases.__eo_prog_str_replace_all_find.case_0
  step as ⟨e_v100, he_v100⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s17 e_v100 (by rw [he_v100]; exact empty_args) hinv17 h64 as ⟨v100, s18, hinv18, h_v100⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v93 h_v96 h_v98 h_v99 dropping h_v86 h_v88 h_v89 h_v90 h_v92 h_v95 he_v100 hinv17 e_v100 s17 v86 v88 v89 v90 v92 v95
  pat_same v98 v100 with h_v98 h_v100 using hinv18 else hinv18 hG in EoCases.__eo_prog_str_replace_all_find.case_0
  pat_same v99 a0 with h_v99 h_a0 using hinv18 else hinv18 hG in EoCases.__eo_prog_str_replace_all_find.case_0
  pat_unapply h_v96 as ⟨v102, v103, x_v102, x_v103, h_v102, h_v103, hn_v102, hn_v103⟩ using hinv18 else hinv18 hG in EoCases.__eo_prog_str_replace_all_find.case_0
  pat_unapply h_v102 as ⟨v105, v106, x_v105, x_v106, h_v105, h_v106, hn_v105, hn_v106⟩ using hinv18 else hinv18 hG in EoCases.__eo_prog_str_replace_all_find.case_0
  step as ⟨e_v107, he_v107⟩
  store_step with CtorSpec.eo__2b.construct s18 e_v107 (by rw [he_v107]; exact empty_args) hinv18 h64 as ⟨v107, s19, hinv19, h_v107⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v93 h_v103 h_v105 h_v106 dropping h_v100 h_v102 h_v96 h_v98 h_v99 he_v107 hinv18 e_v107 s18 v100 v102 v96 v98 v99
  pat_same v105 v107 with h_v105 h_v107 using hinv19 else hinv19 hG in EoCases.__eo_prog_str_replace_all_find.case_0
  pat_unapply h_v106 as ⟨v109, v110, x_v109, x_v110, h_v109, h_v110, hn_v109, hn_v110⟩ using hinv19 else hinv19 hG in EoCases.__eo_prog_str_replace_all_find.case_0
  pat_unapply h_v109 as ⟨v112, v113, x_v112, x_v113, h_v112, h_v113, hn_v112, hn_v113⟩ using hinv19 else hinv19 hG in EoCases.__eo_prog_str_replace_all_find.case_0
  pat_unapply h_v112 as ⟨v115, v116, x_v115, x_v116, h_v115, h_v116, hn_v115, hn_v116⟩ using hinv19 else hinv19 hG in EoCases.__eo_prog_str_replace_all_find.case_0
  step as ⟨e_v117, he_v117⟩
  store_step with CtorSpec.eo_str_2eindexof.construct s19 e_v117 (by rw [he_v117]; exact empty_args) hinv19 h64 as ⟨v117, s20, hinv20, h_v117⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v93 h_v103 h_v110 h_v113 h_v115 h_v116 dropping h_v105 h_v106 h_v107 h_v109 h_v112 he_v117 hinv19 e_v117 s19 v105 v106 v107 v109 v112
  pat_same v115 v117 with h_v115 h_v117 using hinv20 else hinv20 hG in EoCases.__eo_prog_str_replace_all_find.case_0
  pat_same v116 a0 with h_v116 h_a0 using hinv20 else hinv20 hG in EoCases.__eo_prog_str_replace_all_find.case_0
  pat_same v113 a1 with h_v113 h_a1 using hinv20 else hinv20 hG in EoCases.__eo_prog_str_replace_all_find.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s20 0#u32 (0) (by scalar_tac) hinv20 h64 as ⟨v118, s21, hinv21, h_v118⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v93 h_v103 h_v110 dropping h_v113 h_v115 h_v116 h_v117 hinv20 s20 v113 v115 v116 v117
  pat_same v110 v118 with h_v110 h_v118 using hinv21 else hinv21 hG in EoCases.__eo_prog_str_replace_all_find.case_0
  pat_unapply h_v103 as ⟨v120, v121, x_v120, x_v121, h_v120, h_v121, hn_v120, hn_v121⟩ using hinv21 else hinv21 hG in EoCases.__eo_prog_str_replace_all_find.case_0
  pat_unapply h_v120 as ⟨v123, v124, x_v123, x_v124, h_v123, h_v124, hn_v123, hn_v124⟩ using hinv21 else hinv21 hG in EoCases.__eo_prog_str_replace_all_find.case_0
  step as ⟨e_v125, he_v125⟩
  store_step with CtorSpec.eo__2b.construct s21 e_v125 (by rw [he_v125]; exact empty_args) hinv21 h64 as ⟨v125, s22, hinv22, h_v125⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v93 h_v121 h_v123 h_v124 dropping h_v103 h_v110 h_v118 h_v120 he_v125 hinv21 e_v125 s21 v103 v110 v118 v120
  pat_same v123 v125 with h_v123 h_v125 using hinv22 else hinv22 hG in EoCases.__eo_prog_str_replace_all_find.case_0
  pat_unapply h_v124 as ⟨v127, v128, x_v127, x_v128, h_v127, h_v128, hn_v127, hn_v128⟩ using hinv22 else hinv22 hG in EoCases.__eo_prog_str_replace_all_find.case_0
  step as ⟨e_v129, he_v129⟩
  store_step with CtorSpec.eo_str_2elen.construct s22 e_v129 (by rw [he_v129]; exact empty_args) hinv22 h64 as ⟨v129, s23, hinv23, h_v129⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v93 h_v121 h_v127 h_v128 dropping h_v123 h_v124 h_v125 he_v129 hinv22 e_v129 s22 v123 v124 v125
  pat_same v127 v129 with h_v127 h_v129 using hinv23 else hinv23 hG in EoCases.__eo_prog_str_replace_all_find.case_0
  pat_same v128 a1 with h_v128 h_a1 using hinv23 else hinv23 hG in EoCases.__eo_prog_str_replace_all_find.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s23 0#u32 (0) (by scalar_tac) hinv23 h64 as ⟨v130, s24, hinv24, h_v130⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v93 h_v121 dropping h_v127 h_v128 h_v129 hinv23 s23 v127 v128 v129
  pat_same v121 v130 with h_v121 h_v130 using hinv24 else hinv24 hG in EoCases.__eo_prog_str_replace_all_find.case_0
  pat_unapply h_v93 as ⟨v132, v133, x_v132, x_v133, h_v132, h_v133, hn_v132, hn_v133⟩ using hinv24 else hinv24 hG in EoCases.__eo_prog_str_replace_all_find.case_0
  step as ⟨e_v134, he_v134⟩
  store_step with CtorSpec.eo_str_2elen.construct s24 e_v134 (by rw [he_v134]; exact empty_args) hinv24 h64 as ⟨v134, s25, hinv25, h_v134⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v132 h_v133 dropping h_v121 h_v130 h_v93 he_v134 hinv24 e_v134 s24 v121 v130 v93
  pat_same v132 v134 with h_v132 h_v134 using hinv25 else hinv25 hG in EoCases.__eo_prog_str_replace_all_find.case_0
  pat_same v133 a0 with h_v133 h_a0 using hinv25 else hinv25 hG in EoCases.__eo_prog_str_replace_all_find.case_0
  step as ⟨e_v135, he_v135⟩
  store_step with CtorSpec.eo__3d.construct s25 e_v135 (by rw [he_v135]; exact empty_args) hinv25 h64 as ⟨v135, s26, hinv26, h_v135⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 dropping h_v132 h_v133 h_v134 he_v135 hinv25 e_v135 s25 v132 v133 v134
  step as ⟨e_v136, he_v136⟩
  store_step with CtorSpec.eo_str_2ereplace_5fall.construct s26 e_v136 (by rw [he_v136]; exact empty_args) hinv26 h64 as ⟨v136, s27, hinv27, h_v136⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v135 dropping he_v136 hinv26 e_v136 s26
  store_step with Store.apply_rep s27 v136 a0 _ _ hinv27 h64 h_v136 h_a0 (by ns_tac) (by ns_tac) as ⟨v137, s28, hinv28, h_v137⟩ growing hG carrying h_a1 h_a2 h_a3 h_a4 h_v135 dropping h_a0 h_v136 hinv27 s27 v136
  store_step with Store.apply_rep s28 v137 a1 _ _ hinv28 h64 h_v137 h_a1 (by ns_tac) (by ns_tac) as ⟨v138, s29, hinv29, h_v138⟩ growing hG carrying h_a1 h_a2 h_a3 h_a4 h_v135 dropping h_v137 hinv28 s28 v137
  store_step with Store.apply_rep s29 v138 a2 _ _ hinv29 h64 h_v138 h_a2 (by ns_tac) (by ns_tac) as ⟨v139, s30, hinv30, h_v139⟩ growing hG carrying h_a1 h_a2 h_a3 h_a4 h_v135 dropping h_v138 hinv29 s29 v138
  store_step with Store.apply_rep s30 v135 v139 _ _ hinv30 h64 h_v135 h_v139 (by ns_tac) (by ns_tac) as ⟨v140, s31, hinv31, h_v140⟩ growing hG carrying h_a1 h_a2 h_a3 h_a4 dropping h_v135 h_v139 hinv30 s30 v135 v139
  step as ⟨e_v141, he_v141⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s31 e_v141 (by rw [he_v141]; exact empty_args) hinv31 h64 as ⟨v141, s32, hinv32, h_v141⟩ growing hG carrying h_a1 h_a2 h_a3 h_a4 h_v140 dropping he_v141 hinv31 e_v141 s31
  store_step with Store.apply_rep s32 v141 a3 _ _ hinv32 h64 h_v141 h_a3 (by ns_tac) (by ns_tac) as ⟨v142, s33, hinv33, h_v142⟩ growing hG carrying h_a1 h_a2 h_a3 h_a4 h_v140 dropping h_v141 hinv32 s32 v141
  step as ⟨e_v143, he_v143⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s33 e_v143 (by rw [he_v143]; exact empty_args) hinv33 h64 as ⟨v143, s34, hinv34, h_v143⟩ growing hG carrying h_a1 h_a2 h_a3 h_a4 h_v140 h_v142 dropping he_v143 hinv33 e_v143 s33
  store_step with Store.apply_rep s34 v143 a2 _ _ hinv34 h64 h_v143 h_a2 (by ns_tac) (by ns_tac) as ⟨v144, s35, hinv35, h_v144⟩ growing hG carrying h_a1 h_a2 h_a3 h_a4 h_v140 h_v142 dropping h_v143 hinv34 s34 v143
  step as ⟨e_v145, he_v145⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s35 e_v145 (by rw [he_v145]; exact empty_args) hinv35 h64 as ⟨v145, s36, hinv36, h_v145⟩ growing hG carrying h_a1 h_a2 h_a3 h_a4 h_v140 h_v142 h_v144 dropping he_v145 hinv35 e_v145 s35
  step as ⟨e_v146, he_v146⟩
  store_step with CtorSpec.eo_str_2ereplace_5fall.construct s36 e_v146 (by rw [he_v146]; exact empty_args) hinv36 h64 as ⟨v146, s37, hinv37, h_v146⟩ growing hG carrying h_a1 h_a2 h_a3 h_a4 h_v140 h_v142 h_v144 h_v145 dropping he_v146 hinv36 e_v146 s36
  store_step with Store.apply_rep s37 v146 a4 _ _ hinv37 h64 h_v146 h_a4 (by ns_tac) (by ns_tac) as ⟨v147, s38, hinv38, h_v147⟩ growing hG carrying h_a1 h_a2 h_a3 h_v140 h_v142 h_v144 h_v145 dropping h_a4 h_v146 hinv37 s37 v146
  store_step with Store.apply_rep s38 v147 a1 _ _ hinv38 h64 h_v147 h_a1 (by ns_tac) (by ns_tac) as ⟨v148, s39, hinv39, h_v148⟩ growing hG carrying h_a2 h_a3 h_v140 h_v142 h_v144 h_v145 dropping h_a1 h_v147 hinv38 s38 v147
  store_step with Store.apply_rep s39 v148 a2 _ _ hinv39 h64 h_v148 h_a2 (by ns_tac) (by ns_tac) as ⟨v149, s40, hinv40, h_v149⟩ growing hG carrying h_a3 h_v140 h_v142 h_v144 h_v145 dropping h_a2 h_v148 hinv39 s39 v148
  store_step with Store.apply_rep s40 v145 v149 _ _ hinv40 h64 h_v145 h_v149 (by ns_tac) (by ns_tac) as ⟨v150, s41, hinv41, h_v150⟩ growing hG carrying h_a3 h_v140 h_v142 h_v144 dropping h_v145 h_v149 hinv40 s40 v145 v149
  step as ⟨e_v151, he_v151⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s41 e_v151 (by rw [he_v151]; exact empty_args) hinv41 h64 as ⟨v151, s42, hinv42, h_v151⟩ growing hG carrying h_a3 h_v140 h_v142 h_v144 h_v150 dropping he_v151 hinv41 e_v151 s41
  store_step with ih.eo__24eo_5ftypeof s42 a3 _ hinv42 h64 (hG.rem hrem) h_a3 as ⟨v152, s43, hinv43, h_v152⟩ growing hG carrying h_v140 h_v142 h_v144 h_v150 h_v151 dropping h_a3 hinv42 s42
  store_step with ih.eo__24eo_5fnil s43 v151 v152 _ _ hinv43 h64 (hG.rem hrem) h_v151 h_v152 as ⟨v153, s44, hinv44, h_v153⟩ growing hG carrying h_v140 h_v142 h_v144 h_v150 dropping h_v151 h_v152 hinv43 s43 v151 v152
  store_step with Store.apply_mk_rep s44 v150 v153 _ _ hinv44 h64 h_v150 h_v153 as ⟨v154, s45, hinv45, h_v154⟩ growing hG carrying h_v140 h_v142 h_v144 dropping h_v150 h_v153 hinv44 s44 v150 v153
  store_step with Store.apply_mk_rep s45 v144 v154 _ _ hinv45 h64 h_v144 h_v154 as ⟨v155, s46, hinv46, h_v155⟩ growing hG carrying h_v140 h_v142 dropping h_v144 h_v154 hinv45 s45 v144 v154
  store_step with Store.apply_mk_rep s46 v142 v155 _ _ hinv46 h64 h_v142 h_v155 as ⟨v156, s47, hinv47, h_v156⟩ growing hG carrying h_v140 dropping h_v142 h_v155 hinv46 s46 v142 v155
  store_step with Store.apply_mk_rep s47 v140 v156 _ _ hinv47 h64 h_v140 h_v156 as ⟨v157, s48, hinv48, h_v157⟩ growing hG carrying dropping h_v140 h_v156 hinv47 s47 v140 v156
  case_done hinv48 hG with h_v157 in EoCases.__eo_prog_str_replace_all_find.case_0 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v13 hn_v14 hn_v17 hn_v18 hn_v20 hn_v21 hn_v23 hn_v24 hn_v32 hn_v33 hn_v35 hn_v36 hn_v39 hn_v40 hn_v42 hn_v43 hn_v46 hn_v47 hn_v54 hn_v55 hn_v57 hn_v58 hn_v61 hn_v62 hn_v64 hn_v65 hn_v67 hn_v68 hn_v72 hn_v73 hn_v75 hn_v76 hn_v78 hn_v79 hn_v85 hn_v86 hn_v88 hn_v89 hn_v92 hn_v93 hn_v95 hn_v96 hn_v98 hn_v99 hn_v102 hn_v103 hn_v105 hn_v106 hn_v109 hn_v110 hn_v112 hn_v113 hn_v115 hn_v116 hn_v120 hn_v121 hn_v123 hn_v124 hn_v127 hn_v128 hn_v132 hn_v133

set_option maxHeartbeats 20000000 in
/-- logos's `__eo_prog_str_replace_all_find` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstr_2dreplace_2dall_2dfind.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _) (x_a7 : _) (x_a8 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) (hw_a4 : Valid.valid x_a4) (hw_a5 : Valid.valid x_a5) (hw_a6 : Valid.valid x_a6) (hw_a7 : Valid.valid x_a7) (hw_a8 : Valid.valid x_a8) :
    __eo_prog_str_replace_all_find x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else if x_a4 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_str_replace_all_find.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_str_replace_all_find
  unfold EoCases.__eo_prog_str_replace_all_find.case_0
  logos_eq

set_option maxHeartbeats 20000000 in
theorem body_eo__24eo_5fprog_5fstr_2dreplace_2dall_2dfind_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 a6 a7 a8 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _) (x_a7 : _) (x_a8 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) (h_a6 : Represents.rep s a6 x_a6) (h_a7 : Represents.rep s a7 x_a7) (h_a8 : Represents.rep s a8 x_a8) :
    body_eo__24eo_5fprog_5fstr_2dreplace_2dall_2dfind s a0 a1 a2 a3 a4 a5 a6 a7 a8 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_replace_all_find x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstr_2dreplace_2dall_2dfind.rust_eq x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3) (by valid_tac hinv h_a4) (by valid_tac hinv h_a5) (by valid_tac hinv h_a6) (by valid_tac hinv h_a7) (by valid_tac hinv h_a8)]
  unfold body_eo__24eo_5fprog_5fstr_2dreplace_2dall_2dfind
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  stuck_check h_a3 : x_a3 as hn_a3 else hinv hG
  stuck_check h_a4 : x_a4 as hn_a4 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstr_2dreplace_2dall_2dfind_spec n ih s a0 a1 a2 a3 a4 a5 a6 a7 a8 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 hn_a0 hn_a1 hn_a2 hn_a3 hn_a4
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hc0 in EoCases.__eo_prog_str_replace_all_find.case_0

set_option maxHeartbeats 20000000 in
theorem eo__24eo_5fprog_5fstr_2dreplace_2dall_2dfind_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstr_2dreplace_2dall_2dfind.Spec n := by
  intro s a0 a1 a2 a3 a4 a5 a6 a7 a8 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8
  unfold eo__24eo_5fprog_5fstr_2dreplace_2dall_2dfind
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstr_2dreplace_2dall_2dfind s1 a0 a1 a2 a3 a4 a5 a6 a7 a8) (fun s' t => Represents.rep s' t (__eo_prog_str_replace_all_find x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstr_2dreplace_2dall_2dfind_spec m (ih m hm) s1 a0 a1 a2 a3 a4 a5 a6 a7 a8 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn) (by congr_one h_a4 hn) (by congr_one h_a5 hn) (by congr_one h_a6 hn) (by congr_one h_a7 hn) (by congr_one h_a8 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

end pathos_compiled_checker
