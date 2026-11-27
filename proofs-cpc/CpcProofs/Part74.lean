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
theorem case_0_eo__24eo_5fprog_5fstr_2dreplace_2dfind_2dfirst_2dconcat_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 a6 a7 a8 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _) (x_a7 : _) (x_a8 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) (h_a6 : Represents.rep s a6 x_a6) (h_a7 : Represents.rep s a7 x_a7) (h_a8 : Represents.rep s a8 x_a8) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) (hn_a4 : x_a4 ≠ Eo.Term.Stuck) (hn_a5 : x_a5 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstr_2dreplace_2dfind_2dfirst_2dconcat s a0 a1 a2 a3 a4 a5 a6 a7 a8 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_str_replace_find_first_concat.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_str_replace_find_first_concat.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstr_2dreplace_2dfind_2dfirst_2dconcat
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a6 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_str_replace_find_first_concat.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_str_replace_find_first_concat.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_str_replace_find_first_concat.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a7 h_a8 h_v4 h_v6 h_v7 dropping h_a6 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_str_replace_find_first_concat.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_str_replace_find_first_concat.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_str_replace_find_first_concat.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__3e_3d.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a7 h_a8 h_v4 h_v11 h_v13 h_v14 dropping h_v10 h_v6 h_v7 h_v8 he_v15 hinv1 e_v15 s1 v10 v6 v7 v8
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_replace_find_first_concat.case_0
  pat_unapply h_v14 as ⟨v17, v18, x_v17, x_v18, h_v17, h_v18, hn_v17, hn_v18⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_str_replace_find_first_concat.case_0
  pat_unapply h_v17 as ⟨v20, v21, x_v20, x_v21, h_v20, h_v21, hn_v20, hn_v21⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_str_replace_find_first_concat.case_0
  pat_unapply h_v20 as ⟨v23, v24, x_v23, x_v24, h_v23, h_v24, hn_v23, hn_v24⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_str_replace_find_first_concat.case_0
  step as ⟨e_v25, he_v25⟩
  store_step with CtorSpec.eo_str_2eindexof.construct s2 e_v25 (by rw [he_v25]; exact empty_args) hinv2 h64 as ⟨v25, s3, hinv3, h_v25⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a7 h_a8 h_v4 h_v11 h_v18 h_v21 h_v23 h_v24 dropping h_v13 h_v14 h_v15 h_v17 h_v20 he_v25 hinv2 e_v25 s2 v13 v14 v15 v17 v20
  pat_same v23 v25 with h_v23 h_v25 using hinv3 else hinv3 hG in EoCases.__eo_prog_str_replace_find_first_concat.case_0
  pat_same v24 a0 with h_v24 h_a0 using hinv3 else hinv3 hG in EoCases.__eo_prog_str_replace_find_first_concat.case_0
  pat_same v21 a2 with h_v21 h_a2 using hinv3 else hinv3 hG in EoCases.__eo_prog_str_replace_find_first_concat.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s3 0#u32 (0) (by scalar_tac) hinv3 h64 as ⟨v26, s4, hinv4, h_v26⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a7 h_a8 h_v4 h_v11 h_v18 dropping h_v21 h_v23 h_v24 h_v25 hinv3 s3 v21 v23 v24 v25
  pat_same v18 v26 with h_v18 h_v26 using hinv4 else hinv4 hG in EoCases.__eo_prog_str_replace_find_first_concat.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s4 0#u32 (0) (by scalar_tac) hinv4 h64 as ⟨v27, s5, hinv5, h_v27⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a7 h_a8 h_v4 h_v11 dropping h_v18 h_v26 hinv4 s4 v18 v26
  pat_same v11 v27 with h_v11 h_v27 using hinv5 else hinv5 hG in EoCases.__eo_prog_str_replace_find_first_concat.case_0
  store_step with Store.literal_boolean_spec s5 true hinv5 h64 as ⟨v28, s6, hinv6, h_v28⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a7 h_a8 h_v4 dropping h_v11 h_v27 hinv5 s5 v11 v27
  pat_same v4 v28 with h_v4 h_v28 using hinv6 else hinv6 hG in EoCases.__eo_prog_str_replace_find_first_concat.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a7 as ⟨v30, x_v30, h_v30⟩ else hinv6 hG in EoCases.__eo_prog_str_replace_find_first_concat.case_0
  pat_unapply h_v30 as ⟨v32, v33, x_v32, x_v33, h_v32, h_v33, hn_v32, hn_v33⟩ using hinv6 else hinv6 hG in EoCases.__eo_prog_str_replace_find_first_concat.case_0
  pat_unapply h_v32 as ⟨v35, v36, x_v35, x_v36, h_v35, h_v36, hn_v35, hn_v36⟩ using hinv6 else hinv6 hG in EoCases.__eo_prog_str_replace_find_first_concat.case_0
  step as ⟨e_v37, he_v37⟩
  store_step with CtorSpec.eo__3d.construct s6 e_v37 (by rw [he_v37]; exact empty_args) hinv6 h64 as ⟨v37, s7, hinv7, h_v37⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a8 h_v33 h_v35 h_v36 dropping h_a7 h_v28 h_v30 h_v32 h_v4 he_v37 hinv6 e_v37 s6 v28 v30 v32 v4
  pat_same v35 v37 with h_v35 h_v37 using hinv7 else hinv7 hG in EoCases.__eo_prog_str_replace_find_first_concat.case_0
  pat_same v36 a4 with h_v36 h_a4 using hinv7 else hinv7 hG in EoCases.__eo_prog_str_replace_find_first_concat.case_0
  pat_unapply h_v33 as ⟨v39, v40, x_v39, x_v40, h_v39, h_v40, hn_v39, hn_v40⟩ using hinv7 else hinv7 hG in EoCases.__eo_prog_str_replace_find_first_concat.case_0
  pat_unapply h_v39 as ⟨v42, v43, x_v42, x_v43, h_v42, h_v43, hn_v42, hn_v43⟩ using hinv7 else hinv7 hG in EoCases.__eo_prog_str_replace_find_first_concat.case_0
  pat_unapply h_v42 as ⟨v45, v46, x_v45, x_v46, h_v45, h_v46, hn_v45, hn_v46⟩ using hinv7 else hinv7 hG in EoCases.__eo_prog_str_replace_find_first_concat.case_0
  step as ⟨e_v47, he_v47⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s7 e_v47 (by rw [he_v47]; exact empty_args) hinv7 h64 as ⟨v47, s8, hinv8, h_v47⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a8 h_v40 h_v43 h_v45 h_v46 dropping h_v33 h_v35 h_v36 h_v37 h_v39 h_v42 he_v47 hinv7 e_v47 s7 v33 v35 v36 v37 v39 v42
  pat_same v45 v47 with h_v45 h_v47 using hinv8 else hinv8 hG in EoCases.__eo_prog_str_replace_find_first_concat.case_0
  pat_same v46 a0 with h_v46 h_a0 using hinv8 else hinv8 hG in EoCases.__eo_prog_str_replace_find_first_concat.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s8 0#u32 (0) (by scalar_tac) hinv8 h64 as ⟨v48, s9, hinv9, h_v48⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a8 h_v40 h_v43 dropping h_v45 h_v46 h_v47 hinv8 s8 v45 v46 v47
  pat_same v43 v48 with h_v43 h_v48 using hinv9 else hinv9 hG in EoCases.__eo_prog_str_replace_find_first_concat.case_0
  pat_unapply h_v40 as ⟨v50, v51, x_v50, x_v51, h_v50, h_v51, hn_v50, hn_v51⟩ using hinv9 else hinv9 hG in EoCases.__eo_prog_str_replace_find_first_concat.case_0
  pat_unapply h_v50 as ⟨v53, v54, x_v53, x_v54, h_v53, h_v54, hn_v53, hn_v54⟩ using hinv9 else hinv9 hG in EoCases.__eo_prog_str_replace_find_first_concat.case_0
  pat_unapply h_v53 as ⟨v56, v57, x_v56, x_v57, h_v56, h_v57, hn_v56, hn_v57⟩ using hinv9 else hinv9 hG in EoCases.__eo_prog_str_replace_find_first_concat.case_0
  step as ⟨e_v58, he_v58⟩
  store_step with CtorSpec.eo_str_2eindexof.construct s9 e_v58 (by rw [he_v58]; exact empty_args) hinv9 h64 as ⟨v58, s10, hinv10, h_v58⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a8 h_v51 h_v54 h_v56 h_v57 dropping h_v40 h_v43 h_v48 h_v50 h_v53 he_v58 hinv9 e_v58 s9 v40 v43 v48 v50 v53
  pat_same v56 v58 with h_v56 h_v58 using hinv10 else hinv10 hG in EoCases.__eo_prog_str_replace_find_first_concat.case_0
  pat_same v57 a0 with h_v57 h_a0 using hinv10 else hinv10 hG in EoCases.__eo_prog_str_replace_find_first_concat.case_0
  pat_same v54 a2 with h_v54 h_a2 using hinv10 else hinv10 hG in EoCases.__eo_prog_str_replace_find_first_concat.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s10 0#u32 (0) (by scalar_tac) hinv10 h64 as ⟨v59, s11, hinv11, h_v59⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a8 h_v51 dropping h_v54 h_v56 h_v57 h_v58 hinv10 s10 v54 v56 v57 v58
  pat_same v51 v59 with h_v51 h_v59 using hinv11 else hinv11 hG in EoCases.__eo_prog_str_replace_find_first_concat.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a8 as ⟨v61, x_v61, h_v61⟩ else hinv11 hG in EoCases.__eo_prog_str_replace_find_first_concat.case_0
  pat_unapply h_v61 as ⟨v63, v64, x_v63, x_v64, h_v63, h_v64, hn_v63, hn_v64⟩ using hinv11 else hinv11 hG in EoCases.__eo_prog_str_replace_find_first_concat.case_0
  pat_unapply h_v63 as ⟨v66, v67, x_v66, x_v67, h_v66, h_v67, hn_v66, hn_v67⟩ using hinv11 else hinv11 hG in EoCases.__eo_prog_str_replace_find_first_concat.case_0
  step as ⟨e_v68, he_v68⟩
  store_step with CtorSpec.eo__3d.construct s11 e_v68 (by rw [he_v68]; exact empty_args) hinv11 h64 as ⟨v68, s12, hinv12, h_v68⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v64 h_v66 h_v67 dropping h_a8 h_v51 h_v59 h_v61 h_v63 he_v68 hinv11 e_v68 s11 v51 v59 v61 v63
  pat_same v66 v68 with h_v66 h_v68 using hinv12 else hinv12 hG in EoCases.__eo_prog_str_replace_find_first_concat.case_0
  pat_same v67 a5 with h_v67 h_a5 using hinv12 else hinv12 hG in EoCases.__eo_prog_str_replace_find_first_concat.case_0
  pat_unapply h_v64 as ⟨v70, v71, x_v70, x_v71, h_v70, h_v71, hn_v70, hn_v71⟩ using hinv12 else hinv12 hG in EoCases.__eo_prog_str_replace_find_first_concat.case_0
  pat_unapply h_v70 as ⟨v73, v74, x_v73, x_v74, h_v73, h_v74, hn_v73, hn_v74⟩ using hinv12 else hinv12 hG in EoCases.__eo_prog_str_replace_find_first_concat.case_0
  pat_unapply h_v73 as ⟨v76, v77, x_v76, x_v77, h_v76, h_v77, hn_v76, hn_v77⟩ using hinv12 else hinv12 hG in EoCases.__eo_prog_str_replace_find_first_concat.case_0
  step as ⟨e_v78, he_v78⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s12 e_v78 (by rw [he_v78]; exact empty_args) hinv12 h64 as ⟨v78, s13, hinv13, h_v78⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v71 h_v74 h_v76 h_v77 dropping h_v64 h_v66 h_v67 h_v68 h_v70 h_v73 he_v78 hinv12 e_v78 s12 v64 v66 v67 v68 v70 v73
  pat_same v76 v78 with h_v76 h_v78 using hinv13 else hinv13 hG in EoCases.__eo_prog_str_replace_find_first_concat.case_0
  pat_same v77 a0 with h_v77 h_a0 using hinv13 else hinv13 hG in EoCases.__eo_prog_str_replace_find_first_concat.case_0
  pat_unapply h_v74 as ⟨v80, v81, x_v80, x_v81, h_v80, h_v81, hn_v80, hn_v81⟩ using hinv13 else hinv13 hG in EoCases.__eo_prog_str_replace_find_first_concat.case_0
  pat_unapply h_v80 as ⟨v83, v84, x_v83, x_v84, h_v83, h_v84, hn_v83, hn_v84⟩ using hinv13 else hinv13 hG in EoCases.__eo_prog_str_replace_find_first_concat.case_0
  step as ⟨e_v85, he_v85⟩
  store_step with CtorSpec.eo__2b.construct s13 e_v85 (by rw [he_v85]; exact empty_args) hinv13 h64 as ⟨v85, s14, hinv14, h_v85⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v71 h_v81 h_v83 h_v84 dropping h_v74 h_v76 h_v77 h_v78 h_v80 he_v85 hinv13 e_v85 s13 v74 v76 v77 v78 v80
  pat_same v83 v85 with h_v83 h_v85 using hinv14 else hinv14 hG in EoCases.__eo_prog_str_replace_find_first_concat.case_0
  pat_unapply h_v84 as ⟨v87, v88, x_v87, x_v88, h_v87, h_v88, hn_v87, hn_v88⟩ using hinv14 else hinv14 hG in EoCases.__eo_prog_str_replace_find_first_concat.case_0
  pat_unapply h_v87 as ⟨v90, v91, x_v90, x_v91, h_v90, h_v91, hn_v90, hn_v91⟩ using hinv14 else hinv14 hG in EoCases.__eo_prog_str_replace_find_first_concat.case_0
  pat_unapply h_v90 as ⟨v93, v94, x_v93, x_v94, h_v93, h_v94, hn_v93, hn_v94⟩ using hinv14 else hinv14 hG in EoCases.__eo_prog_str_replace_find_first_concat.case_0
  step as ⟨e_v95, he_v95⟩
  store_step with CtorSpec.eo_str_2eindexof.construct s14 e_v95 (by rw [he_v95]; exact empty_args) hinv14 h64 as ⟨v95, s15, hinv15, h_v95⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v71 h_v81 h_v88 h_v91 h_v93 h_v94 dropping h_v83 h_v84 h_v85 h_v87 h_v90 he_v95 hinv14 e_v95 s14 v83 v84 v85 v87 v90
  pat_same v93 v95 with h_v93 h_v95 using hinv15 else hinv15 hG in EoCases.__eo_prog_str_replace_find_first_concat.case_0
  pat_same v94 a0 with h_v94 h_a0 using hinv15 else hinv15 hG in EoCases.__eo_prog_str_replace_find_first_concat.case_0
  pat_same v91 a2 with h_v91 h_a2 using hinv15 else hinv15 hG in EoCases.__eo_prog_str_replace_find_first_concat.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s15 0#u32 (0) (by scalar_tac) hinv15 h64 as ⟨v96, s16, hinv16, h_v96⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v71 h_v81 h_v88 dropping h_v91 h_v93 h_v94 h_v95 hinv15 s15 v91 v93 v94 v95
  pat_same v88 v96 with h_v88 h_v96 using hinv16 else hinv16 hG in EoCases.__eo_prog_str_replace_find_first_concat.case_0
  pat_unapply h_v81 as ⟨v98, v99, x_v98, x_v99, h_v98, h_v99, hn_v98, hn_v99⟩ using hinv16 else hinv16 hG in EoCases.__eo_prog_str_replace_find_first_concat.case_0
  pat_unapply h_v98 as ⟨v101, v102, x_v101, x_v102, h_v101, h_v102, hn_v101, hn_v102⟩ using hinv16 else hinv16 hG in EoCases.__eo_prog_str_replace_find_first_concat.case_0
  step as ⟨e_v103, he_v103⟩
  store_step with CtorSpec.eo__2b.construct s16 e_v103 (by rw [he_v103]; exact empty_args) hinv16 h64 as ⟨v103, s17, hinv17, h_v103⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v71 h_v99 h_v101 h_v102 dropping h_v81 h_v88 h_v96 h_v98 he_v103 hinv16 e_v103 s16 v81 v88 v96 v98
  pat_same v101 v103 with h_v101 h_v103 using hinv17 else hinv17 hG in EoCases.__eo_prog_str_replace_find_first_concat.case_0
  pat_unapply h_v102 as ⟨v105, v106, x_v105, x_v106, h_v105, h_v106, hn_v105, hn_v106⟩ using hinv17 else hinv17 hG in EoCases.__eo_prog_str_replace_find_first_concat.case_0
  step as ⟨e_v107, he_v107⟩
  store_step with CtorSpec.eo_str_2elen.construct s17 e_v107 (by rw [he_v107]; exact empty_args) hinv17 h64 as ⟨v107, s18, hinv18, h_v107⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v71 h_v99 h_v105 h_v106 dropping h_v101 h_v102 h_v103 he_v107 hinv17 e_v107 s17 v101 v102 v103
  pat_same v105 v107 with h_v105 h_v107 using hinv18 else hinv18 hG in EoCases.__eo_prog_str_replace_find_first_concat.case_0
  pat_same v106 a2 with h_v106 h_a2 using hinv18 else hinv18 hG in EoCases.__eo_prog_str_replace_find_first_concat.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s18 0#u32 (0) (by scalar_tac) hinv18 h64 as ⟨v108, s19, hinv19, h_v108⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v71 h_v99 dropping h_v105 h_v106 h_v107 hinv18 s18 v105 v106 v107
  pat_same v99 v108 with h_v99 h_v108 using hinv19 else hinv19 hG in EoCases.__eo_prog_str_replace_find_first_concat.case_0
  pat_unapply h_v71 as ⟨v110, v111, x_v110, x_v111, h_v110, h_v111, hn_v110, hn_v111⟩ using hinv19 else hinv19 hG in EoCases.__eo_prog_str_replace_find_first_concat.case_0
  step as ⟨e_v112, he_v112⟩
  store_step with CtorSpec.eo_str_2elen.construct s19 e_v112 (by rw [he_v112]; exact empty_args) hinv19 h64 as ⟨v112, s20, hinv20, h_v112⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v110 h_v111 dropping h_v108 h_v71 h_v99 he_v112 hinv19 e_v112 s19 v108 v71 v99
  pat_same v110 v112 with h_v110 h_v112 using hinv20 else hinv20 hG in EoCases.__eo_prog_str_replace_find_first_concat.case_0
  pat_same v111 a0 with h_v111 h_a0 using hinv20 else hinv20 hG in EoCases.__eo_prog_str_replace_find_first_concat.case_0
  step as ⟨e_v113, he_v113⟩
  store_step with CtorSpec.eo__3d.construct s20 e_v113 (by rw [he_v113]; exact empty_args) hinv20 h64 as ⟨v113, s21, hinv21, h_v113⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 dropping h_v110 h_v111 h_v112 he_v113 hinv20 e_v113 s20 v110 v111 v112
  step as ⟨e_v114, he_v114⟩
  store_step with CtorSpec.eo_str_2ereplace.construct s21 e_v114 (by rw [he_v114]; exact empty_args) hinv21 h64 as ⟨v114, s22, hinv22, h_v114⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v113 dropping he_v114 hinv21 e_v114 s21
  step as ⟨e_v115, he_v115⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s22 e_v115 (by rw [he_v115]; exact empty_args) hinv22 h64 as ⟨v115, s23, hinv23, h_v115⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v113 h_v114 dropping he_v115 hinv22 e_v115 s22
  store_step with Store.apply_rep s23 v115 a0 _ _ hinv23 h64 h_v115 h_a0 (by ns_tac) (by ns_tac) as ⟨v116, s24, hinv24, h_v116⟩ growing hG carrying h_a1 h_a2 h_a3 h_a4 h_a5 h_v113 h_v114 dropping h_a0 h_v115 hinv23 s23 v115
  store_step with Store.apply_rep s24 v116 a1 _ _ hinv24 h64 h_v116 h_a1 (by ns_tac) (by ns_tac) as ⟨v117, s25, hinv25, h_v117⟩ growing hG carrying h_a1 h_a2 h_a3 h_a4 h_a5 h_v113 h_v114 dropping h_v116 hinv24 s24 v116
  store_step with Store.apply_rep s25 v114 v117 _ _ hinv25 h64 h_v114 h_v117 (by ns_tac) (by ns_tac) as ⟨v118, s26, hinv26, h_v118⟩ growing hG carrying h_a1 h_a2 h_a3 h_a4 h_a5 h_v113 dropping h_v114 h_v117 hinv25 s25 v114 v117
  store_step with Store.apply_rep s26 v118 a2 _ _ hinv26 h64 h_v118 h_a2 (by ns_tac) (by ns_tac) as ⟨v119, s27, hinv27, h_v119⟩ growing hG carrying h_a1 h_a3 h_a4 h_a5 h_v113 dropping h_a2 h_v118 hinv26 s26 v118
  store_step with Store.apply_rep s27 v119 a3 _ _ hinv27 h64 h_v119 h_a3 (by ns_tac) (by ns_tac) as ⟨v120, s28, hinv28, h_v120⟩ growing hG carrying h_a1 h_a3 h_a4 h_a5 h_v113 dropping h_v119 hinv27 s27 v119
  store_step with Store.apply_rep s28 v113 v120 _ _ hinv28 h64 h_v113 h_v120 (by ns_tac) (by ns_tac) as ⟨v121, s29, hinv29, h_v121⟩ growing hG carrying h_a1 h_a3 h_a4 h_a5 dropping h_v113 h_v120 hinv28 s28 v113 v120
  step as ⟨e_v122, he_v122⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s29 e_v122 (by rw [he_v122]; exact empty_args) hinv29 h64 as ⟨v122, s30, hinv30, h_v122⟩ growing hG carrying h_a1 h_a3 h_a4 h_a5 h_v121 dropping he_v122 hinv29 e_v122 s29
  store_step with Store.apply_rep s30 v122 a4 _ _ hinv30 h64 h_v122 h_a4 (by ns_tac) (by ns_tac) as ⟨v123, s31, hinv31, h_v123⟩ growing hG carrying h_a1 h_a3 h_a5 h_v121 dropping h_a4 h_v122 hinv30 s30 v122
  step as ⟨e_v124, he_v124⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s31 e_v124 (by rw [he_v124]; exact empty_args) hinv31 h64 as ⟨v124, s32, hinv32, h_v124⟩ growing hG carrying h_a1 h_a3 h_a5 h_v121 h_v123 dropping he_v124 hinv31 e_v124 s31
  store_step with Store.apply_rep s32 v124 a3 _ _ hinv32 h64 h_v124 h_a3 (by ns_tac) (by ns_tac) as ⟨v125, s33, hinv33, h_v125⟩ growing hG carrying h_a1 h_a5 h_v121 h_v123 dropping h_a3 h_v124 hinv32 s32 v124
  step as ⟨e_v126, he_v126⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s33 e_v126 (by rw [he_v126]; exact empty_args) hinv33 h64 as ⟨v126, s34, hinv34, h_v126⟩ growing hG carrying h_a1 h_a5 h_v121 h_v123 h_v125 dropping he_v126 hinv33 e_v126 s33
  store_step with Store.apply_rep s34 v126 a5 _ _ hinv34 h64 h_v126 h_a5 (by ns_tac) (by ns_tac) as ⟨v127, s35, hinv35, h_v127⟩ growing hG carrying h_a1 h_v121 h_v123 h_v125 dropping h_a5 h_v126 hinv34 s34 v126
  store_step with Store.apply_rep s35 v127 a1 _ _ hinv35 h64 h_v127 h_a1 (by ns_tac) (by ns_tac) as ⟨v128, s36, hinv36, h_v128⟩ growing hG carrying h_v121 h_v123 h_v125 dropping h_a1 h_v127 hinv35 s35 v127
  store_step with Store.apply_rep s36 v125 v128 _ _ hinv36 h64 h_v125 h_v128 (by ns_tac) (by ns_tac) as ⟨v129, s37, hinv37, h_v129⟩ growing hG carrying h_v121 h_v123 dropping h_v125 h_v128 hinv36 s36 v125 v128
  store_step with Store.apply_rep s37 v123 v129 _ _ hinv37 h64 h_v123 h_v129 (by ns_tac) (by ns_tac) as ⟨v130, s38, hinv38, h_v130⟩ growing hG carrying h_v121 dropping h_v123 h_v129 hinv37 s37 v123 v129
  store_step with Store.apply_rep s38 v121 v130 _ _ hinv38 h64 h_v121 h_v130 (by ns_tac) (by ns_tac) as ⟨v131, s39, hinv39, h_v131⟩ growing hG carrying dropping h_v121 h_v130 hinv38 s38 v121 v130
  case_done hinv39 hG with h_v131 in EoCases.__eo_prog_str_replace_find_first_concat.case_0 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_a5 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v13 hn_v14 hn_v17 hn_v18 hn_v20 hn_v21 hn_v23 hn_v24 hn_v32 hn_v33 hn_v35 hn_v36 hn_v39 hn_v40 hn_v42 hn_v43 hn_v45 hn_v46 hn_v50 hn_v51 hn_v53 hn_v54 hn_v56 hn_v57 hn_v63 hn_v64 hn_v66 hn_v67 hn_v70 hn_v71 hn_v73 hn_v74 hn_v76 hn_v77 hn_v80 hn_v81 hn_v83 hn_v84 hn_v87 hn_v88 hn_v90 hn_v91 hn_v93 hn_v94 hn_v98 hn_v99 hn_v101 hn_v102 hn_v105 hn_v106 hn_v110 hn_v111

set_option maxHeartbeats 20000000 in
/-- logos's `__eo_prog_str_replace_find_first_concat` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstr_2dreplace_2dfind_2dfirst_2dconcat.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _) (x_a7 : _) (x_a8 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) (hw_a4 : Valid.valid x_a4) (hw_a5 : Valid.valid x_a5) (hw_a6 : Valid.valid x_a6) (hw_a7 : Valid.valid x_a7) (hw_a8 : Valid.valid x_a8) :
    __eo_prog_str_replace_find_first_concat x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else if x_a4 = Eo.Term.Stuck then HasStuck.stuck else if x_a5 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_str_replace_find_first_concat.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_str_replace_find_first_concat
  unfold EoCases.__eo_prog_str_replace_find_first_concat.case_0
  logos_eq

set_option maxHeartbeats 20000000 in
theorem body_eo__24eo_5fprog_5fstr_2dreplace_2dfind_2dfirst_2dconcat_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 a6 a7 a8 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _) (x_a7 : _) (x_a8 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) (h_a6 : Represents.rep s a6 x_a6) (h_a7 : Represents.rep s a7 x_a7) (h_a8 : Represents.rep s a8 x_a8) :
    body_eo__24eo_5fprog_5fstr_2dreplace_2dfind_2dfirst_2dconcat s a0 a1 a2 a3 a4 a5 a6 a7 a8 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_replace_find_first_concat x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstr_2dreplace_2dfind_2dfirst_2dconcat.rust_eq x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3) (by valid_tac hinv h_a4) (by valid_tac hinv h_a5) (by valid_tac hinv h_a6) (by valid_tac hinv h_a7) (by valid_tac hinv h_a8)]
  unfold body_eo__24eo_5fprog_5fstr_2dreplace_2dfind_2dfirst_2dconcat
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  stuck_check h_a3 : x_a3 as hn_a3 else hinv hG
  stuck_check h_a4 : x_a4 as hn_a4 else hinv hG
  stuck_check h_a5 : x_a5 as hn_a5 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstr_2dreplace_2dfind_2dfirst_2dconcat_spec n ih s a0 a1 a2 a3 a4 a5 a6 a7 a8 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_a5
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_a5
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_a5 hc0 in EoCases.__eo_prog_str_replace_find_first_concat.case_0

set_option maxHeartbeats 20000000 in
theorem eo__24eo_5fprog_5fstr_2dreplace_2dfind_2dfirst_2dconcat_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstr_2dreplace_2dfind_2dfirst_2dconcat.Spec n := by
  intro s a0 a1 a2 a3 a4 a5 a6 a7 a8 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8
  unfold eo__24eo_5fprog_5fstr_2dreplace_2dfind_2dfirst_2dconcat
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstr_2dreplace_2dfind_2dfirst_2dconcat s1 a0 a1 a2 a3 a4 a5 a6 a7 a8) (fun s' t => Represents.rep s' t (__eo_prog_str_replace_find_first_concat x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstr_2dreplace_2dfind_2dfirst_2dconcat_spec m (ih m hm) s1 a0 a1 a2 a3 a4 a5 a6 a7 a8 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn) (by congr_one h_a4 hn) (by congr_one h_a5 hn) (by congr_one h_a6 hn) (by congr_one h_a7 hn) (by congr_one h_a8 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

end pathos_compiled_checker
