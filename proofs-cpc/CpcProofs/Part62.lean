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
theorem case_0_eo__24eo_5fprog_5fstr_2dupdate_2din_2dfirst_2dconcat_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _) (x_a7 : _) (x_a8 : _) (x_a9 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) (h_a6 : Represents.rep s a6 x_a6) (h_a7 : Represents.rep s a7 x_a7) (h_a8 : Represents.rep s a8 x_a8) (h_a9 : Represents.rep s a9 x_a9) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) (hn_a4 : x_a4 ≠ Eo.Term.Stuck) (hn_a5 : x_a5 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstr_2dupdate_2din_2dfirst_2dconcat s a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_str_update_in_first_concat.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 x_a9 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_str_update_in_first_concat.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 x_a9 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstr_2dupdate_2din_2dfirst_2dconcat more_0_eo__24eo_5fprog_5fstr_2dupdate_2din_2dfirst_2dconcat more_1_eo__24eo_5fprog_5fstr_2dupdate_2din_2dfirst_2dconcat more_2_eo__24eo_5fprog_5fstr_2dupdate_2din_2dfirst_2dconcat more_3_eo__24eo_5fprog_5fstr_2dupdate_2din_2dfirst_2dconcat more_4_eo__24eo_5fprog_5fstr_2dupdate_2din_2dfirst_2dconcat more_5_eo__24eo_5fprog_5fstr_2dupdate_2din_2dfirst_2dconcat more_6_eo__24eo_5fprog_5fstr_2dupdate_2din_2dfirst_2dconcat more_7_eo__24eo_5fprog_5fstr_2dupdate_2din_2dfirst_2dconcat more_8_eo__24eo_5fprog_5fstr_2dupdate_2din_2dfirst_2dconcat
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a6 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_str_update_in_first_concat.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_str_update_in_first_concat.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_str_update_in_first_concat.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 h_a9 h_v1 h_v3 h_v4 h_v6 h_v7
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_str_update_in_first_concat.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_str_update_in_first_concat.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_str_update_in_first_concat.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__3e_3d.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 h_a9 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_update_in_first_concat.case_0
  pat_same v14 a3 with h_v14 h_a3 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_update_in_first_concat.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s2 0#u32 (0) (by scalar_tac) hinv2 h64 as ⟨v16, s3, hinv3, h_v16⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 h_a9 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15
  pat_same v11 v16 with h_v11 h_v16 using hinv3 else hinv3 hG in EoCases.__eo_prog_str_update_in_first_concat.case_0
  store_step with Store.literal_boolean_spec s3 true hinv3 h64 as ⟨v17, s4, hinv4, h_v17⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 h_a9 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16
  pat_same v4 v17 with h_v4 h_v17 using hinv4 else hinv4 hG in EoCases.__eo_prog_str_update_in_first_concat.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a7 as ⟨v19, x_v19, h_v19⟩ else hinv4 hG in EoCases.__eo_prog_str_update_in_first_concat.case_0
  pat_unapply h_v19 as ⟨v21, v22, x_v21, x_v22, h_v21, h_v22, hn_v21, hn_v22⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_str_update_in_first_concat.case_0
  pat_unapply h_v21 as ⟨v24, v25, x_v24, x_v25, h_v24, h_v25, hn_v24, hn_v25⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_str_update_in_first_concat.case_0
  step as ⟨e_v26, he_v26⟩
  store_step with CtorSpec.eo__3d.construct s4 e_v26 (by rw [he_v26]; exact empty_args) hinv4 h64 as ⟨v26, s5, hinv5, h_v26⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 h_a9 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v19 h_v21 h_v22 h_v24 h_v25
  pat_same v24 v26 with h_v24 h_v26 using hinv5 else hinv5 hG in EoCases.__eo_prog_str_update_in_first_concat.case_0
  pat_unapply h_v25 as ⟨v28, v29, x_v28, x_v29, h_v28, h_v29, hn_v28, hn_v29⟩ using hinv5 else hinv5 hG in EoCases.__eo_prog_str_update_in_first_concat.case_0
  pat_unapply h_v28 as ⟨v31, v32, x_v31, x_v32, h_v31, h_v32, hn_v31, hn_v32⟩ using hinv5 else hinv5 hG in EoCases.__eo_prog_str_update_in_first_concat.case_0
  step as ⟨e_v33, he_v33⟩
  store_step with CtorSpec.eo__3c_3d.construct s5 e_v33 (by rw [he_v33]; exact empty_args) hinv5 h64 as ⟨v33, s6, hinv6, h_v33⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 h_a9 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v19 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32
  pat_same v31 v33 with h_v31 h_v33 using hinv6 else hinv6 hG in EoCases.__eo_prog_str_update_in_first_concat.case_0
  pat_unapply h_v32 as ⟨v35, v36, x_v35, x_v36, h_v35, h_v36, hn_v35, hn_v36⟩ using hinv6 else hinv6 hG in EoCases.__eo_prog_str_update_in_first_concat.case_0
  pat_unapply h_v35 as ⟨v38, v39, x_v38, x_v39, h_v38, h_v39, hn_v38, hn_v39⟩ using hinv6 else hinv6 hG in EoCases.__eo_prog_str_update_in_first_concat.case_0
  step as ⟨e_v40, he_v40⟩
  store_step with CtorSpec.eo__2b.construct s6 e_v40 (by rw [he_v40]; exact empty_args) hinv6 h64 as ⟨v40, s7, hinv7, h_v40⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 h_a9 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v19 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v38 h_v39
  pat_same v38 v40 with h_v38 h_v40 using hinv7 else hinv7 hG in EoCases.__eo_prog_str_update_in_first_concat.case_0
  pat_same v39 a3 with h_v39 h_a3 using hinv7 else hinv7 hG in EoCases.__eo_prog_str_update_in_first_concat.case_0
  pat_unapply h_v36 as ⟨v42, v43, x_v42, x_v43, h_v42, h_v43, hn_v42, hn_v43⟩ using hinv7 else hinv7 hG in EoCases.__eo_prog_str_update_in_first_concat.case_0
  pat_unapply h_v42 as ⟨v45, v46, x_v45, x_v46, h_v45, h_v46, hn_v45, hn_v46⟩ using hinv7 else hinv7 hG in EoCases.__eo_prog_str_update_in_first_concat.case_0
  step as ⟨e_v47, he_v47⟩
  store_step with CtorSpec.eo__2b.construct s7 e_v47 (by rw [he_v47]; exact empty_args) hinv7 h64 as ⟨v47, s8, hinv8, h_v47⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 h_a9 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v19 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v45 h_v46
  pat_same v45 v47 with h_v45 h_v47 using hinv8 else hinv8 hG in EoCases.__eo_prog_str_update_in_first_concat.case_0
  pat_unapply h_v46 as ⟨v49, v50, x_v49, x_v50, h_v49, h_v50, hn_v49, hn_v50⟩ using hinv8 else hinv8 hG in EoCases.__eo_prog_str_update_in_first_concat.case_0
  step as ⟨e_v51, he_v51⟩
  store_step with CtorSpec.eo_str_2elen.construct s8 e_v51 (by rw [he_v51]; exact empty_args) hinv8 h64 as ⟨v51, s9, hinv9, h_v51⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 h_a9 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v19 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v45 h_v46 h_v47 h_v49 h_v50
  pat_same v49 v51 with h_v49 h_v51 using hinv9 else hinv9 hG in EoCases.__eo_prog_str_update_in_first_concat.case_0
  pat_same v50 a2 with h_v50 h_a2 using hinv9 else hinv9 hG in EoCases.__eo_prog_str_update_in_first_concat.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s9 0#u32 (0) (by scalar_tac) hinv9 h64 as ⟨v52, s10, hinv10, h_v52⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 h_a9 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v19 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v45 h_v46 h_v47 h_v49 h_v50 h_v51
  pat_same v43 v52 with h_v43 h_v52 using hinv10 else hinv10 hG in EoCases.__eo_prog_str_update_in_first_concat.case_0
  pat_unapply h_v29 as ⟨v54, v55, x_v54, x_v55, h_v54, h_v55, hn_v54, hn_v55⟩ using hinv10 else hinv10 hG in EoCases.__eo_prog_str_update_in_first_concat.case_0
  step as ⟨e_v56, he_v56⟩
  store_step with CtorSpec.eo_str_2elen.construct s10 e_v56 (by rw [he_v56]; exact empty_args) hinv10 h64 as ⟨v56, s11, hinv11, h_v56⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 h_a9 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v19 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v45 h_v46 h_v47 h_v49 h_v50 h_v51 h_v52 h_v54 h_v55
  pat_same v54 v56 with h_v54 h_v56 using hinv11 else hinv11 hG in EoCases.__eo_prog_str_update_in_first_concat.case_0
  pat_same v55 a0 with h_v55 h_a0 using hinv11 else hinv11 hG in EoCases.__eo_prog_str_update_in_first_concat.case_0
  store_step with Store.literal_boolean_spec s11 true hinv11 h64 as ⟨v57, s12, hinv12, h_v57⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 h_a9 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v19 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v45 h_v46 h_v47 h_v49 h_v50 h_v51 h_v52 h_v54 h_v55 h_v56
  pat_same v22 v57 with h_v22 h_v57 using hinv12 else hinv12 hG in EoCases.__eo_prog_str_update_in_first_concat.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a8 as ⟨v59, x_v59, h_v59⟩ else hinv12 hG in EoCases.__eo_prog_str_update_in_first_concat.case_0
  pat_unapply h_v59 as ⟨v61, v62, x_v61, x_v62, h_v61, h_v62, hn_v61, hn_v62⟩ using hinv12 else hinv12 hG in EoCases.__eo_prog_str_update_in_first_concat.case_0
  pat_unapply h_v61 as ⟨v64, v65, x_v64, x_v65, h_v64, h_v65, hn_v64, hn_v65⟩ using hinv12 else hinv12 hG in EoCases.__eo_prog_str_update_in_first_concat.case_0
  step as ⟨e_v66, he_v66⟩
  store_step with CtorSpec.eo__3d.construct s12 e_v66 (by rw [he_v66]; exact empty_args) hinv12 h64 as ⟨v66, s13, hinv13, h_v66⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 h_a9 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v19 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v45 h_v46 h_v47 h_v49 h_v50 h_v51 h_v52 h_v54 h_v55 h_v56 h_v57 h_v59 h_v61 h_v62 h_v64 h_v65
  pat_same v64 v66 with h_v64 h_v66 using hinv13 else hinv13 hG in EoCases.__eo_prog_str_update_in_first_concat.case_0
  pat_same v65 a4 with h_v65 h_a4 using hinv13 else hinv13 hG in EoCases.__eo_prog_str_update_in_first_concat.case_0
  pat_unapply h_v62 as ⟨v68, v69, x_v68, x_v69, h_v68, h_v69, hn_v68, hn_v69⟩ using hinv13 else hinv13 hG in EoCases.__eo_prog_str_update_in_first_concat.case_0
  pat_unapply h_v68 as ⟨v71, v72, x_v71, x_v72, h_v71, h_v72, hn_v71, hn_v72⟩ using hinv13 else hinv13 hG in EoCases.__eo_prog_str_update_in_first_concat.case_0
  pat_unapply h_v71 as ⟨v74, v75, x_v74, x_v75, h_v74, h_v75, hn_v74, hn_v75⟩ using hinv13 else hinv13 hG in EoCases.__eo_prog_str_update_in_first_concat.case_0
  step as ⟨e_v76, he_v76⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s13 e_v76 (by rw [he_v76]; exact empty_args) hinv13 h64 as ⟨v76, s14, hinv14, h_v76⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 h_a9 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v19 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v45 h_v46 h_v47 h_v49 h_v50 h_v51 h_v52 h_v54 h_v55 h_v56 h_v57 h_v59 h_v61 h_v62 h_v64 h_v65 h_v66 h_v68 h_v69 h_v71 h_v72 h_v74 h_v75
  pat_same v74 v76 with h_v74 h_v76 using hinv14 else hinv14 hG in EoCases.__eo_prog_str_update_in_first_concat.case_0
  pat_same v75 a0 with h_v75 h_a0 using hinv14 else hinv14 hG in EoCases.__eo_prog_str_update_in_first_concat.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s14 0#u32 (0) (by scalar_tac) hinv14 h64 as ⟨v77, s15, hinv15, h_v77⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 h_a9 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v19 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v45 h_v46 h_v47 h_v49 h_v50 h_v51 h_v52 h_v54 h_v55 h_v56 h_v57 h_v59 h_v61 h_v62 h_v64 h_v65 h_v66 h_v68 h_v69 h_v71 h_v72 h_v74 h_v75 h_v76
  pat_same v72 v77 with h_v72 h_v77 using hinv15 else hinv15 hG in EoCases.__eo_prog_str_update_in_first_concat.case_0
  pat_same v69 a3 with h_v69 h_a3 using hinv15 else hinv15 hG in EoCases.__eo_prog_str_update_in_first_concat.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a9 as ⟨v79, x_v79, h_v79⟩ else hinv15 hG in EoCases.__eo_prog_str_update_in_first_concat.case_0
  pat_unapply h_v79 as ⟨v81, v82, x_v81, x_v82, h_v81, h_v82, hn_v81, hn_v82⟩ using hinv15 else hinv15 hG in EoCases.__eo_prog_str_update_in_first_concat.case_0
  pat_unapply h_v81 as ⟨v84, v85, x_v84, x_v85, h_v84, h_v85, hn_v84, hn_v85⟩ using hinv15 else hinv15 hG in EoCases.__eo_prog_str_update_in_first_concat.case_0
  step as ⟨e_v86, he_v86⟩
  store_step with CtorSpec.eo__3d.construct s15 e_v86 (by rw [he_v86]; exact empty_args) hinv15 h64 as ⟨v86, s16, hinv16, h_v86⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 h_a9 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v19 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v45 h_v46 h_v47 h_v49 h_v50 h_v51 h_v52 h_v54 h_v55 h_v56 h_v57 h_v59 h_v61 h_v62 h_v64 h_v65 h_v66 h_v68 h_v69 h_v71 h_v72 h_v74 h_v75 h_v76 h_v77 h_v79 h_v81 h_v82 h_v84 h_v85
  pat_same v84 v86 with h_v84 h_v86 using hinv16 else hinv16 hG in EoCases.__eo_prog_str_update_in_first_concat.case_0
  pat_same v85 a5 with h_v85 h_a5 using hinv16 else hinv16 hG in EoCases.__eo_prog_str_update_in_first_concat.case_0
  pat_unapply h_v82 as ⟨v88, v89, x_v88, x_v89, h_v88, h_v89, hn_v88, hn_v89⟩ using hinv16 else hinv16 hG in EoCases.__eo_prog_str_update_in_first_concat.case_0
  pat_unapply h_v88 as ⟨v91, v92, x_v91, x_v92, h_v91, h_v92, hn_v91, hn_v92⟩ using hinv16 else hinv16 hG in EoCases.__eo_prog_str_update_in_first_concat.case_0
  pat_unapply h_v91 as ⟨v94, v95, x_v94, x_v95, h_v94, h_v95, hn_v94, hn_v95⟩ using hinv16 else hinv16 hG in EoCases.__eo_prog_str_update_in_first_concat.case_0
  step as ⟨e_v96, he_v96⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s16 e_v96 (by rw [he_v96]; exact empty_args) hinv16 h64 as ⟨v96, s17, hinv17, h_v96⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 h_a9 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v19 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v45 h_v46 h_v47 h_v49 h_v50 h_v51 h_v52 h_v54 h_v55 h_v56 h_v57 h_v59 h_v61 h_v62 h_v64 h_v65 h_v66 h_v68 h_v69 h_v71 h_v72 h_v74 h_v75 h_v76 h_v77 h_v79 h_v81 h_v82 h_v84 h_v85 h_v86 h_v88 h_v89 h_v91 h_v92 h_v94 h_v95
  pat_same v94 v96 with h_v94 h_v96 using hinv17 else hinv17 hG in EoCases.__eo_prog_str_update_in_first_concat.case_0
  pat_same v95 a0 with h_v95 h_a0 using hinv17 else hinv17 hG in EoCases.__eo_prog_str_update_in_first_concat.case_0
  pat_unapply h_v92 as ⟨v98, v99, x_v98, x_v99, h_v98, h_v99, hn_v98, hn_v99⟩ using hinv17 else hinv17 hG in EoCases.__eo_prog_str_update_in_first_concat.case_0
  pat_unapply h_v98 as ⟨v101, v102, x_v101, x_v102, h_v101, h_v102, hn_v101, hn_v102⟩ using hinv17 else hinv17 hG in EoCases.__eo_prog_str_update_in_first_concat.case_0
  step as ⟨e_v103, he_v103⟩
  store_step with CtorSpec.eo__2b.construct s17 e_v103 (by rw [he_v103]; exact empty_args) hinv17 h64 as ⟨v103, s18, hinv18, h_v103⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 h_a9 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v19 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v45 h_v46 h_v47 h_v49 h_v50 h_v51 h_v52 h_v54 h_v55 h_v56 h_v57 h_v59 h_v61 h_v62 h_v64 h_v65 h_v66 h_v68 h_v69 h_v71 h_v72 h_v74 h_v75 h_v76 h_v77 h_v79 h_v81 h_v82 h_v84 h_v85 h_v86 h_v88 h_v89 h_v91 h_v92 h_v94 h_v95 h_v96 h_v98 h_v99 h_v101 h_v102
  pat_same v101 v103 with h_v101 h_v103 using hinv18 else hinv18 hG in EoCases.__eo_prog_str_update_in_first_concat.case_0
  pat_same v102 a3 with h_v102 h_a3 using hinv18 else hinv18 hG in EoCases.__eo_prog_str_update_in_first_concat.case_0
  pat_unapply h_v99 as ⟨v105, v106, x_v105, x_v106, h_v105, h_v106, hn_v105, hn_v106⟩ using hinv18 else hinv18 hG in EoCases.__eo_prog_str_update_in_first_concat.case_0
  pat_unapply h_v105 as ⟨v108, v109, x_v108, x_v109, h_v108, h_v109, hn_v108, hn_v109⟩ using hinv18 else hinv18 hG in EoCases.__eo_prog_str_update_in_first_concat.case_0
  step as ⟨e_v110, he_v110⟩
  store_step with CtorSpec.eo__2b.construct s18 e_v110 (by rw [he_v110]; exact empty_args) hinv18 h64 as ⟨v110, s19, hinv19, h_v110⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 h_a9 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v19 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v45 h_v46 h_v47 h_v49 h_v50 h_v51 h_v52 h_v54 h_v55 h_v56 h_v57 h_v59 h_v61 h_v62 h_v64 h_v65 h_v66 h_v68 h_v69 h_v71 h_v72 h_v74 h_v75 h_v76 h_v77 h_v79 h_v81 h_v82 h_v84 h_v85 h_v86 h_v88 h_v89 h_v91 h_v92 h_v94 h_v95 h_v96 h_v98 h_v99 h_v101 h_v102 h_v103 h_v105 h_v106 h_v108 h_v109
  pat_same v108 v110 with h_v108 h_v110 using hinv19 else hinv19 hG in EoCases.__eo_prog_str_update_in_first_concat.case_0
  pat_unapply h_v109 as ⟨v112, v113, x_v112, x_v113, h_v112, h_v113, hn_v112, hn_v113⟩ using hinv19 else hinv19 hG in EoCases.__eo_prog_str_update_in_first_concat.case_0
  step as ⟨e_v114, he_v114⟩
  store_step with CtorSpec.eo_str_2elen.construct s19 e_v114 (by rw [he_v114]; exact empty_args) hinv19 h64 as ⟨v114, s20, hinv20, h_v114⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 h_a9 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v19 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v45 h_v46 h_v47 h_v49 h_v50 h_v51 h_v52 h_v54 h_v55 h_v56 h_v57 h_v59 h_v61 h_v62 h_v64 h_v65 h_v66 h_v68 h_v69 h_v71 h_v72 h_v74 h_v75 h_v76 h_v77 h_v79 h_v81 h_v82 h_v84 h_v85 h_v86 h_v88 h_v89 h_v91 h_v92 h_v94 h_v95 h_v96 h_v98 h_v99 h_v101 h_v102 h_v103 h_v105 h_v106 h_v108 h_v109 h_v110 h_v112 h_v113
  pat_same v112 v114 with h_v112 h_v114 using hinv20 else hinv20 hG in EoCases.__eo_prog_str_update_in_first_concat.case_0
  pat_same v113 a2 with h_v113 h_a2 using hinv20 else hinv20 hG in EoCases.__eo_prog_str_update_in_first_concat.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s20 0#u32 (0) (by scalar_tac) hinv20 h64 as ⟨v115, s21, hinv21, h_v115⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 h_a9 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v19 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v45 h_v46 h_v47 h_v49 h_v50 h_v51 h_v52 h_v54 h_v55 h_v56 h_v57 h_v59 h_v61 h_v62 h_v64 h_v65 h_v66 h_v68 h_v69 h_v71 h_v72 h_v74 h_v75 h_v76 h_v77 h_v79 h_v81 h_v82 h_v84 h_v85 h_v86 h_v88 h_v89 h_v91 h_v92 h_v94 h_v95 h_v96 h_v98 h_v99 h_v101 h_v102 h_v103 h_v105 h_v106 h_v108 h_v109 h_v110 h_v112 h_v113 h_v114
  pat_same v106 v115 with h_v106 h_v115 using hinv21 else hinv21 hG in EoCases.__eo_prog_str_update_in_first_concat.case_0
  pat_unapply h_v89 as ⟨v117, v118, x_v117, x_v118, h_v117, h_v118, hn_v117, hn_v118⟩ using hinv21 else hinv21 hG in EoCases.__eo_prog_str_update_in_first_concat.case_0
  step as ⟨e_v119, he_v119⟩
  store_step with CtorSpec.eo_str_2elen.construct s21 e_v119 (by rw [he_v119]; exact empty_args) hinv21 h64 as ⟨v119, s22, hinv22, h_v119⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 h_a9 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v19 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v45 h_v46 h_v47 h_v49 h_v50 h_v51 h_v52 h_v54 h_v55 h_v56 h_v57 h_v59 h_v61 h_v62 h_v64 h_v65 h_v66 h_v68 h_v69 h_v71 h_v72 h_v74 h_v75 h_v76 h_v77 h_v79 h_v81 h_v82 h_v84 h_v85 h_v86 h_v88 h_v89 h_v91 h_v92 h_v94 h_v95 h_v96 h_v98 h_v99 h_v101 h_v102 h_v103 h_v105 h_v106 h_v108 h_v109 h_v110 h_v112 h_v113 h_v114 h_v115 h_v117 h_v118
  pat_same v117 v119 with h_v117 h_v119 using hinv22 else hinv22 hG in EoCases.__eo_prog_str_update_in_first_concat.case_0
  pat_same v118 a0 with h_v118 h_a0 using hinv22 else hinv22 hG in EoCases.__eo_prog_str_update_in_first_concat.case_0
  step as ⟨e_v120, he_v120⟩
  store_step with CtorSpec.eo__3d.construct s22 e_v120 (by rw [he_v120]; exact empty_args) hinv22 h64 as ⟨v120, s23, hinv23, h_v120⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 h_a9 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v19 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v45 h_v46 h_v47 h_v49 h_v50 h_v51 h_v52 h_v54 h_v55 h_v56 h_v57 h_v59 h_v61 h_v62 h_v64 h_v65 h_v66 h_v68 h_v69 h_v71 h_v72 h_v74 h_v75 h_v76 h_v77 h_v79 h_v81 h_v82 h_v84 h_v85 h_v86 h_v88 h_v89 h_v91 h_v92 h_v94 h_v95 h_v96 h_v98 h_v99 h_v101 h_v102 h_v103 h_v105 h_v106 h_v108 h_v109 h_v110 h_v112 h_v113 h_v114 h_v115 h_v117 h_v118 h_v119
  step as ⟨e_v121, he_v121⟩
  store_step with CtorSpec.eo_str_2eupdate.construct s23 e_v121 (by rw [he_v121]; exact empty_args) hinv23 h64 as ⟨v121, s24, hinv24, h_v121⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 h_a9 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v19 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v45 h_v46 h_v47 h_v49 h_v50 h_v51 h_v52 h_v54 h_v55 h_v56 h_v57 h_v59 h_v61 h_v62 h_v64 h_v65 h_v66 h_v68 h_v69 h_v71 h_v72 h_v74 h_v75 h_v76 h_v77 h_v79 h_v81 h_v82 h_v84 h_v85 h_v86 h_v88 h_v89 h_v91 h_v92 h_v94 h_v95 h_v96 h_v98 h_v99 h_v101 h_v102 h_v103 h_v105 h_v106 h_v108 h_v109 h_v110 h_v112 h_v113 h_v114 h_v115 h_v117 h_v118 h_v119 h_v120
  step as ⟨e_v122, he_v122⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s24 e_v122 (by rw [he_v122]; exact empty_args) hinv24 h64 as ⟨v122, s25, hinv25, h_v122⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 h_a9 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v19 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v45 h_v46 h_v47 h_v49 h_v50 h_v51 h_v52 h_v54 h_v55 h_v56 h_v57 h_v59 h_v61 h_v62 h_v64 h_v65 h_v66 h_v68 h_v69 h_v71 h_v72 h_v74 h_v75 h_v76 h_v77 h_v79 h_v81 h_v82 h_v84 h_v85 h_v86 h_v88 h_v89 h_v91 h_v92 h_v94 h_v95 h_v96 h_v98 h_v99 h_v101 h_v102 h_v103 h_v105 h_v106 h_v108 h_v109 h_v110 h_v112 h_v113 h_v114 h_v115 h_v117 h_v118 h_v119 h_v120 h_v121
  store_step with Store.apply_rep s25 v122 a0 _ _ hinv25 h64 h_v122 h_a0 (by ns_tac) (by ns_tac) as ⟨v123, s26, hinv26, h_v123⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 h_a9 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v19 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v45 h_v46 h_v47 h_v49 h_v50 h_v51 h_v52 h_v54 h_v55 h_v56 h_v57 h_v59 h_v61 h_v62 h_v64 h_v65 h_v66 h_v68 h_v69 h_v71 h_v72 h_v74 h_v75 h_v76 h_v77 h_v79 h_v81 h_v82 h_v84 h_v85 h_v86 h_v88 h_v89 h_v91 h_v92 h_v94 h_v95 h_v96 h_v98 h_v99 h_v101 h_v102 h_v103 h_v105 h_v106 h_v108 h_v109 h_v110 h_v112 h_v113 h_v114 h_v115 h_v117 h_v118 h_v119 h_v120 h_v121 h_v122
  store_step with Store.apply_rep s26 v123 a1 _ _ hinv26 h64 h_v123 h_a1 (by ns_tac) (by ns_tac) as ⟨v124, s27, hinv27, h_v124⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 h_a9 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v19 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v45 h_v46 h_v47 h_v49 h_v50 h_v51 h_v52 h_v54 h_v55 h_v56 h_v57 h_v59 h_v61 h_v62 h_v64 h_v65 h_v66 h_v68 h_v69 h_v71 h_v72 h_v74 h_v75 h_v76 h_v77 h_v79 h_v81 h_v82 h_v84 h_v85 h_v86 h_v88 h_v89 h_v91 h_v92 h_v94 h_v95 h_v96 h_v98 h_v99 h_v101 h_v102 h_v103 h_v105 h_v106 h_v108 h_v109 h_v110 h_v112 h_v113 h_v114 h_v115 h_v117 h_v118 h_v119 h_v120 h_v121 h_v122 h_v123
  store_step with Store.apply_rep s27 v121 v124 _ _ hinv27 h64 h_v121 h_v124 (by ns_tac) (by ns_tac) as ⟨v125, s28, hinv28, h_v125⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 h_a9 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v19 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v45 h_v46 h_v47 h_v49 h_v50 h_v51 h_v52 h_v54 h_v55 h_v56 h_v57 h_v59 h_v61 h_v62 h_v64 h_v65 h_v66 h_v68 h_v69 h_v71 h_v72 h_v74 h_v75 h_v76 h_v77 h_v79 h_v81 h_v82 h_v84 h_v85 h_v86 h_v88 h_v89 h_v91 h_v92 h_v94 h_v95 h_v96 h_v98 h_v99 h_v101 h_v102 h_v103 h_v105 h_v106 h_v108 h_v109 h_v110 h_v112 h_v113 h_v114 h_v115 h_v117 h_v118 h_v119 h_v120 h_v121 h_v122 h_v123 h_v124
  store_step with Store.apply_rep s28 v125 a3 _ _ hinv28 h64 h_v125 h_a3 (by ns_tac) (by ns_tac) as ⟨v126, s29, hinv29, h_v126⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 h_a9 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v19 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v45 h_v46 h_v47 h_v49 h_v50 h_v51 h_v52 h_v54 h_v55 h_v56 h_v57 h_v59 h_v61 h_v62 h_v64 h_v65 h_v66 h_v68 h_v69 h_v71 h_v72 h_v74 h_v75 h_v76 h_v77 h_v79 h_v81 h_v82 h_v84 h_v85 h_v86 h_v88 h_v89 h_v91 h_v92 h_v94 h_v95 h_v96 h_v98 h_v99 h_v101 h_v102 h_v103 h_v105 h_v106 h_v108 h_v109 h_v110 h_v112 h_v113 h_v114 h_v115 h_v117 h_v118 h_v119 h_v120 h_v121 h_v122 h_v123 h_v124 h_v125
  store_step with Store.apply_rep s29 v126 a2 _ _ hinv29 h64 h_v126 h_a2 (by ns_tac) (by ns_tac) as ⟨v127, s30, hinv30, h_v127⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 h_a9 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v19 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v45 h_v46 h_v47 h_v49 h_v50 h_v51 h_v52 h_v54 h_v55 h_v56 h_v57 h_v59 h_v61 h_v62 h_v64 h_v65 h_v66 h_v68 h_v69 h_v71 h_v72 h_v74 h_v75 h_v76 h_v77 h_v79 h_v81 h_v82 h_v84 h_v85 h_v86 h_v88 h_v89 h_v91 h_v92 h_v94 h_v95 h_v96 h_v98 h_v99 h_v101 h_v102 h_v103 h_v105 h_v106 h_v108 h_v109 h_v110 h_v112 h_v113 h_v114 h_v115 h_v117 h_v118 h_v119 h_v120 h_v121 h_v122 h_v123 h_v124 h_v125 h_v126
  store_step with Store.apply_rep s30 v120 v127 _ _ hinv30 h64 h_v120 h_v127 (by ns_tac) (by ns_tac) as ⟨v128, s31, hinv31, h_v128⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 h_a9 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v19 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v45 h_v46 h_v47 h_v49 h_v50 h_v51 h_v52 h_v54 h_v55 h_v56 h_v57 h_v59 h_v61 h_v62 h_v64 h_v65 h_v66 h_v68 h_v69 h_v71 h_v72 h_v74 h_v75 h_v76 h_v77 h_v79 h_v81 h_v82 h_v84 h_v85 h_v86 h_v88 h_v89 h_v91 h_v92 h_v94 h_v95 h_v96 h_v98 h_v99 h_v101 h_v102 h_v103 h_v105 h_v106 h_v108 h_v109 h_v110 h_v112 h_v113 h_v114 h_v115 h_v117 h_v118 h_v119 h_v120 h_v121 h_v122 h_v123 h_v124 h_v125 h_v126 h_v127
  step as ⟨e_v129, he_v129⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s31 e_v129 (by rw [he_v129]; exact empty_args) hinv31 h64 as ⟨v129, s32, hinv32, h_v129⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 h_a9 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v19 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v45 h_v46 h_v47 h_v49 h_v50 h_v51 h_v52 h_v54 h_v55 h_v56 h_v57 h_v59 h_v61 h_v62 h_v64 h_v65 h_v66 h_v68 h_v69 h_v71 h_v72 h_v74 h_v75 h_v76 h_v77 h_v79 h_v81 h_v82 h_v84 h_v85 h_v86 h_v88 h_v89 h_v91 h_v92 h_v94 h_v95 h_v96 h_v98 h_v99 h_v101 h_v102 h_v103 h_v105 h_v106 h_v108 h_v109 h_v110 h_v112 h_v113 h_v114 h_v115 h_v117 h_v118 h_v119 h_v120 h_v121 h_v122 h_v123 h_v124 h_v125 h_v126 h_v127 h_v128
  store_step with Store.apply_rep s32 v129 a4 _ _ hinv32 h64 h_v129 h_a4 (by ns_tac) (by ns_tac) as ⟨v130, s33, hinv33, h_v130⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 h_a9 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v19 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v45 h_v46 h_v47 h_v49 h_v50 h_v51 h_v52 h_v54 h_v55 h_v56 h_v57 h_v59 h_v61 h_v62 h_v64 h_v65 h_v66 h_v68 h_v69 h_v71 h_v72 h_v74 h_v75 h_v76 h_v77 h_v79 h_v81 h_v82 h_v84 h_v85 h_v86 h_v88 h_v89 h_v91 h_v92 h_v94 h_v95 h_v96 h_v98 h_v99 h_v101 h_v102 h_v103 h_v105 h_v106 h_v108 h_v109 h_v110 h_v112 h_v113 h_v114 h_v115 h_v117 h_v118 h_v119 h_v120 h_v121 h_v122 h_v123 h_v124 h_v125 h_v126 h_v127 h_v128 h_v129
  step as ⟨e_v131, he_v131⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s33 e_v131 (by rw [he_v131]; exact empty_args) hinv33 h64 as ⟨v131, s34, hinv34, h_v131⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 h_a9 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v19 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v45 h_v46 h_v47 h_v49 h_v50 h_v51 h_v52 h_v54 h_v55 h_v56 h_v57 h_v59 h_v61 h_v62 h_v64 h_v65 h_v66 h_v68 h_v69 h_v71 h_v72 h_v74 h_v75 h_v76 h_v77 h_v79 h_v81 h_v82 h_v84 h_v85 h_v86 h_v88 h_v89 h_v91 h_v92 h_v94 h_v95 h_v96 h_v98 h_v99 h_v101 h_v102 h_v103 h_v105 h_v106 h_v108 h_v109 h_v110 h_v112 h_v113 h_v114 h_v115 h_v117 h_v118 h_v119 h_v120 h_v121 h_v122 h_v123 h_v124 h_v125 h_v126 h_v127 h_v128 h_v129 h_v130
  store_step with Store.apply_rep s34 v131 a2 _ _ hinv34 h64 h_v131 h_a2 (by ns_tac) (by ns_tac) as ⟨v132, s35, hinv35, h_v132⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 h_a9 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v19 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v45 h_v46 h_v47 h_v49 h_v50 h_v51 h_v52 h_v54 h_v55 h_v56 h_v57 h_v59 h_v61 h_v62 h_v64 h_v65 h_v66 h_v68 h_v69 h_v71 h_v72 h_v74 h_v75 h_v76 h_v77 h_v79 h_v81 h_v82 h_v84 h_v85 h_v86 h_v88 h_v89 h_v91 h_v92 h_v94 h_v95 h_v96 h_v98 h_v99 h_v101 h_v102 h_v103 h_v105 h_v106 h_v108 h_v109 h_v110 h_v112 h_v113 h_v114 h_v115 h_v117 h_v118 h_v119 h_v120 h_v121 h_v122 h_v123 h_v124 h_v125 h_v126 h_v127 h_v128 h_v129 h_v130 h_v131
  step as ⟨e_v133, he_v133⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s35 e_v133 (by rw [he_v133]; exact empty_args) hinv35 h64 as ⟨v133, s36, hinv36, h_v133⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 h_a9 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v19 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v45 h_v46 h_v47 h_v49 h_v50 h_v51 h_v52 h_v54 h_v55 h_v56 h_v57 h_v59 h_v61 h_v62 h_v64 h_v65 h_v66 h_v68 h_v69 h_v71 h_v72 h_v74 h_v75 h_v76 h_v77 h_v79 h_v81 h_v82 h_v84 h_v85 h_v86 h_v88 h_v89 h_v91 h_v92 h_v94 h_v95 h_v96 h_v98 h_v99 h_v101 h_v102 h_v103 h_v105 h_v106 h_v108 h_v109 h_v110 h_v112 h_v113 h_v114 h_v115 h_v117 h_v118 h_v119 h_v120 h_v121 h_v122 h_v123 h_v124 h_v125 h_v126 h_v127 h_v128 h_v129 h_v130 h_v131 h_v132
  store_step with Store.apply_rep s36 v133 a5 _ _ hinv36 h64 h_v133 h_a5 (by ns_tac) (by ns_tac) as ⟨v134, s37, hinv37, h_v134⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 h_a9 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v19 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v45 h_v46 h_v47 h_v49 h_v50 h_v51 h_v52 h_v54 h_v55 h_v56 h_v57 h_v59 h_v61 h_v62 h_v64 h_v65 h_v66 h_v68 h_v69 h_v71 h_v72 h_v74 h_v75 h_v76 h_v77 h_v79 h_v81 h_v82 h_v84 h_v85 h_v86 h_v88 h_v89 h_v91 h_v92 h_v94 h_v95 h_v96 h_v98 h_v99 h_v101 h_v102 h_v103 h_v105 h_v106 h_v108 h_v109 h_v110 h_v112 h_v113 h_v114 h_v115 h_v117 h_v118 h_v119 h_v120 h_v121 h_v122 h_v123 h_v124 h_v125 h_v126 h_v127 h_v128 h_v129 h_v130 h_v131 h_v132 h_v133
  store_step with Store.apply_rep s37 v134 a1 _ _ hinv37 h64 h_v134 h_a1 (by ns_tac) (by ns_tac) as ⟨v135, s38, hinv38, h_v135⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 h_a9 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v19 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v45 h_v46 h_v47 h_v49 h_v50 h_v51 h_v52 h_v54 h_v55 h_v56 h_v57 h_v59 h_v61 h_v62 h_v64 h_v65 h_v66 h_v68 h_v69 h_v71 h_v72 h_v74 h_v75 h_v76 h_v77 h_v79 h_v81 h_v82 h_v84 h_v85 h_v86 h_v88 h_v89 h_v91 h_v92 h_v94 h_v95 h_v96 h_v98 h_v99 h_v101 h_v102 h_v103 h_v105 h_v106 h_v108 h_v109 h_v110 h_v112 h_v113 h_v114 h_v115 h_v117 h_v118 h_v119 h_v120 h_v121 h_v122 h_v123 h_v124 h_v125 h_v126 h_v127 h_v128 h_v129 h_v130 h_v131 h_v132 h_v133 h_v134
  store_step with Store.apply_rep s38 v132 v135 _ _ hinv38 h64 h_v132 h_v135 (by ns_tac) (by ns_tac) as ⟨v136, s39, hinv39, h_v136⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 h_a9 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v19 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v45 h_v46 h_v47 h_v49 h_v50 h_v51 h_v52 h_v54 h_v55 h_v56 h_v57 h_v59 h_v61 h_v62 h_v64 h_v65 h_v66 h_v68 h_v69 h_v71 h_v72 h_v74 h_v75 h_v76 h_v77 h_v79 h_v81 h_v82 h_v84 h_v85 h_v86 h_v88 h_v89 h_v91 h_v92 h_v94 h_v95 h_v96 h_v98 h_v99 h_v101 h_v102 h_v103 h_v105 h_v106 h_v108 h_v109 h_v110 h_v112 h_v113 h_v114 h_v115 h_v117 h_v118 h_v119 h_v120 h_v121 h_v122 h_v123 h_v124 h_v125 h_v126 h_v127 h_v128 h_v129 h_v130 h_v131 h_v132 h_v133 h_v134 h_v135
  store_step with Store.apply_rep s39 v130 v136 _ _ hinv39 h64 h_v130 h_v136 (by ns_tac) (by ns_tac) as ⟨v137, s40, hinv40, h_v137⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 h_a9 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v19 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v45 h_v46 h_v47 h_v49 h_v50 h_v51 h_v52 h_v54 h_v55 h_v56 h_v57 h_v59 h_v61 h_v62 h_v64 h_v65 h_v66 h_v68 h_v69 h_v71 h_v72 h_v74 h_v75 h_v76 h_v77 h_v79 h_v81 h_v82 h_v84 h_v85 h_v86 h_v88 h_v89 h_v91 h_v92 h_v94 h_v95 h_v96 h_v98 h_v99 h_v101 h_v102 h_v103 h_v105 h_v106 h_v108 h_v109 h_v110 h_v112 h_v113 h_v114 h_v115 h_v117 h_v118 h_v119 h_v120 h_v121 h_v122 h_v123 h_v124 h_v125 h_v126 h_v127 h_v128 h_v129 h_v130 h_v131 h_v132 h_v133 h_v134 h_v135 h_v136
  store_step with Store.apply_rep s40 v128 v137 _ _ hinv40 h64 h_v128 h_v137 (by ns_tac) (by ns_tac) as ⟨v138, s41, hinv41, h_v138⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 h_a9 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v19 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v45 h_v46 h_v47 h_v49 h_v50 h_v51 h_v52 h_v54 h_v55 h_v56 h_v57 h_v59 h_v61 h_v62 h_v64 h_v65 h_v66 h_v68 h_v69 h_v71 h_v72 h_v74 h_v75 h_v76 h_v77 h_v79 h_v81 h_v82 h_v84 h_v85 h_v86 h_v88 h_v89 h_v91 h_v92 h_v94 h_v95 h_v96 h_v98 h_v99 h_v101 h_v102 h_v103 h_v105 h_v106 h_v108 h_v109 h_v110 h_v112 h_v113 h_v114 h_v115 h_v117 h_v118 h_v119 h_v120 h_v121 h_v122 h_v123 h_v124 h_v125 h_v126 h_v127 h_v128 h_v129 h_v130 h_v131 h_v132 h_v133 h_v134 h_v135 h_v136 h_v137
  case_done hinv41 hG with h_v138 in EoCases.__eo_prog_str_update_in_first_concat.case_0 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_a5 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v13 hn_v14 hn_v21 hn_v22 hn_v24 hn_v25 hn_v28 hn_v29 hn_v31 hn_v32 hn_v35 hn_v36 hn_v38 hn_v39 hn_v42 hn_v43 hn_v45 hn_v46 hn_v49 hn_v50 hn_v54 hn_v55 hn_v61 hn_v62 hn_v64 hn_v65 hn_v68 hn_v69 hn_v71 hn_v72 hn_v74 hn_v75 hn_v81 hn_v82 hn_v84 hn_v85 hn_v88 hn_v89 hn_v91 hn_v92 hn_v94 hn_v95 hn_v98 hn_v99 hn_v101 hn_v102 hn_v105 hn_v106 hn_v108 hn_v109 hn_v112 hn_v113 hn_v117 hn_v118

set_option maxHeartbeats 20000000 in
/-- logos's `__eo_prog_str_update_in_first_concat` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstr_2dupdate_2din_2dfirst_2dconcat.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _) (x_a7 : _) (x_a8 : _) (x_a9 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) (hw_a4 : Valid.valid x_a4) (hw_a5 : Valid.valid x_a5) (hw_a6 : Valid.valid x_a6) (hw_a7 : Valid.valid x_a7) (hw_a8 : Valid.valid x_a8) (hw_a9 : Valid.valid x_a9) :
    __eo_prog_str_update_in_first_concat x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 x_a9 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else if x_a4 = Eo.Term.Stuck then HasStuck.stuck else if x_a5 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_str_update_in_first_concat.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 x_a9] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_str_update_in_first_concat
  unfold EoCases.__eo_prog_str_update_in_first_concat.case_0
  logos_eq

set_option maxHeartbeats 20000000 in
theorem body_eo__24eo_5fprog_5fstr_2dupdate_2din_2dfirst_2dconcat_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _) (x_a7 : _) (x_a8 : _) (x_a9 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) (h_a6 : Represents.rep s a6 x_a6) (h_a7 : Represents.rep s a7 x_a7) (h_a8 : Represents.rep s a8 x_a8) (h_a9 : Represents.rep s a9 x_a9) :
    body_eo__24eo_5fprog_5fstr_2dupdate_2din_2dfirst_2dconcat s a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_update_in_first_concat x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 x_a9)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstr_2dupdate_2din_2dfirst_2dconcat.rust_eq x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 x_a9 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3) (by valid_tac hinv h_a4) (by valid_tac hinv h_a5) (by valid_tac hinv h_a6) (by valid_tac hinv h_a7) (by valid_tac hinv h_a8) (by valid_tac hinv h_a9)]
  unfold body_eo__24eo_5fprog_5fstr_2dupdate_2din_2dfirst_2dconcat
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  stuck_check h_a3 : x_a3 as hn_a3 else hinv hG
  stuck_check h_a4 : x_a4 as hn_a4 else hinv hG
  stuck_check h_a5 : x_a5 as hn_a5 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstr_2dupdate_2din_2dfirst_2dconcat_spec n ih s a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 x_a9 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 h_a9 hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_a5
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 h_a9 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_a5
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_a5 hc0 in EoCases.__eo_prog_str_update_in_first_concat.case_0

set_option maxHeartbeats 20000000 in
theorem eo__24eo_5fprog_5fstr_2dupdate_2din_2dfirst_2dconcat_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstr_2dupdate_2din_2dfirst_2dconcat.Spec n := by
  intro s a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 x_a9 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 h_a9
  unfold eo__24eo_5fprog_5fstr_2dupdate_2din_2dfirst_2dconcat
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstr_2dupdate_2din_2dfirst_2dconcat s1 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9) (fun s' t => Represents.rep s' t (__eo_prog_str_update_in_first_concat x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 x_a9))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstr_2dupdate_2din_2dfirst_2dconcat_spec m (ih m hm) s1 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 x_a9 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn) (by congr_one h_a4 hn) (by congr_one h_a5 hn) (by congr_one h_a6 hn) (by congr_one h_a7 hn) (by congr_one h_a8 hn) (by congr_one h_a9 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

end pathos_compiled_checker
