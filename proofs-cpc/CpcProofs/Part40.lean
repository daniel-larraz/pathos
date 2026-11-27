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
theorem case_0_eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d4_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) (hn_a4 : x_a4 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d4 s a0 a1 a2 a3 a4 a5 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_bv_extract_concat_4.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_bv_extract_concat_4.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d4 more_0_eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d4 more_1_eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d4 more_2_eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d4 more_3_eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d4
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a5 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_bv_extract_concat_4.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_extract_concat_4.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_extract_concat_4.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_extract_concat_4.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_extract_concat_4.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_extract_concat_4.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__3c.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_extract_concat_4.case_0
  pat_same v14 a4 with h_v14 h_a4 using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_extract_concat_4.case_0
  pat_unapply h_v11 as ⟨v17, v18, x_v17, x_v18, h_v17, h_v18, hn_v17, hn_v18⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_extract_concat_4.case_0
  pat_unapply h_v17 as ⟨v20, v21, x_v20, x_v21, h_v20, h_v21, hn_v20, hn_v21⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_extract_concat_4.case_0
  step as ⟨e_v22, he_v22⟩
  store_step with CtorSpec.eo__2d.construct s2 e_v22 (by rw [he_v22]; exact empty_args) hinv2 h64 as ⟨v22, s3, hinv3, h_v22⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v20 h_v21
  pat_same v20 v22 with h_v20 h_v22 using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_extract_concat_4.case_0
  pat_unapply h_v21 as ⟨v24, v25, x_v24, x_v25, h_v24, h_v25, hn_v24, hn_v25⟩ using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_extract_concat_4.case_0
  step as ⟨e_v26, he_v26⟩
  store_step with CtorSpec.eo__40bvsize.construct s3 e_v26 (by rw [he_v26]; exact empty_args) hinv3 h64 as ⟨v26, s4, hinv4, h_v26⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25
  pat_same v24 v26 with h_v24 h_v26 using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_extract_concat_4.case_0
  pat_unapply h_v25 as ⟨v28, v29, x_v28, x_v29, h_v28, h_v29, hn_v28, hn_v29⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_extract_concat_4.case_0
  pat_unapply h_v28 as ⟨v31, v32, x_v31, x_v32, h_v31, h_v32, hn_v31, hn_v32⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_extract_concat_4.case_0
  step as ⟨e_v33, he_v33⟩
  store_step with CtorSpec.eo_concat.construct s4 e_v33 (by rw [he_v33]; exact empty_args) hinv4 h64 as ⟨v33, s5, hinv5, h_v33⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32
  pat_same v31 v33 with h_v31 h_v33 using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_extract_concat_4.case_0
  pat_same v32 a0 with h_v32 h_a0 using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_extract_concat_4.case_0
  pat_unapply h_v29 as ⟨v35, v36, x_v35, x_v36, h_v35, h_v36, hn_v35, hn_v36⟩ using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_extract_concat_4.case_0
  pat_unapply h_v35 as ⟨v38, v39, x_v38, x_v39, h_v38, h_v39, hn_v38, hn_v39⟩ using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_extract_concat_4.case_0
  step as ⟨e_v40, he_v40⟩
  store_step with CtorSpec.eo_concat.construct s5 e_v40 (by rw [he_v40]; exact empty_args) hinv5 h64 as ⟨v40, s6, hinv6, h_v40⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v38 h_v39
  pat_same v38 v40 with h_v38 h_v40 using hinv6 else hinv6 hG in EoCases.__eo_prog_bv_extract_concat_4.case_0
  pat_same v39 a1 with h_v39 h_a1 using hinv6 else hinv6 hG in EoCases.__eo_prog_bv_extract_concat_4.case_0
  pat_same v36 a2 with h_v36 h_a2 using hinv6 else hinv6 hG in EoCases.__eo_prog_bv_extract_concat_4.case_0
  pat_unapply h_v18 as ⟨v42, v43, x_v42, x_v43, h_v42, h_v43, hn_v42, hn_v43⟩ using hinv6 else hinv6 hG in EoCases.__eo_prog_bv_extract_concat_4.case_0
  step as ⟨e_v44, he_v44⟩
  store_step with CtorSpec.eo__40bvsize.construct s6 e_v44 (by rw [he_v44]; exact empty_args) hinv6 h64 as ⟨v44, s7, hinv7, h_v44⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43
  pat_same v42 v44 with h_v42 h_v44 using hinv7 else hinv7 hG in EoCases.__eo_prog_bv_extract_concat_4.case_0
  pat_same v43 a0 with h_v43 h_a0 using hinv7 else hinv7 hG in EoCases.__eo_prog_bv_extract_concat_4.case_0
  store_step with Store.literal_boolean_spec s7 true hinv7 h64 as ⟨v45, s8, hinv8, h_v45⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v44
  pat_same v4 v45 with h_v4 h_v45 using hinv8 else hinv8 hG in EoCases.__eo_prog_bv_extract_concat_4.case_0
  step as ⟨e_v46, he_v46⟩
  store_step with CtorSpec.eo__3d.construct s8 e_v46 (by rw [he_v46]; exact empty_args) hinv8 h64 as ⟨v46, s9, hinv9, h_v46⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v44 h_v45
  step as ⟨e_v47, he_v47⟩
  store_step with CtorSpec.eo_extract.construct s9 e_v47 (by rw [he_v47]; rfl) h_a4 h_a3 hinv9 h64 as ⟨v47, s10, hinv10, h_v47⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v44 h_v45 h_v46
  step as ⟨e_v48, he_v48⟩
  store_step with CtorSpec.eo_concat.construct s10 e_v48 (by rw [he_v48]; exact empty_args) hinv10 h64 as ⟨v48, s11, hinv11, h_v48⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47
  store_step with Store.apply_rep s11 v48 a0 _ _ hinv11 h64 h_v48 h_a0 (by ns_tac) (by ns_tac) as ⟨v49, s12, hinv12, h_v49⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48
  step as ⟨e_v50, he_v50⟩
  store_step with CtorSpec.eo_concat.construct s12 e_v50 (by rw [he_v50]; exact empty_args) hinv12 h64 as ⟨v50, s13, hinv13, h_v50⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49
  step as ⟨e_v51, he_v51⟩
  store_step with CtorSpec.eo_concat.construct s13 e_v51 (by rw [he_v51]; exact empty_args) hinv13 h64 as ⟨v51, s14, hinv14, h_v51⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50
  store_step with Store.apply_rep s14 v51 a1 _ _ hinv14 h64 h_v51 h_a1 (by ns_tac) (by ns_tac) as ⟨v52, s15, hinv15, h_v52⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s15 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv15 h64 as ⟨v53, s16, hinv16, h_v53⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52
  store_step with Store.apply_rep s16 v52 v53 _ _ hinv16 h64 h_v52 h_v53 (by ns_tac) (by ns_tac) as ⟨v54, s17, hinv17, h_v54⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53
  step as ⟨e_v55, he_v55⟩
  store_step with Store.builtin_spec_list_concat n ih.eo__24eo_5fis_5flist_5fnil s17 e_v55 (by rw [he_v55]; rfl) h_v50 h_a2 h_v54 hinv17 h64 (hG.rem hrem) (by not_left_tac) (by unique_nil_tac) as ⟨v55, s18, hinv18, h_v55⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54
  store_step with Store.apply_mk_rep s18 v49 v55 _ _ hinv18 h64 h_v49 h_v55 as ⟨v56, s19, hinv19, h_v56⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55
  store_step with Store.apply_mk_rep s19 v47 v56 _ _ hinv19 h64 h_v47 h_v56 as ⟨v57, s20, hinv20, h_v57⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56
  store_step with Store.apply_mk_rep s20 v46 v57 _ _ hinv20 h64 h_v46 h_v57 as ⟨v58, s21, hinv21, h_v58⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57
  step as ⟨e_v59, he_v59⟩
  store_step with CtorSpec.eo_extract.construct s21 e_v59 (by rw [he_v59]; rfl) h_a4 h_a3 hinv21 h64 as ⟨v59, s22, hinv22, h_v59⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58
  step as ⟨e_v60, he_v60⟩
  store_step with CtorSpec.eo_concat.construct s22 e_v60 (by rw [he_v60]; exact empty_args) hinv22 h64 as ⟨v60, s23, hinv23, h_v60⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59
  step as ⟨e_v61, he_v61⟩
  store_step with CtorSpec.eo_concat.construct s23 e_v61 (by rw [he_v61]; exact empty_args) hinv23 h64 as ⟨v61, s24, hinv24, h_v61⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60
  step as ⟨e_v62, he_v62⟩
  store_step with CtorSpec.eo_concat.construct s24 e_v62 (by rw [he_v62]; exact empty_args) hinv24 h64 as ⟨v62, s25, hinv25, h_v62⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61
  store_step with Store.apply_rep s25 v62 a1 _ _ hinv25 h64 h_v62 h_a1 (by ns_tac) (by ns_tac) as ⟨v63, s26, hinv26, h_v63⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s26 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv26 h64 as ⟨v64, s27, hinv27, h_v64⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63
  store_step with Store.apply_rep s27 v63 v64 _ _ hinv27 h64 h_v63 h_v64 (by ns_tac) (by ns_tac) as ⟨v65, s28, hinv28, h_v65⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64
  step as ⟨e_v66, he_v66⟩
  store_step with Store.builtin_spec_list_concat n ih.eo__24eo_5fis_5flist_5fnil s28 e_v66 (by rw [he_v66]; rfl) h_v61 h_a2 h_v65 hinv28 h64 (hG.rem hrem) (by not_left_tac) (by unique_nil_tac) as ⟨v66, s29, hinv29, h_v66⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65
  step as ⟨e_v67, he_v67⟩
  store_step with Store.builtin_spec_list_singleton_elim n ih.eo__24eo_5fis_5flist_5fnil s29 e_v67 (by rw [he_v67]; rfl) h_v60 h_v66 hinv29 h64 (hG.rem hrem) (by not_left_tac) (by nil_apply_tac) as ⟨v67, s30, hinv30, h_v67⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66
  store_step with Store.apply_mk_rep s30 v59 v67 _ _ hinv30 h64 h_v59 h_v67 as ⟨v68, s31, hinv31, h_v68⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67
  store_step with Store.apply_mk_rep s31 v58 v68 _ _ hinv31 h64 h_v58 h_v68 as ⟨v69, s32, hinv32, h_v69⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v38 h_v39 h_v40 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68
  case_done hinv32 hG with h_v69 in EoCases.__eo_prog_bv_extract_concat_4.case_0 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v13 hn_v14 hn_v17 hn_v18 hn_v20 hn_v21 hn_v24 hn_v25 hn_v28 hn_v29 hn_v31 hn_v32 hn_v35 hn_v36 hn_v38 hn_v39 hn_v42 hn_v43

set_option maxHeartbeats 20000000 in
/-- logos's `__eo_prog_bv_extract_concat_4` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d4.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) (hw_a4 : Valid.valid x_a4) (hw_a5 : Valid.valid x_a5) :
    __eo_prog_bv_extract_concat_4 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else if x_a4 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_bv_extract_concat_4.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_bv_extract_concat_4
  unfold EoCases.__eo_prog_bv_extract_concat_4.case_0
  logos_eq

set_option maxHeartbeats 20000000 in
theorem body_eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d4_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) :
    body_eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d4 s a0 a1 a2 a3 a4 a5 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_extract_concat_4 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d4.rust_eq x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3) (by valid_tac hinv h_a4) (by valid_tac hinv h_a5)]
  unfold body_eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d4
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  stuck_check h_a3 : x_a3 as hn_a3 else hinv hG
  stuck_check h_a4 : x_a4 as hn_a4 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d4_spec n ih s a0 a1 a2 a3 a4 a5 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 hn_a0 hn_a1 hn_a2 hn_a3 hn_a4
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hc0 in EoCases.__eo_prog_bv_extract_concat_4.case_0

set_option maxHeartbeats 20000000 in
theorem eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d4_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d4.Spec n := by
  intro s a0 a1 a2 a3 a4 a5 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5
  unfold eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d4
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d4 s1 a0 a1 a2 a3 a4 a5) (fun s' t => Represents.rep s' t (__eo_prog_bv_extract_concat_4 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d4_spec m (ih m hm) s1 a0 a1 a2 a3 a4 a5 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn) (by congr_one h_a4 hn) (by congr_one h_a5 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

end pathos_compiled_checker
