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
theorem case_0_eo__24eo_5fprog_5fbv_2dconcat_2dmerge_2dconst_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 a6 a7 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _) (x_a7 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) (h_a6 : Represents.rep s a6 x_a6) (h_a7 : Represents.rep s a7 x_a7) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) (hn_a4 : x_a4 ≠ Eo.Term.Stuck) (hn_a5 : x_a5 ≠ Eo.Term.Stuck) (hn_a6 : x_a6 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fbv_2dconcat_2dmerge_2dconst s a0 a1 a2 a3 a4 a5 a6 a7 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_bv_concat_merge_const.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_bv_concat_merge_const.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fbv_2dconcat_2dmerge_2dconst
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a7 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_bv_concat_merge_const.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_concat_merge_const.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_concat_merge_const.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v4 h_v6 h_v7 dropping h_a7 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_concat_merge_const.case_0
  pat_same v7 a5 with h_v7 h_a5 using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_concat_merge_const.case_0
  pat_unapply h_v4 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_concat_merge_const.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_concat_merge_const.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__2b.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v11 h_v13 h_v14 dropping h_v10 h_v4 h_v6 h_v7 h_v8 he_v15 hinv1 e_v15 s1 v10 v4 v6 v7 v8
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_concat_merge_const.case_0
  pat_same v14 a2 with h_v14 h_a2 using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_concat_merge_const.case_0
  pat_unapply h_v11 as ⟨v17, v18, x_v17, x_v18, h_v17, h_v18, hn_v17, hn_v18⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_concat_merge_const.case_0
  pat_unapply h_v17 as ⟨v20, v21, x_v20, x_v21, h_v20, h_v21, hn_v20, hn_v21⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_concat_merge_const.case_0
  step as ⟨e_v22, he_v22⟩
  store_step with CtorSpec.eo__2b.construct s2 e_v22 (by rw [he_v22]; exact empty_args) hinv2 h64 as ⟨v22, s3, hinv3, h_v22⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v18 h_v20 h_v21 dropping h_v11 h_v13 h_v14 h_v15 h_v17 he_v22 hinv2 e_v22 s2 v11 v13 v14 v15 v17
  pat_same v20 v22 with h_v20 h_v22 using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_concat_merge_const.case_0
  pat_same v21 a4 with h_v21 h_a4 using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_concat_merge_const.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s3 0#u32 (0) (by scalar_tac) hinv3 h64 as ⟨v23, s4, hinv4, h_v23⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v18 dropping h_v20 h_v21 h_v22 hinv3 s3 v20 v21 v22
  pat_same v18 v23 with h_v18 h_v23 using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_concat_merge_const.case_0
  step as ⟨e_v24, he_v24⟩
  store_step with CtorSpec.eo__3d.construct s4 e_v24 (by rw [he_v24]; exact empty_args) hinv4 h64 as ⟨v24, s5, hinv5, h_v24⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 dropping h_v18 h_v23 he_v24 hinv4 e_v24 s4 v18 v23
  step as ⟨e_v25, he_v25⟩
  store_step with CtorSpec.eo_concat.construct s5 e_v25 (by rw [he_v25]; exact empty_args) hinv5 h64 as ⟨v25, s6, hinv6, h_v25⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v24 dropping he_v25 hinv5 e_v25 s5
  step as ⟨e_v26, he_v26⟩
  store_step with CtorSpec.eo_concat.construct s6 e_v26 (by rw [he_v26]; exact empty_args) hinv6 h64 as ⟨v26, s7, hinv7, h_v26⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v24 h_v25 dropping he_v26 hinv6 e_v26 s6
  step as ⟨e_v27, he_v27⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s7 e_v27 (by rw [he_v27]; rfl) h_a2 hinv7 h64 as ⟨v27, s8, hinv8, h_v27⟩ growing hG carrying h_a0 h_a1 h_a3 h_a4 h_a5 h_a6 h_v24 h_v25 h_v26 dropping h_a2 he_v27 hinv7 e_v27 s7
  store_step with Store.apply_rep s8 v27 a1 _ _ hinv8 h64 h_v27 h_a1 (by ns_tac) (by ns_tac) as ⟨v28, s9, hinv9, h_v28⟩ growing hG carrying h_a0 h_a1 h_a3 h_a4 h_a5 h_a6 h_v24 h_v25 h_v26 dropping h_v27 hinv8 s8 v27
  store_step with Store.apply_rep s9 v26 v28 _ _ hinv9 h64 h_v26 h_v28 (by ns_tac) (by ns_tac) as ⟨v29, s10, hinv10, h_v29⟩ growing hG carrying h_a0 h_a1 h_a3 h_a4 h_a5 h_a6 h_v24 h_v25 dropping h_v26 h_v28 hinv9 s9 v26 v28
  step as ⟨e_v30, he_v30⟩
  store_step with CtorSpec.eo_concat.construct s10 e_v30 (by rw [he_v30]; exact empty_args) hinv10 h64 as ⟨v30, s11, hinv11, h_v30⟩ growing hG carrying h_a0 h_a1 h_a3 h_a4 h_a5 h_a6 h_v24 h_v25 h_v29 dropping he_v30 hinv10 e_v30 s10
  step as ⟨e_v31, he_v31⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s11 e_v31 (by rw [he_v31]; rfl) h_a4 hinv11 h64 as ⟨v31, s12, hinv12, h_v31⟩ growing hG carrying h_a0 h_a1 h_a3 h_a4 h_a5 h_a6 h_v24 h_v25 h_v29 h_v30 dropping he_v31 hinv11 e_v31 s11
  store_step with Store.apply_rep s12 v31 a3 _ _ hinv12 h64 h_v31 h_a3 (by ns_tac) (by ns_tac) as ⟨v32, s13, hinv13, h_v32⟩ growing hG carrying h_a0 h_a1 h_a3 h_a4 h_a5 h_a6 h_v24 h_v25 h_v29 h_v30 dropping h_v31 hinv12 s12 v31
  store_step with Store.apply_rep s13 v30 v32 _ _ hinv13 h64 h_v30 h_v32 (by ns_tac) (by ns_tac) as ⟨v33, s14, hinv14, h_v33⟩ growing hG carrying h_a0 h_a1 h_a3 h_a4 h_a5 h_a6 h_v24 h_v25 h_v29 dropping h_v30 h_v32 hinv13 s13 v30 v32
  store_step with Store.apply_rep s14 v33 a6 _ _ hinv14 h64 h_v33 h_a6 (by ns_tac) (by ns_tac) as ⟨v34, s15, hinv15, h_v34⟩ growing hG carrying h_a0 h_a1 h_a3 h_a4 h_a5 h_a6 h_v24 h_v25 h_v29 dropping h_v33 hinv14 s14 v33
  store_step with Store.apply_rep s15 v29 v34 _ _ hinv15 h64 h_v29 h_v34 (by ns_tac) (by ns_tac) as ⟨v35, s16, hinv16, h_v35⟩ growing hG carrying h_a0 h_a1 h_a3 h_a4 h_a5 h_a6 h_v24 h_v25 dropping h_v29 h_v34 hinv15 s15 v29 v34
  step as ⟨e_v36, he_v36⟩
  store_step with Store.builtin_spec_list_concat n ih.eo__24eo_5fis_5flist_5fnil s16 e_v36 (by rw [he_v36]; rfl) h_v25 h_a0 h_v35 hinv16 h64 (hG.rem hrem) op_not_left_eo_concat op_unique_nil_eo_concat as ⟨v36, s17, hinv17, h_v36⟩ growing hG carrying h_a0 h_a1 h_a3 h_a4 h_a5 h_a6 h_v24 dropping h_v25 h_v35 he_v36 hinv16 e_v36 s16 v25 v35
  store_step with Store.apply_mk_rep s17 v24 v36 _ _ hinv17 h64 h_v24 h_v36 as ⟨v37, s18, hinv18, h_v37⟩ growing hG carrying h_a0 h_a1 h_a3 h_a4 h_a5 h_a6 dropping h_v24 h_v36 hinv17 s17 v24 v36
  step as ⟨e_v38, he_v38⟩
  store_step with CtorSpec.eo_concat.construct s18 e_v38 (by rw [he_v38]; exact empty_args) hinv18 h64 as ⟨v38, s19, hinv19, h_v38⟩ growing hG carrying h_a0 h_a1 h_a3 h_a4 h_a5 h_a6 h_v37 dropping he_v38 hinv18 e_v38 s18
  step as ⟨e_v39, he_v39⟩
  store_step with CtorSpec.eo_concat.construct s19 e_v39 (by rw [he_v39]; exact empty_args) hinv19 h64 as ⟨v39, s20, hinv20, h_v39⟩ growing hG carrying h_a0 h_a1 h_a3 h_a4 h_a5 h_a6 h_v37 h_v38 dropping he_v39 hinv19 e_v39 s19
  step as ⟨e_v40, he_v40⟩
  store_step with CtorSpec.eo_concat.construct s20 e_v40 (by rw [he_v40]; exact empty_args) hinv20 h64 as ⟨v40, s21, hinv21, h_v40⟩ growing hG carrying h_a0 h_a1 h_a3 h_a4 h_a5 h_a6 h_v37 h_v38 h_v39 dropping he_v40 hinv20 e_v40 s20
  step as ⟨e_v41, he_v41⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s21 e_v41 (by rw [he_v41]; rfl) h_a5 hinv21 h64 as ⟨v41, s22, hinv22, h_v41⟩ growing hG carrying h_a0 h_a1 h_a3 h_a4 h_a6 h_v37 h_v38 h_v39 h_v40 dropping h_a5 he_v41 hinv21 e_v41 s21
  step as ⟨e_v42, he_v42⟩
  store_step with CtorSpec.eo__2b.construct s22 e_v42 (by rw [he_v42]; exact empty_args) hinv22 h64 as ⟨v42, s23, hinv23, h_v42⟩ growing hG carrying h_a0 h_a1 h_a3 h_a4 h_a6 h_v37 h_v38 h_v39 h_v40 h_v41 dropping he_v42 hinv22 e_v42 s22
  step as ⟨e_v43, he_v43⟩
  store_step with CtorSpec.eo__2a.construct s23 e_v43 (by rw [he_v43]; exact empty_args) hinv23 h64 as ⟨v43, s24, hinv24, h_v43⟩ growing hG carrying h_a0 h_a1 h_a3 h_a4 h_a6 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 dropping he_v43 hinv23 e_v43 s23
  store_step with Store.apply_rep s24 v43 a1 _ _ hinv24 h64 h_v43 h_a1 (by ns_tac) (by ns_tac) as ⟨v44, s25, hinv25, h_v44⟩ growing hG carrying h_a0 h_a3 h_a4 h_a6 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 dropping h_a1 h_v43 hinv24 s24 v43
  step as ⟨e_v45, he_v45⟩
  store_step with CtorSpec.eo__2a.construct s25 e_v45 (by rw [he_v45]; exact empty_args) hinv25 h64 as ⟨v45, s26, hinv26, h_v45⟩ growing hG carrying h_a0 h_a3 h_a4 h_a6 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v44 dropping he_v45 hinv25 e_v45 s25
  step as ⟨e_v46, he_v46⟩
  store_step with CtorSpec.eo_int_2epow2.construct s26 e_v46 (by rw [he_v46]; exact empty_args) hinv26 h64 as ⟨v46, s27, hinv27, h_v46⟩ growing hG carrying h_a0 h_a3 h_a4 h_a6 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v44 h_v45 dropping he_v46 hinv26 e_v46 s26
  store_step with Store.apply_rep s27 v46 a4 _ _ hinv27 h64 h_v46 h_a4 (by ns_tac) (by ns_tac) as ⟨v47, s28, hinv28, h_v47⟩ growing hG carrying h_a0 h_a3 h_a4 h_a6 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v44 h_v45 dropping h_v46 hinv27 s27 v46
  store_step with Store.apply_rep s28 v45 v47 _ _ hinv28 h64 h_v45 h_v47 (by ns_tac) (by ns_tac) as ⟨v48, s29, hinv29, h_v48⟩ growing hG carrying h_a0 h_a3 h_a4 h_a6 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v44 dropping h_v45 h_v47 hinv28 s28 v45 v47
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s29 1#u32 (1) (by scalar_tac) hinv29 h64 as ⟨v49, s30, hinv30, h_v49⟩ growing hG carrying h_a0 h_a3 h_a4 h_a6 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v44 h_v48 dropping hinv29 s29
  store_step with Store.apply_rep s30 v48 v49 _ _ hinv30 h64 h_v48 h_v49 (by ns_tac) (by ns_tac) as ⟨v50, s31, hinv31, h_v50⟩ growing hG carrying h_a0 h_a3 h_a4 h_a6 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v44 dropping h_v48 h_v49 hinv30 s30 v48 v49
  store_step with Store.apply_rep s31 v44 v50 _ _ hinv31 h64 h_v44 h_v50 (by ns_tac) (by ns_tac) as ⟨v51, s32, hinv32, h_v51⟩ growing hG carrying h_a0 h_a3 h_a4 h_a6 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 dropping h_v44 h_v50 hinv31 s31 v44 v50
  store_step with Store.apply_rep s32 v42 v51 _ _ hinv32 h64 h_v42 h_v51 (by ns_tac) (by ns_tac) as ⟨v52, s33, hinv33, h_v52⟩ growing hG carrying h_a0 h_a3 h_a4 h_a6 h_v37 h_v38 h_v39 h_v40 h_v41 dropping h_v42 h_v51 hinv32 s32 v42 v51
  step as ⟨e_v53, he_v53⟩
  store_step with CtorSpec.eo__2b.construct s33 e_v53 (by rw [he_v53]; exact empty_args) hinv33 h64 as ⟨v53, s34, hinv34, h_v53⟩ growing hG carrying h_a0 h_a3 h_a4 h_a6 h_v37 h_v38 h_v39 h_v40 h_v41 h_v52 dropping he_v53 hinv33 e_v53 s33
  step as ⟨e_v54, he_v54⟩
  store_step with CtorSpec.eo_mod.construct s34 e_v54 (by rw [he_v54]; exact empty_args) hinv34 h64 as ⟨v54, s35, hinv35, h_v54⟩ growing hG carrying h_a0 h_a3 h_a4 h_a6 h_v37 h_v38 h_v39 h_v40 h_v41 h_v52 h_v53 dropping he_v54 hinv34 e_v54 s34
  store_step with Store.apply_rep s35 v54 a3 _ _ hinv35 h64 h_v54 h_a3 (by ns_tac) (by ns_tac) as ⟨v55, s36, hinv36, h_v55⟩ growing hG carrying h_a0 h_a4 h_a6 h_v37 h_v38 h_v39 h_v40 h_v41 h_v52 h_v53 dropping h_a3 h_v54 hinv35 s35 v54
  step as ⟨e_v56, he_v56⟩
  store_step with CtorSpec.eo_int_2epow2.construct s36 e_v56 (by rw [he_v56]; exact empty_args) hinv36 h64 as ⟨v56, s37, hinv37, h_v56⟩ growing hG carrying h_a0 h_a4 h_a6 h_v37 h_v38 h_v39 h_v40 h_v41 h_v52 h_v53 h_v55 dropping he_v56 hinv36 e_v56 s36
  store_step with Store.apply_rep s37 v56 a4 _ _ hinv37 h64 h_v56 h_a4 (by ns_tac) (by ns_tac) as ⟨v57, s38, hinv38, h_v57⟩ growing hG carrying h_a0 h_a6 h_v37 h_v38 h_v39 h_v40 h_v41 h_v52 h_v53 h_v55 dropping h_a4 h_v56 hinv37 s37 v56
  store_step with Store.apply_rep s38 v55 v57 _ _ hinv38 h64 h_v55 h_v57 (by ns_tac) (by ns_tac) as ⟨v58, s39, hinv39, h_v58⟩ growing hG carrying h_a0 h_a6 h_v37 h_v38 h_v39 h_v40 h_v41 h_v52 h_v53 dropping h_v55 h_v57 hinv38 s38 v55 v57
  store_step with Store.apply_rep s39 v53 v58 _ _ hinv39 h64 h_v53 h_v58 (by ns_tac) (by ns_tac) as ⟨v59, s40, hinv40, h_v59⟩ growing hG carrying h_a0 h_a6 h_v37 h_v38 h_v39 h_v40 h_v41 h_v52 dropping h_v53 h_v58 hinv39 s39 v53 v58
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s40 0#u32 (0) (by scalar_tac) hinv40 h64 as ⟨v60, s41, hinv41, h_v60⟩ growing hG carrying h_a0 h_a6 h_v37 h_v38 h_v39 h_v40 h_v41 h_v52 h_v59 dropping hinv40 s40
  store_step with Store.apply_rep s41 v59 v60 _ _ hinv41 h64 h_v59 h_v60 (by ns_tac) (by ns_tac) as ⟨v61, s42, hinv42, h_v61⟩ growing hG carrying h_a0 h_a6 h_v37 h_v38 h_v39 h_v40 h_v41 h_v52 dropping h_v59 h_v60 hinv41 s41 v59 v60
  store_step with Store.apply_rep s42 v52 v61 _ _ hinv42 h64 h_v52 h_v61 (by ns_tac) (by ns_tac) as ⟨v62, s43, hinv43, h_v62⟩ growing hG carrying h_a0 h_a6 h_v37 h_v38 h_v39 h_v40 h_v41 dropping h_v52 h_v61 hinv42 s42 v52 v61
  store_step with Store.apply_rep s43 v41 v62 _ _ hinv43 h64 h_v41 h_v62 (by ns_tac) (by ns_tac) as ⟨v63, s44, hinv44, h_v63⟩ growing hG carrying h_a0 h_a6 h_v37 h_v38 h_v39 h_v40 dropping h_v41 h_v62 hinv43 s43 v41 v62
  store_step with Store.apply_rep s44 v40 v63 _ _ hinv44 h64 h_v40 h_v63 (by ns_tac) (by ns_tac) as ⟨v64, s45, hinv45, h_v64⟩ growing hG carrying h_a0 h_a6 h_v37 h_v38 h_v39 dropping h_v40 h_v63 hinv44 s44 v40 v63
  store_step with Store.apply_rep s45 v64 a6 _ _ hinv45 h64 h_v64 h_a6 (by ns_tac) (by ns_tac) as ⟨v65, s46, hinv46, h_v65⟩ growing hG carrying h_a0 h_v37 h_v38 h_v39 dropping h_a6 h_v64 hinv45 s45 v64
  step as ⟨e_v66, he_v66⟩
  store_step with Store.builtin_spec_list_concat n ih.eo__24eo_5fis_5flist_5fnil s46 e_v66 (by rw [he_v66]; rfl) h_v39 h_a0 h_v65 hinv46 h64 (hG.rem hrem) op_not_left_eo_concat op_unique_nil_eo_concat as ⟨v66, s47, hinv47, h_v66⟩ growing hG carrying h_v37 h_v38 dropping h_a0 h_v39 h_v65 he_v66 hinv46 e_v66 s46 v39 v65
  step as ⟨e_v67, he_v67⟩
  store_step with Store.builtin_spec_list_singleton_elim n ih.eo__24eo_5fis_5flist_5fnil s47 e_v67 (by rw [he_v67]; rfl) h_v38 h_v66 hinv47 h64 (hG.rem hrem) op_not_left_eo_concat op_nil_apply_eo_concat as ⟨v67, s48, hinv48, h_v67⟩ growing hG carrying h_v37 dropping h_v38 h_v66 he_v67 hinv47 e_v67 s47 v38 v66
  store_step with Store.apply_mk_rep s48 v37 v67 _ _ hinv48 h64 h_v37 h_v67 as ⟨v68, s49, hinv49, h_v68⟩ growing hG carrying dropping h_v37 h_v67 hinv48 s48 v37 v67
  case_done hinv49 hG with h_v68 in EoCases.__eo_prog_bv_concat_merge_const.case_0 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_a5 hn_a6 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v13 hn_v14 hn_v17 hn_v18 hn_v20 hn_v21

set_option maxHeartbeats 20000000 in
/-- logos's `__eo_prog_bv_concat_merge_const` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fbv_2dconcat_2dmerge_2dconst.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _) (x_a7 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) (hw_a4 : Valid.valid x_a4) (hw_a5 : Valid.valid x_a5) (hw_a6 : Valid.valid x_a6) (hw_a7 : Valid.valid x_a7) :
    __eo_prog_bv_concat_merge_const x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else if x_a4 = Eo.Term.Stuck then HasStuck.stuck else if x_a5 = Eo.Term.Stuck then HasStuck.stuck else if x_a6 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_bv_concat_merge_const.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_bv_concat_merge_const
  unfold EoCases.__eo_prog_bv_concat_merge_const.case_0
  logos_eq

set_option maxHeartbeats 20000000 in
theorem body_eo__24eo_5fprog_5fbv_2dconcat_2dmerge_2dconst_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 a6 a7 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _) (x_a7 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) (h_a6 : Represents.rep s a6 x_a6) (h_a7 : Represents.rep s a7 x_a7) :
    body_eo__24eo_5fprog_5fbv_2dconcat_2dmerge_2dconst s a0 a1 a2 a3 a4 a5 a6 a7 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_concat_merge_const x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fbv_2dconcat_2dmerge_2dconst.rust_eq x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3) (by valid_tac hinv h_a4) (by valid_tac hinv h_a5) (by valid_tac hinv h_a6) (by valid_tac hinv h_a7)]
  unfold body_eo__24eo_5fprog_5fbv_2dconcat_2dmerge_2dconst
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  stuck_check h_a3 : x_a3 as hn_a3 else hinv hG
  stuck_check h_a4 : x_a4 as hn_a4 else hinv hG
  stuck_check h_a5 : x_a5 as hn_a5 else hinv hG
  stuck_check h_a6 : x_a6 as hn_a6 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fbv_2dconcat_2dmerge_2dconst_spec n ih s a0 a1 a2 a3 a4 a5 a6 a7 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_a5 hn_a6
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_a5 hn_a6
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_a5 hn_a6 hc0 in EoCases.__eo_prog_bv_concat_merge_const.case_0

set_option maxHeartbeats 20000000 in
theorem eo__24eo_5fprog_5fbv_2dconcat_2dmerge_2dconst_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fbv_2dconcat_2dmerge_2dconst.Spec n := by
  intro s a0 a1 a2 a3 a4 a5 a6 a7 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7
  unfold eo__24eo_5fprog_5fbv_2dconcat_2dmerge_2dconst
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fbv_2dconcat_2dmerge_2dconst s1 a0 a1 a2 a3 a4 a5 a6 a7) (fun s' t => Represents.rep s' t (__eo_prog_bv_concat_merge_const x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fbv_2dconcat_2dmerge_2dconst_spec m (ih m hm) s1 a0 a1 a2 a3 a4 a5 a6 a7 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn) (by congr_one h_a4 hn) (by congr_one h_a5 hn) (by congr_one h_a6 hn) (by congr_one h_a7 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

end pathos_compiled_checker
