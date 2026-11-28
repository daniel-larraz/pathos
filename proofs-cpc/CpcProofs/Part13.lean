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

set_option maxHeartbeats 11640000 in
theorem case_0_eo__24eo_5fprog_5fconcat_5fsplit_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fconcat_5fsplit s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_concat_split.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_concat_split.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fconcat_5fsplit
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a1 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_concat_split.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_concat_split.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_concat_split.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a2 h_v4 h_v6 h_v7 dropping h_a1 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_concat_split.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a2 as ⟨v10, x_v10, h_v10⟩ else hinv1 hG in EoCases.__eo_prog_concat_split.case_0
  pat_unapply h_v10 as ⟨v12, v13, x_v12, x_v13, h_v12, h_v13, hn_v12, hn_v13⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_concat_split.case_0
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo_not.construct s1 e_v14 (by rw [he_v14]; exact empty_args) hinv1 h64 as ⟨v14, s2, hinv2, h_v14⟩ growing hG carrying h_a0 h_v4 h_v7 h_v12 h_v13 dropping h_a2 h_v10 h_v6 h_v8 he_v14 hinv1 e_v14 s1 v10 v6 v8
  pat_same v12 v14 with h_v12 h_v14 using hinv2 else hinv2 hG in EoCases.__eo_prog_concat_split.case_0
  pat_unapply h_v13 as ⟨v16, v17, x_v16, x_v17, h_v16, h_v17, hn_v16, hn_v17⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_concat_split.case_0
  pat_unapply h_v16 as ⟨v19, v20, x_v19, x_v20, h_v19, h_v20, hn_v19, hn_v20⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_concat_split.case_0
  step as ⟨e_v21, he_v21⟩
  store_step with CtorSpec.eo__3d.construct s2 e_v21 (by rw [he_v21]; exact empty_args) hinv2 h64 as ⟨v21, s3, hinv3, h_v21⟩ growing hG carrying h_a0 h_v4 h_v7 h_v17 h_v19 h_v20 dropping h_v12 h_v13 h_v14 h_v16 he_v21 hinv2 e_v21 s2 v12 v13 v14 v16
  pat_same v19 v21 with h_v19 h_v21 using hinv3 else hinv3 hG in EoCases.__eo_prog_concat_split.case_0
  pat_unapply h_v20 as ⟨v23, v24, x_v23, x_v24, h_v23, h_v24, hn_v23, hn_v24⟩ using hinv3 else hinv3 hG in EoCases.__eo_prog_concat_split.case_0
  step as ⟨e_v25, he_v25⟩
  store_step with CtorSpec.eo_str_2elen.construct s3 e_v25 (by rw [he_v25]; exact empty_args) hinv3 h64 as ⟨v25, s4, hinv4, h_v25⟩ growing hG carrying h_a0 h_v4 h_v7 h_v17 h_v23 h_v24 dropping h_v19 h_v20 h_v21 he_v25 hinv3 e_v25 s3 v19 v20 v21
  pat_same v23 v25 with h_v23 h_v25 using hinv4 else hinv4 hG in EoCases.__eo_prog_concat_split.case_0
  pat_unapply h_v17 as ⟨v27, v28, x_v27, x_v28, h_v27, h_v28, hn_v27, hn_v28⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_concat_split.case_0
  step as ⟨e_v29, he_v29⟩
  store_step with CtorSpec.eo_str_2elen.construct s4 e_v29 (by rw [he_v29]; exact empty_args) hinv4 h64 as ⟨v29, s5, hinv5, h_v29⟩ growing hG carrying h_a0 h_v4 h_v7 h_v24 h_v27 h_v28 dropping h_v17 h_v23 h_v25 he_v29 hinv4 e_v29 s4 v17 v23 v25
  pat_same v27 v29 with h_v27 h_v29 using hinv5 else hinv5 hG in EoCases.__eo_prog_concat_split.case_0
  step as ⟨e_v30, he_v30⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s5 e_v30 (by rw [he_v30]; exact empty_args) hinv5 h64 as ⟨v30, s6, hinv6, h_v30⟩ growing hG carrying h_a0 h_v4 h_v7 h_v24 h_v28 dropping h_v27 h_v29 he_v30 hinv5 e_v30 s5 v27 v29
  have h_ite_v37 := (show if_0_eo__24eo_5fprog_5fconcat_5fsplit s6 a0 v7 ⦃ r s' => s'.Inv ∧ s6.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_0_eo__24eo_5fprog_5fconcat_5fsplit
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s6
    rcases Store.boolean_value_term h_a0 with ⟨hx_31, hbv_31⟩ | ⟨hx_31, hbv_31⟩ | ⟨hx_31, hbv_31⟩
    · ite_branch hbv_31
      step as ⟨e_v31, he_v31⟩
      store_step with CtorSpec.eo_str_2e_2b_2b.construct s6 e_v31 (by rw [he_v31]; exact empty_args) hinv6 h64 as ⟨v31, s7, hinv7, h_v31⟩ growing hG carrying h_a0 h_v4 h_v7 h_v24 h_v28 h_v30 dropping he_v31 e_v31
      step as ⟨e_v32, he_v32⟩
      store_step with CtorSpec.eo_str_2e_2b_2b.construct s7 e_v32 (by rw [he_v32]; exact empty_args) hinv7 h64 as ⟨v32, s8, hinv8, h_v32⟩ growing hG carrying h_a0 h_v4 h_v7 h_v24 h_v28 h_v30 h_v31 dropping he_v32 e_v32
      step as ⟨e_v33, he_v33⟩
      store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s8 e_v33 (by rw [he_v33]; rfl) h_v32 h_v7 hinv8 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v33, s9, hinv9, h_v33⟩ growing hG carrying h_a0 h_v4 h_v7 h_v24 h_v28 h_v30 h_v31 dropping h_v32 he_v33 e_v33 v32
      step as ⟨e_v34, he_v34⟩
      store_step with Store.builtin_spec_list_rev n ih.eo__24eo_5fis_5flist_5fnil s9 e_v34 (by rw [he_v34]; rfl) h_v31 h_v33 hinv9 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v34, s10, hinv10, h_v34⟩ growing hG carrying h_a0 h_v4 h_v7 h_v24 h_v28 h_v30 dropping h_v31 h_v33 he_v34 e_v34 v31 v33
      ite_done hinv10 hG with (eo_ite_true_rep _ hx_31 h_v34)
    · ite_branch hbv_31
      step as ⟨e_v35, he_v35⟩
      store_step with CtorSpec.eo_str_2e_2b_2b.construct s6 e_v35 (by rw [he_v35]; exact empty_args) hinv6 h64 as ⟨v35, s7, hinv7, h_v35⟩ growing hG carrying h_a0 h_v4 h_v7 h_v24 h_v28 h_v30 dropping he_v35 e_v35
      step as ⟨e_v36, he_v36⟩
      store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s7 e_v36 (by rw [he_v36]; rfl) h_v35 h_v7 hinv7 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v36, s8, hinv8, h_v36⟩ growing hG carrying h_a0 h_v4 h_v7 h_v24 h_v28 h_v30 dropping h_v35 he_v36 e_v36 v35
      ite_done hinv8 hG with (eo_ite_false_rep _ hx_31 h_v36)
    · ite_branch hbv_31
      ite_stuck hinv6 hG with hx_31)
  store_step with h_ite_v37 as ⟨v37, s7, hinv7, h_v37⟩ growing hG carrying h_a0 h_v4 h_v7 h_v24 h_v28 h_v30 dropping h_ite_v37 hinv6 s6
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s7 0#u32 (0) (by scalar_tac) hinv7 h64 as ⟨v38, s8, hinv8, h_v38⟩ growing hG carrying h_a0 h_v4 h_v7 h_v24 h_v28 h_v30 h_v37 dropping hinv7 s7
  step as ⟨e_v39, he_v39⟩
  store_step with Store.builtin_spec_list_nth n ih.eo__24eo_5fis_5flist_5fnil s8 e_v39 (by rw [he_v39]; rfl) h_v30 h_v37 h_v38 hinv8 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v39, s9, hinv9, h_v39⟩ growing hG carrying h_a0 h_v4 h_v7 h_v24 h_v28 dropping h_v30 h_v37 h_v38 he_v39 hinv8 e_v39 s8 v30 v37 v38
  have h_req_v412 := (show requires_45_eo__24eo_5fprog_5fconcat_5fsplit s9 v39 v24 a0 v4 v28 v7 ⦃ r s' => s'.Inv ∧ s9.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold requires_45_eo__24eo_5fprog_5fconcat_5fsplit
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s9
    req_same v39 v24 with h_v39 h_v24 using hinv9 hG
    req_stuck h_v39 as hq_v39 using hinv9 hG
    step as ⟨e_v40, he_v40⟩
    store_step with CtorSpec.eo_str_2e_2b_2b.construct s9 e_v40 (by rw [he_v40]; exact empty_args) hinv9 h64 as ⟨v40, s10, hinv10, h_v40⟩ growing hG carrying h_a0 h_v4 h_v7 h_v28 dropping h_v24 h_v39 he_v40 hinv9 e_v40 s9 v24 v39
    have h_ite_v47 := (show if_1_eo__24eo_5fprog_5fconcat_5fsplit s10 a0 v4 ⦃ r s' => s'.Inv ∧ s10.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
      unfold if_1_eo__24eo_5fprog_5fconcat_5fsplit
      have hrem := (hG.rem hrem)
      have hG := Store.Grows.refl s10
      rcases Store.boolean_value_term h_a0 with ⟨hx_41, hbv_41⟩ | ⟨hx_41, hbv_41⟩ | ⟨hx_41, hbv_41⟩
      · ite_branch hbv_41
        step as ⟨e_v41, he_v41⟩
        store_step with CtorSpec.eo_str_2e_2b_2b.construct s10 e_v41 (by rw [he_v41]; exact empty_args) hinv10 h64 as ⟨v41, s11, hinv11, h_v41⟩ growing hG carrying h_a0 h_v4 h_v7 h_v28 h_v40 dropping he_v41 e_v41
        step as ⟨e_v42, he_v42⟩
        store_step with CtorSpec.eo_str_2e_2b_2b.construct s11 e_v42 (by rw [he_v42]; exact empty_args) hinv11 h64 as ⟨v42, s12, hinv12, h_v42⟩ growing hG carrying h_a0 h_v4 h_v7 h_v28 h_v40 h_v41 dropping he_v42 e_v42
        step as ⟨e_v43, he_v43⟩
        store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s12 e_v43 (by rw [he_v43]; rfl) h_v42 h_v4 hinv12 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v43, s13, hinv13, h_v43⟩ growing hG carrying h_a0 h_v4 h_v7 h_v28 h_v40 h_v41 dropping h_v42 he_v43 e_v43 v42
        step as ⟨e_v44, he_v44⟩
        store_step with Store.builtin_spec_list_rev n ih.eo__24eo_5fis_5flist_5fnil s13 e_v44 (by rw [he_v44]; rfl) h_v41 h_v43 hinv13 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v44, s14, hinv14, h_v44⟩ growing hG carrying h_a0 h_v4 h_v7 h_v28 h_v40 dropping h_v41 h_v43 he_v44 e_v44 v41 v43
        ite_done hinv14 hG with (eo_ite_true_rep _ hx_41 h_v44)
      · ite_branch hbv_41
        step as ⟨e_v45, he_v45⟩
        store_step with CtorSpec.eo_str_2e_2b_2b.construct s10 e_v45 (by rw [he_v45]; exact empty_args) hinv10 h64 as ⟨v45, s11, hinv11, h_v45⟩ growing hG carrying h_a0 h_v4 h_v7 h_v28 h_v40 dropping he_v45 e_v45
        step as ⟨e_v46, he_v46⟩
        store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s11 e_v46 (by rw [he_v46]; rfl) h_v45 h_v4 hinv11 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v46, s12, hinv12, h_v46⟩ growing hG carrying h_a0 h_v4 h_v7 h_v28 h_v40 dropping h_v45 he_v46 e_v46 v45
        ite_done hinv12 hG with (eo_ite_false_rep _ hx_41 h_v46)
      · ite_branch hbv_41
        ite_stuck hinv10 hG with hx_41)
    store_step with h_ite_v47 as ⟨v47, s11, hinv11, h_v47⟩ growing hG carrying h_a0 h_v4 h_v7 h_v28 h_v40 dropping h_ite_v47 hinv10 s10
    try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
    store_step with Store.literal_int_u32_spec s11 0#u32 (0) (by scalar_tac) hinv11 h64 as ⟨v48, s12, hinv12, h_v48⟩ growing hG carrying h_a0 h_v4 h_v7 h_v28 h_v40 h_v47 dropping hinv11 s11
    step as ⟨e_v49, he_v49⟩
    store_step with Store.builtin_spec_list_nth n ih.eo__24eo_5fis_5flist_5fnil s12 e_v49 (by rw [he_v49]; rfl) h_v40 h_v47 h_v48 hinv12 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v49, s13, hinv13, h_v49⟩ growing hG carrying h_a0 h_v4 h_v7 h_v28 dropping h_v40 h_v47 h_v48 he_v49 hinv12 e_v49 s12 v40 v47 v48
    have h_req_v411 := (show requires_44_eo__24eo_5fprog_5fconcat_5fsplit s13 v49 v28 a0 v7 v4 ⦃ r s' => s'.Inv ∧ s13.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
      unfold requires_44_eo__24eo_5fprog_5fconcat_5fsplit
      have hrem := (hG.rem hrem)
      have hG := Store.Grows.refl s13
      req_same v49 v28 with h_v49 h_v28 using hinv13 hG
      req_stuck h_v49 as hq_v49 using hinv13 hG
      step as ⟨e_v50, he_v50⟩
      store_step with CtorSpec.eo_and.construct s13 e_v50 (by rw [he_v50]; exact empty_args) hinv13 h64 as ⟨v50, s14, hinv14, h_v50⟩ growing hG carrying h_a0 h_v4 h_v7 dropping h_v28 h_v49 he_v50 hinv13 e_v50 s13 v28 v49
      step as ⟨e_v51, he_v51⟩
      store_step with CtorSpec.eo_or.construct s14 e_v51 (by rw [he_v51]; exact empty_args) hinv14 h64 as ⟨v51, s15, hinv15, h_v51⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 dropping he_v51 hinv14 e_v51 s14
      step as ⟨e_v52, he_v52⟩
      store_step with CtorSpec.eo__3d.construct s15 e_v52 (by rw [he_v52]; exact empty_args) hinv15 h64 as ⟨v52, s16, hinv16, h_v52⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 dropping he_v52 hinv15 e_v52 s15
      step as ⟨e_v53, he_v53⟩
      store_step with CtorSpec.eo_str_2e_2b_2b.construct s16 e_v53 (by rw [he_v53]; exact empty_args) hinv16 h64 as ⟨v53, s17, hinv17, h_v53⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v52 dropping he_v53 hinv16 e_v53 s16
      have h_ite_v60 := (show if_2_eo__24eo_5fprog_5fconcat_5fsplit s17 a0 v7 ⦃ r s' => s'.Inv ∧ s17.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_2_eo__24eo_5fprog_5fconcat_5fsplit
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s17
        rcases Store.boolean_value_term h_a0 with ⟨hx_54, hbv_54⟩ | ⟨hx_54, hbv_54⟩ | ⟨hx_54, hbv_54⟩
        · ite_branch hbv_54
          step as ⟨e_v54, he_v54⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s17 e_v54 (by rw [he_v54]; exact empty_args) hinv17 h64 as ⟨v54, s18, hinv18, h_v54⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v52 h_v53 dropping he_v54 e_v54
          step as ⟨e_v55, he_v55⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s18 e_v55 (by rw [he_v55]; exact empty_args) hinv18 h64 as ⟨v55, s19, hinv19, h_v55⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v52 h_v53 h_v54 dropping he_v55 e_v55
          step as ⟨e_v56, he_v56⟩
          store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s19 e_v56 (by rw [he_v56]; rfl) h_v55 h_v7 hinv19 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v56, s20, hinv20, h_v56⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v52 h_v53 h_v54 dropping h_v55 he_v56 e_v56 v55
          step as ⟨e_v57, he_v57⟩
          store_step with Store.builtin_spec_list_rev n ih.eo__24eo_5fis_5flist_5fnil s20 e_v57 (by rw [he_v57]; rfl) h_v54 h_v56 hinv20 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v57, s21, hinv21, h_v57⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v52 h_v53 dropping h_v54 h_v56 he_v57 e_v57 v54 v56
          ite_done hinv21 hG with (eo_ite_true_rep _ hx_54 h_v57)
        · ite_branch hbv_54
          step as ⟨e_v58, he_v58⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s17 e_v58 (by rw [he_v58]; exact empty_args) hinv17 h64 as ⟨v58, s18, hinv18, h_v58⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v52 h_v53 dropping he_v58 e_v58
          step as ⟨e_v59, he_v59⟩
          store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s18 e_v59 (by rw [he_v59]; rfl) h_v58 h_v7 hinv18 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v59, s19, hinv19, h_v59⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v52 h_v53 dropping h_v58 he_v59 e_v59 v58
          ite_done hinv19 hG with (eo_ite_false_rep _ hx_54 h_v59)
        · ite_branch hbv_54
          ite_stuck hinv17 hG with hx_54)
      store_step with h_ite_v60 as ⟨v60, s18, hinv18, h_v60⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v52 h_v53 dropping h_ite_v60 hinv17 s17
      try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
      store_step with Store.literal_int_u32_spec s18 0#u32 (0) (by scalar_tac) hinv18 h64 as ⟨v61, s19, hinv19, h_v61⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v52 h_v53 h_v60 dropping hinv18 s18
      step as ⟨e_v62, he_v62⟩
      store_step with Store.builtin_spec_list_nth n ih.eo__24eo_5fis_5flist_5fnil s19 e_v62 (by rw [he_v62]; rfl) h_v53 h_v60 h_v61 hinv19 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v62, s20, hinv20, h_v62⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v52 dropping h_v53 h_v60 h_v61 he_v62 hinv19 e_v62 s19 v53 v60 v61
      store_step with Store.apply_mk_rep s20 v52 v62 _ _ hinv20 h64 h_v52 h_v62 as ⟨v63, s21, hinv21, h_v63⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 dropping h_v52 h_v62 hinv20 s20 v52 v62
      have h_ite_v181 := (show if_16_eo__24eo_5fprog_5fconcat_5fsplit s21 a0 a0 v7 v4 ⦃ r s' => s'.Inv ∧ s21.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_16_eo__24eo_5fprog_5fconcat_5fsplit
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s21
        rcases Store.boolean_value_term h_a0 with ⟨hx_64, hbv_64⟩ | ⟨hx_64, hbv_64⟩ | ⟨hx_64, hbv_64⟩
        · ite_branch hbv_64
          step as ⟨e_v64, he_v64⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s21 e_v64 (by rw [he_v64]; exact empty_args) hinv21 h64 as ⟨v64, s22, hinv22, h_v64⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 dropping he_v64 e_v64
          step as ⟨e_v65, he_v65⟩
          store_step with CtorSpec.eo__40purify.construct s22 e_v65 (by rw [he_v65]; exact empty_args) hinv22 h64 as ⟨v65, s23, hinv23, h_v65⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v64 dropping he_v65 e_v65
          step as ⟨e_v66, he_v66⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s23 e_v66 (by rw [he_v66]; exact empty_args) hinv23 h64 as ⟨v66, s24, hinv24, h_v66⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v64 h_v65 dropping he_v66 e_v66
          have h_ite_v73 := (show if_3_eo__24eo_5fprog_5fconcat_5fsplit s24 a0 v7 ⦃ r s' => s'.Inv ∧ s24.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
            unfold if_3_eo__24eo_5fprog_5fconcat_5fsplit
            have hrem := (hG.rem hrem)
            have hG := Store.Grows.refl s24
            rcases Store.boolean_value_term h_a0 with ⟨hx_67, hbv_67⟩ | ⟨hx_67, hbv_67⟩ | ⟨hx_67, hbv_67⟩
            · ite_branch hbv_67
              step as ⟨e_v67, he_v67⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s24 e_v67 (by rw [he_v67]; exact empty_args) hinv24 h64 as ⟨v67, s25, hinv25, h_v67⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v64 h_v65 h_v66 dropping he_v67 e_v67
              step as ⟨e_v68, he_v68⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s25 e_v68 (by rw [he_v68]; exact empty_args) hinv25 h64 as ⟨v68, s26, hinv26, h_v68⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v64 h_v65 h_v66 h_v67 dropping he_v68 e_v68
              step as ⟨e_v69, he_v69⟩
              store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s26 e_v69 (by rw [he_v69]; rfl) h_v68 h_v7 hinv26 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v69, s27, hinv27, h_v69⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v64 h_v65 h_v66 h_v67 dropping h_v68 he_v69 e_v69 v68
              step as ⟨e_v70, he_v70⟩
              store_step with Store.builtin_spec_list_rev n ih.eo__24eo_5fis_5flist_5fnil s27 e_v70 (by rw [he_v70]; rfl) h_v67 h_v69 hinv27 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v70, s28, hinv28, h_v70⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v64 h_v65 h_v66 dropping h_v67 h_v69 he_v70 e_v70 v67 v69
              ite_done hinv28 hG with (eo_ite_true_rep _ hx_67 h_v70)
            · ite_branch hbv_67
              step as ⟨e_v71, he_v71⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s24 e_v71 (by rw [he_v71]; exact empty_args) hinv24 h64 as ⟨v71, s25, hinv25, h_v71⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v64 h_v65 h_v66 dropping he_v71 e_v71
              step as ⟨e_v72, he_v72⟩
              store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s25 e_v72 (by rw [he_v72]; rfl) h_v71 h_v7 hinv25 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v72, s26, hinv26, h_v72⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v64 h_v65 h_v66 dropping h_v71 he_v72 e_v72 v71
              ite_done hinv26 hG with (eo_ite_false_rep _ hx_67 h_v72)
            · ite_branch hbv_67
              ite_stuck hinv24 hG with hx_67)
          store_step with h_ite_v73 as ⟨v73, s25, hinv25, h_v73⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v64 h_v65 h_v66 dropping h_ite_v73
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s25 0#u32 (0) (by scalar_tac) hinv25 h64 as ⟨v74, s26, hinv26, h_v74⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v64 h_v65 h_v66 h_v73 dropping
          step as ⟨e_v75, he_v75⟩
          store_step with Store.builtin_spec_list_nth n ih.eo__24eo_5fis_5flist_5fnil s26 e_v75 (by rw [he_v75]; rfl) h_v66 h_v73 h_v74 hinv26 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v75, s27, hinv27, h_v75⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v64 h_v65 dropping h_v66 h_v73 h_v74 he_v75 e_v75 v66 v73 v74
          step as ⟨e_v76, he_v76⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s27 e_v76 (by rw [he_v76]; exact empty_args) hinv27 h64 as ⟨v76, s28, hinv28, h_v76⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v64 h_v65 h_v75 dropping he_v76 e_v76
          have h_ite_v83 := (show if_4_eo__24eo_5fprog_5fconcat_5fsplit s28 a0 v4 ⦃ r s' => s'.Inv ∧ s28.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
            unfold if_4_eo__24eo_5fprog_5fconcat_5fsplit
            have hrem := (hG.rem hrem)
            have hG := Store.Grows.refl s28
            rcases Store.boolean_value_term h_a0 with ⟨hx_77, hbv_77⟩ | ⟨hx_77, hbv_77⟩ | ⟨hx_77, hbv_77⟩
            · ite_branch hbv_77
              step as ⟨e_v77, he_v77⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s28 e_v77 (by rw [he_v77]; exact empty_args) hinv28 h64 as ⟨v77, s29, hinv29, h_v77⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v64 h_v65 h_v75 h_v76 dropping he_v77 e_v77
              step as ⟨e_v78, he_v78⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s29 e_v78 (by rw [he_v78]; exact empty_args) hinv29 h64 as ⟨v78, s30, hinv30, h_v78⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v64 h_v65 h_v75 h_v76 h_v77 dropping he_v78 e_v78
              step as ⟨e_v79, he_v79⟩
              store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s30 e_v79 (by rw [he_v79]; rfl) h_v78 h_v4 hinv30 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v79, s31, hinv31, h_v79⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v64 h_v65 h_v75 h_v76 h_v77 dropping h_v78 he_v79 e_v79 v78
              step as ⟨e_v80, he_v80⟩
              store_step with Store.builtin_spec_list_rev n ih.eo__24eo_5fis_5flist_5fnil s31 e_v80 (by rw [he_v80]; rfl) h_v77 h_v79 hinv31 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v80, s32, hinv32, h_v80⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v64 h_v65 h_v75 h_v76 dropping h_v77 h_v79 he_v80 e_v80 v77 v79
              ite_done hinv32 hG with (eo_ite_true_rep _ hx_77 h_v80)
            · ite_branch hbv_77
              step as ⟨e_v81, he_v81⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s28 e_v81 (by rw [he_v81]; exact empty_args) hinv28 h64 as ⟨v81, s29, hinv29, h_v81⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v64 h_v65 h_v75 h_v76 dropping he_v81 e_v81
              step as ⟨e_v82, he_v82⟩
              store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s29 e_v82 (by rw [he_v82]; rfl) h_v81 h_v4 hinv29 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v82, s30, hinv30, h_v82⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v64 h_v65 h_v75 h_v76 dropping h_v81 he_v82 e_v82 v81
              ite_done hinv30 hG with (eo_ite_false_rep _ hx_77 h_v82)
            · ite_branch hbv_77
              ite_stuck hinv28 hG with hx_77)
          store_step with h_ite_v83 as ⟨v83, s29, hinv29, h_v83⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v64 h_v65 h_v75 h_v76 dropping h_ite_v83
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s29 0#u32 (0) (by scalar_tac) hinv29 h64 as ⟨v84, s30, hinv30, h_v84⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v64 h_v65 h_v75 h_v76 h_v83 dropping
          step as ⟨e_v85, he_v85⟩
          store_step with Store.builtin_spec_list_nth n ih.eo__24eo_5fis_5flist_5fnil s30 e_v85 (by rw [he_v85]; rfl) h_v76 h_v83 h_v84 hinv30 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v85, s31, hinv31, h_v85⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v64 h_v65 h_v75 dropping h_v76 h_v83 h_v84 he_v85 e_v85 v76 v83 v84
          store_step with ih.eo__24str_5funify_5fsplit s31 v75 v85 a0 _ _ _ hinv31 h64 (hG.rem hrem) h_v75 h_v85 h_a0 as ⟨v86, s32, hinv32, h_v86⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v64 h_v65 dropping h_v75 h_v85 v75 v85
          store_step with Store.apply_mk_rep s32 v65 v86 _ _ hinv32 h64 h_v65 h_v86 as ⟨v87, s33, hinv33, h_v87⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v64 dropping h_v65 h_v86 v65 v86
          store_step with Store.apply_mk_rep s33 v64 v87 _ _ hinv33 h64 h_v64 h_v87 as ⟨v88, s34, hinv34, h_v88⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 dropping h_v64 h_v87 v64 v87
          step as ⟨e_v89, he_v89⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s34 e_v89 (by rw [he_v89]; exact empty_args) hinv34 h64 as ⟨v89, s35, hinv35, h_v89⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v88 dropping he_v89 e_v89
          step as ⟨e_v90, he_v90⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s35 e_v90 (by rw [he_v90]; exact empty_args) hinv35 h64 as ⟨v90, s36, hinv36, h_v90⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v88 h_v89 dropping he_v90 e_v90
          have h_ite_v97 := (show if_5_eo__24eo_5fprog_5fconcat_5fsplit s36 a0 v4 ⦃ r s' => s'.Inv ∧ s36.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
            unfold if_5_eo__24eo_5fprog_5fconcat_5fsplit
            have hrem := (hG.rem hrem)
            have hG := Store.Grows.refl s36
            rcases Store.boolean_value_term h_a0 with ⟨hx_91, hbv_91⟩ | ⟨hx_91, hbv_91⟩ | ⟨hx_91, hbv_91⟩
            · ite_branch hbv_91
              step as ⟨e_v91, he_v91⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s36 e_v91 (by rw [he_v91]; exact empty_args) hinv36 h64 as ⟨v91, s37, hinv37, h_v91⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v88 h_v89 h_v90 dropping he_v91 e_v91
              step as ⟨e_v92, he_v92⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s37 e_v92 (by rw [he_v92]; exact empty_args) hinv37 h64 as ⟨v92, s38, hinv38, h_v92⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v88 h_v89 h_v90 h_v91 dropping he_v92 e_v92
              step as ⟨e_v93, he_v93⟩
              store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s38 e_v93 (by rw [he_v93]; rfl) h_v92 h_v4 hinv38 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v93, s39, hinv39, h_v93⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v88 h_v89 h_v90 h_v91 dropping h_v92 he_v93 e_v93 v92
              step as ⟨e_v94, he_v94⟩
              store_step with Store.builtin_spec_list_rev n ih.eo__24eo_5fis_5flist_5fnil s39 e_v94 (by rw [he_v94]; rfl) h_v91 h_v93 hinv39 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v94, s40, hinv40, h_v94⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v88 h_v89 h_v90 dropping h_v91 h_v93 he_v94 e_v94 v91 v93
              ite_done hinv40 hG with (eo_ite_true_rep _ hx_91 h_v94)
            · ite_branch hbv_91
              step as ⟨e_v95, he_v95⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s36 e_v95 (by rw [he_v95]; exact empty_args) hinv36 h64 as ⟨v95, s37, hinv37, h_v95⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v88 h_v89 h_v90 dropping he_v95 e_v95
              step as ⟨e_v96, he_v96⟩
              store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s37 e_v96 (by rw [he_v96]; rfl) h_v95 h_v4 hinv37 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v96, s38, hinv38, h_v96⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v88 h_v89 h_v90 dropping h_v95 he_v96 e_v96 v95
              ite_done hinv38 hG with (eo_ite_false_rep _ hx_91 h_v96)
            · ite_branch hbv_91
              ite_stuck hinv36 hG with hx_91)
          store_step with h_ite_v97 as ⟨v97, s37, hinv37, h_v97⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v88 h_v89 h_v90 dropping h_ite_v97
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s37 0#u32 (0) (by scalar_tac) hinv37 h64 as ⟨v98, s38, hinv38, h_v98⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v88 h_v89 h_v90 h_v97 dropping
          step as ⟨e_v99, he_v99⟩
          store_step with Store.builtin_spec_list_nth n ih.eo__24eo_5fis_5flist_5fnil s38 e_v99 (by rw [he_v99]; rfl) h_v90 h_v97 h_v98 hinv38 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v99, s39, hinv39, h_v99⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v88 h_v89 dropping h_v90 h_v97 h_v98 he_v99 e_v99 v90 v97 v98
          store_step with Store.apply_mk_rep s39 v89 v99 _ _ hinv39 h64 h_v89 h_v99 as ⟨v100, s40, hinv40, h_v100⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v88 dropping h_v89 h_v99 v89 v99
          step as ⟨e_v101, he_v101⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s40 e_v101 (by rw [he_v101]; exact empty_args) hinv40 h64 as ⟨v101, s41, hinv41, h_v101⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v88 h_v100 dropping he_v101 e_v101
          step as ⟨e_v102, he_v102⟩
          store_step with CtorSpec.eo__40purify.construct s41 e_v102 (by rw [he_v102]; exact empty_args) hinv41 h64 as ⟨v102, s42, hinv42, h_v102⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v88 h_v100 h_v101 dropping he_v102 e_v102
          step as ⟨e_v103, he_v103⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s42 e_v103 (by rw [he_v103]; exact empty_args) hinv42 h64 as ⟨v103, s43, hinv43, h_v103⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v88 h_v100 h_v101 h_v102 dropping he_v103 e_v103
          have h_ite_v110 := (show if_6_eo__24eo_5fprog_5fconcat_5fsplit s43 a0 v7 ⦃ r s' => s'.Inv ∧ s43.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
            unfold if_6_eo__24eo_5fprog_5fconcat_5fsplit
            have hrem := (hG.rem hrem)
            have hG := Store.Grows.refl s43
            rcases Store.boolean_value_term h_a0 with ⟨hx_104, hbv_104⟩ | ⟨hx_104, hbv_104⟩ | ⟨hx_104, hbv_104⟩
            · ite_branch hbv_104
              step as ⟨e_v104, he_v104⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s43 e_v104 (by rw [he_v104]; exact empty_args) hinv43 h64 as ⟨v104, s44, hinv44, h_v104⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v88 h_v100 h_v101 h_v102 h_v103 dropping he_v104 e_v104
              step as ⟨e_v105, he_v105⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s44 e_v105 (by rw [he_v105]; exact empty_args) hinv44 h64 as ⟨v105, s45, hinv45, h_v105⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v88 h_v100 h_v101 h_v102 h_v103 h_v104 dropping he_v105 e_v105
              step as ⟨e_v106, he_v106⟩
              store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s45 e_v106 (by rw [he_v106]; rfl) h_v105 h_v7 hinv45 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v106, s46, hinv46, h_v106⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v88 h_v100 h_v101 h_v102 h_v103 h_v104 dropping h_v105 he_v106 e_v106 v105
              step as ⟨e_v107, he_v107⟩
              store_step with Store.builtin_spec_list_rev n ih.eo__24eo_5fis_5flist_5fnil s46 e_v107 (by rw [he_v107]; rfl) h_v104 h_v106 hinv46 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v107, s47, hinv47, h_v107⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v88 h_v100 h_v101 h_v102 h_v103 dropping h_v104 h_v106 he_v107 e_v107 v104 v106
              ite_done hinv47 hG with (eo_ite_true_rep _ hx_104 h_v107)
            · ite_branch hbv_104
              step as ⟨e_v108, he_v108⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s43 e_v108 (by rw [he_v108]; exact empty_args) hinv43 h64 as ⟨v108, s44, hinv44, h_v108⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v88 h_v100 h_v101 h_v102 h_v103 dropping he_v108 e_v108
              step as ⟨e_v109, he_v109⟩
              store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s44 e_v109 (by rw [he_v109]; rfl) h_v108 h_v7 hinv44 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v109, s45, hinv45, h_v109⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v88 h_v100 h_v101 h_v102 h_v103 dropping h_v108 he_v109 e_v109 v108
              ite_done hinv45 hG with (eo_ite_false_rep _ hx_104 h_v109)
            · ite_branch hbv_104
              ite_stuck hinv43 hG with hx_104)
          store_step with h_ite_v110 as ⟨v110, s44, hinv44, h_v110⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v88 h_v100 h_v101 h_v102 h_v103 dropping h_ite_v110
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s44 0#u32 (0) (by scalar_tac) hinv44 h64 as ⟨v111, s45, hinv45, h_v111⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v88 h_v100 h_v101 h_v102 h_v103 h_v110 dropping
          step as ⟨e_v112, he_v112⟩
          store_step with Store.builtin_spec_list_nth n ih.eo__24eo_5fis_5flist_5fnil s45 e_v112 (by rw [he_v112]; rfl) h_v103 h_v110 h_v111 hinv45 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v112, s46, hinv46, h_v112⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v88 h_v100 h_v101 h_v102 dropping h_v103 h_v110 h_v111 he_v112 e_v112 v103 v110 v111
          step as ⟨e_v113, he_v113⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s46 e_v113 (by rw [he_v113]; exact empty_args) hinv46 h64 as ⟨v113, s47, hinv47, h_v113⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v88 h_v100 h_v101 h_v102 h_v112 dropping he_v113 e_v113
          have h_ite_v120 := (show if_7_eo__24eo_5fprog_5fconcat_5fsplit s47 a0 v4 ⦃ r s' => s'.Inv ∧ s47.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
            unfold if_7_eo__24eo_5fprog_5fconcat_5fsplit
            have hrem := (hG.rem hrem)
            have hG := Store.Grows.refl s47
            rcases Store.boolean_value_term h_a0 with ⟨hx_114, hbv_114⟩ | ⟨hx_114, hbv_114⟩ | ⟨hx_114, hbv_114⟩
            · ite_branch hbv_114
              step as ⟨e_v114, he_v114⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s47 e_v114 (by rw [he_v114]; exact empty_args) hinv47 h64 as ⟨v114, s48, hinv48, h_v114⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v88 h_v100 h_v101 h_v102 h_v112 h_v113 dropping he_v114 e_v114
              step as ⟨e_v115, he_v115⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s48 e_v115 (by rw [he_v115]; exact empty_args) hinv48 h64 as ⟨v115, s49, hinv49, h_v115⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v88 h_v100 h_v101 h_v102 h_v112 h_v113 h_v114 dropping he_v115 e_v115
              step as ⟨e_v116, he_v116⟩
              store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s49 e_v116 (by rw [he_v116]; rfl) h_v115 h_v4 hinv49 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v116, s50, hinv50, h_v116⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v88 h_v100 h_v101 h_v102 h_v112 h_v113 h_v114 dropping h_v115 he_v116 e_v116 v115
              step as ⟨e_v117, he_v117⟩
              store_step with Store.builtin_spec_list_rev n ih.eo__24eo_5fis_5flist_5fnil s50 e_v117 (by rw [he_v117]; rfl) h_v114 h_v116 hinv50 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v117, s51, hinv51, h_v117⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v88 h_v100 h_v101 h_v102 h_v112 h_v113 dropping h_v114 h_v116 he_v117 e_v117 v114 v116
              ite_done hinv51 hG with (eo_ite_true_rep _ hx_114 h_v117)
            · ite_branch hbv_114
              step as ⟨e_v118, he_v118⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s47 e_v118 (by rw [he_v118]; exact empty_args) hinv47 h64 as ⟨v118, s48, hinv48, h_v118⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v88 h_v100 h_v101 h_v102 h_v112 h_v113 dropping he_v118 e_v118
              step as ⟨e_v119, he_v119⟩
              store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s48 e_v119 (by rw [he_v119]; rfl) h_v118 h_v4 hinv48 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v119, s49, hinv49, h_v119⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v88 h_v100 h_v101 h_v102 h_v112 h_v113 dropping h_v118 he_v119 e_v119 v118
              ite_done hinv49 hG with (eo_ite_false_rep _ hx_114 h_v119)
            · ite_branch hbv_114
              ite_stuck hinv47 hG with hx_114)
          store_step with h_ite_v120 as ⟨v120, s48, hinv48, h_v120⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v88 h_v100 h_v101 h_v102 h_v112 h_v113 dropping h_ite_v120
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s48 0#u32 (0) (by scalar_tac) hinv48 h64 as ⟨v121, s49, hinv49, h_v121⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v88 h_v100 h_v101 h_v102 h_v112 h_v113 h_v120 dropping
          step as ⟨e_v122, he_v122⟩
          store_step with Store.builtin_spec_list_nth n ih.eo__24eo_5fis_5flist_5fnil s49 e_v122 (by rw [he_v122]; rfl) h_v113 h_v120 h_v121 hinv49 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v122, s50, hinv50, h_v122⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v88 h_v100 h_v101 h_v102 h_v112 dropping h_v113 h_v120 h_v121 he_v122 e_v122 v113 v120 v121
          store_step with ih.eo__24str_5funify_5fsplit s50 v112 v122 a0 _ _ _ hinv50 h64 (hG.rem hrem) h_v112 h_v122 h_a0 as ⟨v123, s51, hinv51, h_v123⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v88 h_v100 h_v101 h_v102 dropping h_v112 h_v122 v112 v122
          store_step with Store.apply_mk_rep s51 v102 v123 _ _ hinv51 h64 h_v102 h_v123 as ⟨v124, s52, hinv52, h_v124⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v88 h_v100 h_v101 dropping h_v102 h_v123 v102 v123
          store_step with ih.eo__24eo_5ftypeof s52 v124 _ hinv52 h64 (hG.rem hrem) h_v124 as ⟨v125, s53, hinv53, h_v125⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v88 h_v100 h_v101 dropping h_v124 v124
          store_step with ih.eo__24eo_5fnil s53 v101 v125 _ _ hinv53 h64 (hG.rem hrem) h_v101 h_v125 as ⟨v126, s54, hinv54, h_v126⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v88 h_v100 dropping h_v101 h_v125 v101 v125
          store_step with Store.apply_mk_rep s54 v100 v126 _ _ hinv54 h64 h_v100 h_v126 as ⟨v127, s55, hinv55, h_v127⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v88 dropping h_v100 h_v126 v100 v126
          store_step with Store.apply_mk_rep s55 v88 v127 _ _ hinv55 h64 h_v88 h_v127 as ⟨v128, s56, hinv56, h_v128⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 dropping h_v127 h_v88 v127 v88
          ite_done hinv56 hG with (eo_ite_true_rep _ hx_64 h_v128)
        · ite_branch hbv_64
          step as ⟨e_v129, he_v129⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s21 e_v129 (by rw [he_v129]; exact empty_args) hinv21 h64 as ⟨v129, s22, hinv22, h_v129⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 dropping he_v129 e_v129
          step as ⟨e_v130, he_v130⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s22 e_v130 (by rw [he_v130]; exact empty_args) hinv22 h64 as ⟨v130, s23, hinv23, h_v130⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v129 dropping he_v130 e_v130
          have h_ite_v137 := (show if_8_eo__24eo_5fprog_5fconcat_5fsplit s23 a0 v4 ⦃ r s' => s'.Inv ∧ s23.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
            unfold if_8_eo__24eo_5fprog_5fconcat_5fsplit
            have hrem := (hG.rem hrem)
            have hG := Store.Grows.refl s23
            rcases Store.boolean_value_term h_a0 with ⟨hx_131, hbv_131⟩ | ⟨hx_131, hbv_131⟩ | ⟨hx_131, hbv_131⟩
            · ite_branch hbv_131
              step as ⟨e_v131, he_v131⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s23 e_v131 (by rw [he_v131]; exact empty_args) hinv23 h64 as ⟨v131, s24, hinv24, h_v131⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v129 h_v130 dropping he_v131 e_v131
              step as ⟨e_v132, he_v132⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s24 e_v132 (by rw [he_v132]; exact empty_args) hinv24 h64 as ⟨v132, s25, hinv25, h_v132⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v129 h_v130 h_v131 dropping he_v132 e_v132
              step as ⟨e_v133, he_v133⟩
              store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s25 e_v133 (by rw [he_v133]; rfl) h_v132 h_v4 hinv25 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v133, s26, hinv26, h_v133⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v129 h_v130 h_v131 dropping h_v132 he_v133 e_v133 v132
              step as ⟨e_v134, he_v134⟩
              store_step with Store.builtin_spec_list_rev n ih.eo__24eo_5fis_5flist_5fnil s26 e_v134 (by rw [he_v134]; rfl) h_v131 h_v133 hinv26 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v134, s27, hinv27, h_v134⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v129 h_v130 dropping h_v131 h_v133 he_v134 e_v134 v131 v133
              ite_done hinv27 hG with (eo_ite_true_rep _ hx_131 h_v134)
            · ite_branch hbv_131
              step as ⟨e_v135, he_v135⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s23 e_v135 (by rw [he_v135]; exact empty_args) hinv23 h64 as ⟨v135, s24, hinv24, h_v135⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v129 h_v130 dropping he_v135 e_v135
              step as ⟨e_v136, he_v136⟩
              store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s24 e_v136 (by rw [he_v136]; rfl) h_v135 h_v4 hinv24 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v136, s25, hinv25, h_v136⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v129 h_v130 dropping h_v135 he_v136 e_v136 v135
              ite_done hinv25 hG with (eo_ite_false_rep _ hx_131 h_v136)
            · ite_branch hbv_131
              ite_stuck hinv23 hG with hx_131)
          store_step with h_ite_v137 as ⟨v137, s24, hinv24, h_v137⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v129 h_v130 dropping h_ite_v137
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s24 0#u32 (0) (by scalar_tac) hinv24 h64 as ⟨v138, s25, hinv25, h_v138⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v129 h_v130 h_v137 dropping
          step as ⟨e_v139, he_v139⟩
          store_step with Store.builtin_spec_list_nth n ih.eo__24eo_5fis_5flist_5fnil s25 e_v139 (by rw [he_v139]; rfl) h_v130 h_v137 h_v138 hinv25 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v139, s26, hinv26, h_v139⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v129 dropping h_v130 h_v137 h_v138 he_v139 e_v139 v130 v137 v138
          store_step with Store.apply_mk_rep s26 v129 v139 _ _ hinv26 h64 h_v129 h_v139 as ⟨v140, s27, hinv27, h_v140⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 dropping h_v129 h_v139 v129 v139
          step as ⟨e_v141, he_v141⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s27 e_v141 (by rw [he_v141]; exact empty_args) hinv27 h64 as ⟨v141, s28, hinv28, h_v141⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v140 dropping he_v141 e_v141
          step as ⟨e_v142, he_v142⟩
          store_step with CtorSpec.eo__40purify.construct s28 e_v142 (by rw [he_v142]; exact empty_args) hinv28 h64 as ⟨v142, s29, hinv29, h_v142⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v140 h_v141 dropping he_v142 e_v142
          step as ⟨e_v143, he_v143⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s29 e_v143 (by rw [he_v143]; exact empty_args) hinv29 h64 as ⟨v143, s30, hinv30, h_v143⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v140 h_v141 h_v142 dropping he_v143 e_v143
          have h_ite_v150 := (show if_9_eo__24eo_5fprog_5fconcat_5fsplit s30 a0 v7 ⦃ r s' => s'.Inv ∧ s30.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
            unfold if_9_eo__24eo_5fprog_5fconcat_5fsplit
            have hrem := (hG.rem hrem)
            have hG := Store.Grows.refl s30
            rcases Store.boolean_value_term h_a0 with ⟨hx_144, hbv_144⟩ | ⟨hx_144, hbv_144⟩ | ⟨hx_144, hbv_144⟩
            · ite_branch hbv_144
              step as ⟨e_v144, he_v144⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s30 e_v144 (by rw [he_v144]; exact empty_args) hinv30 h64 as ⟨v144, s31, hinv31, h_v144⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v140 h_v141 h_v142 h_v143 dropping he_v144 e_v144
              step as ⟨e_v145, he_v145⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s31 e_v145 (by rw [he_v145]; exact empty_args) hinv31 h64 as ⟨v145, s32, hinv32, h_v145⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v140 h_v141 h_v142 h_v143 h_v144 dropping he_v145 e_v145
              step as ⟨e_v146, he_v146⟩
              store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s32 e_v146 (by rw [he_v146]; rfl) h_v145 h_v7 hinv32 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v146, s33, hinv33, h_v146⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v140 h_v141 h_v142 h_v143 h_v144 dropping h_v145 he_v146 e_v146 v145
              step as ⟨e_v147, he_v147⟩
              store_step with Store.builtin_spec_list_rev n ih.eo__24eo_5fis_5flist_5fnil s33 e_v147 (by rw [he_v147]; rfl) h_v144 h_v146 hinv33 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v147, s34, hinv34, h_v147⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v140 h_v141 h_v142 h_v143 dropping h_v144 h_v146 he_v147 e_v147 v144 v146
              ite_done hinv34 hG with (eo_ite_true_rep _ hx_144 h_v147)
            · ite_branch hbv_144
              step as ⟨e_v148, he_v148⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s30 e_v148 (by rw [he_v148]; exact empty_args) hinv30 h64 as ⟨v148, s31, hinv31, h_v148⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v140 h_v141 h_v142 h_v143 dropping he_v148 e_v148
              step as ⟨e_v149, he_v149⟩
              store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s31 e_v149 (by rw [he_v149]; rfl) h_v148 h_v7 hinv31 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v149, s32, hinv32, h_v149⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v140 h_v141 h_v142 h_v143 dropping h_v148 he_v149 e_v149 v148
              ite_done hinv32 hG with (eo_ite_false_rep _ hx_144 h_v149)
            · ite_branch hbv_144
              ite_stuck hinv30 hG with hx_144)
          store_step with h_ite_v150 as ⟨v150, s31, hinv31, h_v150⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v140 h_v141 h_v142 h_v143 dropping h_ite_v150
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s31 0#u32 (0) (by scalar_tac) hinv31 h64 as ⟨v151, s32, hinv32, h_v151⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v140 h_v141 h_v142 h_v143 h_v150 dropping
          step as ⟨e_v152, he_v152⟩
          store_step with Store.builtin_spec_list_nth n ih.eo__24eo_5fis_5flist_5fnil s32 e_v152 (by rw [he_v152]; rfl) h_v143 h_v150 h_v151 hinv32 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v152, s33, hinv33, h_v152⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v140 h_v141 h_v142 dropping h_v143 h_v150 h_v151 he_v152 e_v152 v143 v150 v151
          step as ⟨e_v153, he_v153⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s33 e_v153 (by rw [he_v153]; exact empty_args) hinv33 h64 as ⟨v153, s34, hinv34, h_v153⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v140 h_v141 h_v142 h_v152 dropping he_v153 e_v153
          have h_ite_v160 := (show if_10_eo__24eo_5fprog_5fconcat_5fsplit s34 a0 v4 ⦃ r s' => s'.Inv ∧ s34.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
            unfold if_10_eo__24eo_5fprog_5fconcat_5fsplit
            have hrem := (hG.rem hrem)
            have hG := Store.Grows.refl s34
            rcases Store.boolean_value_term h_a0 with ⟨hx_154, hbv_154⟩ | ⟨hx_154, hbv_154⟩ | ⟨hx_154, hbv_154⟩
            · ite_branch hbv_154
              step as ⟨e_v154, he_v154⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s34 e_v154 (by rw [he_v154]; exact empty_args) hinv34 h64 as ⟨v154, s35, hinv35, h_v154⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v140 h_v141 h_v142 h_v152 h_v153 dropping he_v154 e_v154
              step as ⟨e_v155, he_v155⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s35 e_v155 (by rw [he_v155]; exact empty_args) hinv35 h64 as ⟨v155, s36, hinv36, h_v155⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v140 h_v141 h_v142 h_v152 h_v153 h_v154 dropping he_v155 e_v155
              step as ⟨e_v156, he_v156⟩
              store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s36 e_v156 (by rw [he_v156]; rfl) h_v155 h_v4 hinv36 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v156, s37, hinv37, h_v156⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v140 h_v141 h_v142 h_v152 h_v153 h_v154 dropping h_v155 he_v156 e_v156 v155
              step as ⟨e_v157, he_v157⟩
              store_step with Store.builtin_spec_list_rev n ih.eo__24eo_5fis_5flist_5fnil s37 e_v157 (by rw [he_v157]; rfl) h_v154 h_v156 hinv37 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v157, s38, hinv38, h_v157⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v140 h_v141 h_v142 h_v152 h_v153 dropping h_v154 h_v156 he_v157 e_v157 v154 v156
              ite_done hinv38 hG with (eo_ite_true_rep _ hx_154 h_v157)
            · ite_branch hbv_154
              step as ⟨e_v158, he_v158⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s34 e_v158 (by rw [he_v158]; exact empty_args) hinv34 h64 as ⟨v158, s35, hinv35, h_v158⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v140 h_v141 h_v142 h_v152 h_v153 dropping he_v158 e_v158
              step as ⟨e_v159, he_v159⟩
              store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s35 e_v159 (by rw [he_v159]; rfl) h_v158 h_v4 hinv35 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v159, s36, hinv36, h_v159⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v140 h_v141 h_v142 h_v152 h_v153 dropping h_v158 he_v159 e_v159 v158
              ite_done hinv36 hG with (eo_ite_false_rep _ hx_154 h_v159)
            · ite_branch hbv_154
              ite_stuck hinv34 hG with hx_154)
          store_step with h_ite_v160 as ⟨v160, s35, hinv35, h_v160⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v140 h_v141 h_v142 h_v152 h_v153 dropping h_ite_v160
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s35 0#u32 (0) (by scalar_tac) hinv35 h64 as ⟨v161, s36, hinv36, h_v161⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v140 h_v141 h_v142 h_v152 h_v153 h_v160 dropping
          step as ⟨e_v162, he_v162⟩
          store_step with Store.builtin_spec_list_nth n ih.eo__24eo_5fis_5flist_5fnil s36 e_v162 (by rw [he_v162]; rfl) h_v153 h_v160 h_v161 hinv36 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v162, s37, hinv37, h_v162⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v140 h_v141 h_v142 h_v152 dropping h_v153 h_v160 h_v161 he_v162 e_v162 v153 v160 v161
          store_step with ih.eo__24str_5funify_5fsplit s37 v152 v162 a0 _ _ _ hinv37 h64 (hG.rem hrem) h_v152 h_v162 h_a0 as ⟨v163, s38, hinv38, h_v163⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v140 h_v141 h_v142 dropping h_v152 h_v162 v152 v162
          store_step with Store.apply_mk_rep s38 v142 v163 _ _ hinv38 h64 h_v142 h_v163 as ⟨v164, s39, hinv39, h_v164⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v140 h_v141 dropping h_v142 h_v163 v142 v163
          store_step with Store.apply_mk_rep s39 v141 v164 _ _ hinv39 h64 h_v141 h_v164 as ⟨v165, s40, hinv40, h_v165⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v140 dropping h_v141 h_v164 v141 v164
          step as ⟨e_v166, he_v166⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s40 e_v166 (by rw [he_v166]; exact empty_args) hinv40 h64 as ⟨v166, s41, hinv41, h_v166⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v140 h_v165 dropping he_v166 e_v166
          step as ⟨e_v167, he_v167⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s41 e_v167 (by rw [he_v167]; exact empty_args) hinv41 h64 as ⟨v167, s42, hinv42, h_v167⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v140 h_v165 h_v166 dropping he_v167 e_v167
          have h_ite_v174 := (show if_11_eo__24eo_5fprog_5fconcat_5fsplit s42 a0 v4 ⦃ r s' => s'.Inv ∧ s42.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
            unfold if_11_eo__24eo_5fprog_5fconcat_5fsplit
            have hrem := (hG.rem hrem)
            have hG := Store.Grows.refl s42
            rcases Store.boolean_value_term h_a0 with ⟨hx_168, hbv_168⟩ | ⟨hx_168, hbv_168⟩ | ⟨hx_168, hbv_168⟩
            · ite_branch hbv_168
              step as ⟨e_v168, he_v168⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s42 e_v168 (by rw [he_v168]; exact empty_args) hinv42 h64 as ⟨v168, s43, hinv43, h_v168⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v140 h_v165 h_v166 h_v167 dropping he_v168 e_v168
              step as ⟨e_v169, he_v169⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s43 e_v169 (by rw [he_v169]; exact empty_args) hinv43 h64 as ⟨v169, s44, hinv44, h_v169⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v140 h_v165 h_v166 h_v167 h_v168 dropping he_v169 e_v169
              step as ⟨e_v170, he_v170⟩
              store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s44 e_v170 (by rw [he_v170]; rfl) h_v169 h_v4 hinv44 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v170, s45, hinv45, h_v170⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v140 h_v165 h_v166 h_v167 h_v168 dropping h_v169 he_v170 e_v170 v169
              step as ⟨e_v171, he_v171⟩
              store_step with Store.builtin_spec_list_rev n ih.eo__24eo_5fis_5flist_5fnil s45 e_v171 (by rw [he_v171]; rfl) h_v168 h_v170 hinv45 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v171, s46, hinv46, h_v171⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v140 h_v165 h_v166 h_v167 dropping h_v168 h_v170 he_v171 e_v171 v168 v170
              ite_done hinv46 hG with (eo_ite_true_rep _ hx_168 h_v171)
            · ite_branch hbv_168
              step as ⟨e_v172, he_v172⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s42 e_v172 (by rw [he_v172]; exact empty_args) hinv42 h64 as ⟨v172, s43, hinv43, h_v172⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v140 h_v165 h_v166 h_v167 dropping he_v172 e_v172
              step as ⟨e_v173, he_v173⟩
              store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s43 e_v173 (by rw [he_v173]; rfl) h_v172 h_v4 hinv43 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v173, s44, hinv44, h_v173⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v140 h_v165 h_v166 h_v167 dropping h_v172 he_v173 e_v173 v172
              ite_done hinv44 hG with (eo_ite_false_rep _ hx_168 h_v173)
            · ite_branch hbv_168
              ite_stuck hinv42 hG with hx_168)
          store_step with h_ite_v174 as ⟨v174, s43, hinv43, h_v174⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v140 h_v165 h_v166 h_v167 dropping h_ite_v174
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s43 0#u32 (0) (by scalar_tac) hinv43 h64 as ⟨v175, s44, hinv44, h_v175⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v140 h_v165 h_v166 h_v167 h_v174 dropping
          step as ⟨e_v176, he_v176⟩
          store_step with Store.builtin_spec_list_nth n ih.eo__24eo_5fis_5flist_5fnil s44 e_v176 (by rw [he_v176]; rfl) h_v167 h_v174 h_v175 hinv44 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v176, s45, hinv45, h_v176⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v140 h_v165 h_v166 dropping h_v167 h_v174 h_v175 he_v176 e_v176 v167 v174 v175
          store_step with ih.eo__24eo_5ftypeof s45 v176 _ hinv45 h64 (hG.rem hrem) h_v176 as ⟨v177, s46, hinv46, h_v177⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v140 h_v165 h_v166 dropping h_v176 v176
          store_step with ih.eo__24eo_5fnil s46 v166 v177 _ _ hinv46 h64 (hG.rem hrem) h_v166 h_v177 as ⟨v178, s47, hinv47, h_v178⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v140 h_v165 dropping h_v166 h_v177 v166 v177
          store_step with Store.apply_mk_rep s47 v165 v178 _ _ hinv47 h64 h_v165 h_v178 as ⟨v179, s48, hinv48, h_v179⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 h_v140 dropping h_v165 h_v178 v165 v178
          store_step with Store.apply_mk_rep s48 v140 v179 _ _ hinv48 h64 h_v140 h_v179 as ⟨v180, s49, hinv49, h_v180⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 dropping h_v140 h_v179 v140 v179
          ite_done hinv49 hG with (eo_ite_false_rep _ hx_64 h_v180)
        · ite_branch hbv_64
          ite_stuck hinv21 hG with hx_64)
      store_step with h_ite_v181 as ⟨v181, s22, hinv22, h_v181⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 h_v63 dropping h_ite_v181 hinv21 s21
      store_step with Store.apply_mk_rep s22 v63 v181 _ _ hinv22 h64 h_v63 h_v181 as ⟨v182, s23, hinv23, h_v182⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v51 dropping h_v181 h_v63 hinv22 s22 v181 v63
      store_step with Store.apply_mk_rep s23 v51 v182 _ _ hinv23 h64 h_v51 h_v182 as ⟨v183, s24, hinv24, h_v183⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 dropping h_v182 h_v51 hinv23 s23 v182 v51
      step as ⟨e_v184, he_v184⟩
      store_step with CtorSpec.eo_or.construct s24 e_v184 (by rw [he_v184]; exact empty_args) hinv24 h64 as ⟨v184, s25, hinv25, h_v184⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 dropping he_v184 hinv24 e_v184 s24
      step as ⟨e_v185, he_v185⟩
      store_step with CtorSpec.eo__3d.construct s25 e_v185 (by rw [he_v185]; exact empty_args) hinv25 h64 as ⟨v185, s26, hinv26, h_v185⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 dropping he_v185 hinv25 e_v185 s25
      step as ⟨e_v186, he_v186⟩
      store_step with CtorSpec.eo_str_2e_2b_2b.construct s26 e_v186 (by rw [he_v186]; exact empty_args) hinv26 h64 as ⟨v186, s27, hinv27, h_v186⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v185 dropping he_v186 hinv26 e_v186 s26
      have h_ite_v193 := (show if_17_eo__24eo_5fprog_5fconcat_5fsplit s27 a0 v4 ⦃ r s' => s'.Inv ∧ s27.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_17_eo__24eo_5fprog_5fconcat_5fsplit
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s27
        rcases Store.boolean_value_term h_a0 with ⟨hx_187, hbv_187⟩ | ⟨hx_187, hbv_187⟩ | ⟨hx_187, hbv_187⟩
        · ite_branch hbv_187
          step as ⟨e_v187, he_v187⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s27 e_v187 (by rw [he_v187]; exact empty_args) hinv27 h64 as ⟨v187, s28, hinv28, h_v187⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v185 h_v186 dropping he_v187 e_v187
          step as ⟨e_v188, he_v188⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s28 e_v188 (by rw [he_v188]; exact empty_args) hinv28 h64 as ⟨v188, s29, hinv29, h_v188⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v185 h_v186 h_v187 dropping he_v188 e_v188
          step as ⟨e_v189, he_v189⟩
          store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s29 e_v189 (by rw [he_v189]; rfl) h_v188 h_v4 hinv29 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v189, s30, hinv30, h_v189⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v185 h_v186 h_v187 dropping h_v188 he_v189 e_v189 v188
          step as ⟨e_v190, he_v190⟩
          store_step with Store.builtin_spec_list_rev n ih.eo__24eo_5fis_5flist_5fnil s30 e_v190 (by rw [he_v190]; rfl) h_v187 h_v189 hinv30 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v190, s31, hinv31, h_v190⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v185 h_v186 dropping h_v187 h_v189 he_v190 e_v190 v187 v189
          ite_done hinv31 hG with (eo_ite_true_rep _ hx_187 h_v190)
        · ite_branch hbv_187
          step as ⟨e_v191, he_v191⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s27 e_v191 (by rw [he_v191]; exact empty_args) hinv27 h64 as ⟨v191, s28, hinv28, h_v191⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v185 h_v186 dropping he_v191 e_v191
          step as ⟨e_v192, he_v192⟩
          store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s28 e_v192 (by rw [he_v192]; rfl) h_v191 h_v4 hinv28 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v192, s29, hinv29, h_v192⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v185 h_v186 dropping h_v191 he_v192 e_v192 v191
          ite_done hinv29 hG with (eo_ite_false_rep _ hx_187 h_v192)
        · ite_branch hbv_187
          ite_stuck hinv27 hG with hx_187)
      store_step with h_ite_v193 as ⟨v193, s28, hinv28, h_v193⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v185 h_v186 dropping h_ite_v193 hinv27 s27
      try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
      store_step with Store.literal_int_u32_spec s28 0#u32 (0) (by scalar_tac) hinv28 h64 as ⟨v194, s29, hinv29, h_v194⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v185 h_v186 h_v193 dropping hinv28 s28
      step as ⟨e_v195, he_v195⟩
      store_step with Store.builtin_spec_list_nth n ih.eo__24eo_5fis_5flist_5fnil s29 e_v195 (by rw [he_v195]; rfl) h_v186 h_v193 h_v194 hinv29 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v195, s30, hinv30, h_v195⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v185 dropping h_v186 h_v193 h_v194 he_v195 hinv29 e_v195 s29 v186 v193 v194
      store_step with Store.apply_mk_rep s30 v185 v195 _ _ hinv30 h64 h_v185 h_v195 as ⟨v196, s31, hinv31, h_v196⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 dropping h_v185 h_v195 hinv30 s30 v185 v195
      have h_ite_v314 := (show if_31_eo__24eo_5fprog_5fconcat_5fsplit s31 a0 a0 v7 v4 ⦃ r s' => s'.Inv ∧ s31.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_31_eo__24eo_5fprog_5fconcat_5fsplit
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s31
        rcases Store.boolean_value_term h_a0 with ⟨hx_197, hbv_197⟩ | ⟨hx_197, hbv_197⟩ | ⟨hx_197, hbv_197⟩
        · ite_branch hbv_197
          step as ⟨e_v197, he_v197⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s31 e_v197 (by rw [he_v197]; exact empty_args) hinv31 h64 as ⟨v197, s32, hinv32, h_v197⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 dropping he_v197 e_v197
          step as ⟨e_v198, he_v198⟩
          store_step with CtorSpec.eo__40purify.construct s32 e_v198 (by rw [he_v198]; exact empty_args) hinv32 h64 as ⟨v198, s33, hinv33, h_v198⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v197 dropping he_v198 e_v198
          step as ⟨e_v199, he_v199⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s33 e_v199 (by rw [he_v199]; exact empty_args) hinv33 h64 as ⟨v199, s34, hinv34, h_v199⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v197 h_v198 dropping he_v199 e_v199
          have h_ite_v206 := (show if_18_eo__24eo_5fprog_5fconcat_5fsplit s34 a0 v7 ⦃ r s' => s'.Inv ∧ s34.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
            unfold if_18_eo__24eo_5fprog_5fconcat_5fsplit
            have hrem := (hG.rem hrem)
            have hG := Store.Grows.refl s34
            rcases Store.boolean_value_term h_a0 with ⟨hx_200, hbv_200⟩ | ⟨hx_200, hbv_200⟩ | ⟨hx_200, hbv_200⟩
            · ite_branch hbv_200
              step as ⟨e_v200, he_v200⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s34 e_v200 (by rw [he_v200]; exact empty_args) hinv34 h64 as ⟨v200, s35, hinv35, h_v200⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v197 h_v198 h_v199 dropping he_v200 e_v200
              step as ⟨e_v201, he_v201⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s35 e_v201 (by rw [he_v201]; exact empty_args) hinv35 h64 as ⟨v201, s36, hinv36, h_v201⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v197 h_v198 h_v199 h_v200 dropping he_v201 e_v201
              step as ⟨e_v202, he_v202⟩
              store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s36 e_v202 (by rw [he_v202]; rfl) h_v201 h_v7 hinv36 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v202, s37, hinv37, h_v202⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v197 h_v198 h_v199 h_v200 dropping h_v201 he_v202 e_v202 v201
              step as ⟨e_v203, he_v203⟩
              store_step with Store.builtin_spec_list_rev n ih.eo__24eo_5fis_5flist_5fnil s37 e_v203 (by rw [he_v203]; rfl) h_v200 h_v202 hinv37 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v203, s38, hinv38, h_v203⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v197 h_v198 h_v199 dropping h_v200 h_v202 he_v203 e_v203 v200 v202
              ite_done hinv38 hG with (eo_ite_true_rep _ hx_200 h_v203)
            · ite_branch hbv_200
              step as ⟨e_v204, he_v204⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s34 e_v204 (by rw [he_v204]; exact empty_args) hinv34 h64 as ⟨v204, s35, hinv35, h_v204⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v197 h_v198 h_v199 dropping he_v204 e_v204
              step as ⟨e_v205, he_v205⟩
              store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s35 e_v205 (by rw [he_v205]; rfl) h_v204 h_v7 hinv35 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v205, s36, hinv36, h_v205⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v197 h_v198 h_v199 dropping h_v204 he_v205 e_v205 v204
              ite_done hinv36 hG with (eo_ite_false_rep _ hx_200 h_v205)
            · ite_branch hbv_200
              ite_stuck hinv34 hG with hx_200)
          store_step with h_ite_v206 as ⟨v206, s35, hinv35, h_v206⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v197 h_v198 h_v199 dropping h_ite_v206
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s35 0#u32 (0) (by scalar_tac) hinv35 h64 as ⟨v207, s36, hinv36, h_v207⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v197 h_v198 h_v199 h_v206 dropping
          step as ⟨e_v208, he_v208⟩
          store_step with Store.builtin_spec_list_nth n ih.eo__24eo_5fis_5flist_5fnil s36 e_v208 (by rw [he_v208]; rfl) h_v199 h_v206 h_v207 hinv36 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v208, s37, hinv37, h_v208⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v197 h_v198 dropping h_v199 h_v206 h_v207 he_v208 e_v208 v199 v206 v207
          step as ⟨e_v209, he_v209⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s37 e_v209 (by rw [he_v209]; exact empty_args) hinv37 h64 as ⟨v209, s38, hinv38, h_v209⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v197 h_v198 h_v208 dropping he_v209 e_v209
          have h_ite_v216 := (show if_19_eo__24eo_5fprog_5fconcat_5fsplit s38 a0 v4 ⦃ r s' => s'.Inv ∧ s38.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
            unfold if_19_eo__24eo_5fprog_5fconcat_5fsplit
            have hrem := (hG.rem hrem)
            have hG := Store.Grows.refl s38
            rcases Store.boolean_value_term h_a0 with ⟨hx_210, hbv_210⟩ | ⟨hx_210, hbv_210⟩ | ⟨hx_210, hbv_210⟩
            · ite_branch hbv_210
              step as ⟨e_v210, he_v210⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s38 e_v210 (by rw [he_v210]; exact empty_args) hinv38 h64 as ⟨v210, s39, hinv39, h_v210⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v197 h_v198 h_v208 h_v209 dropping he_v210 e_v210
              step as ⟨e_v211, he_v211⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s39 e_v211 (by rw [he_v211]; exact empty_args) hinv39 h64 as ⟨v211, s40, hinv40, h_v211⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v197 h_v198 h_v208 h_v209 h_v210 dropping he_v211 e_v211
              step as ⟨e_v212, he_v212⟩
              store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s40 e_v212 (by rw [he_v212]; rfl) h_v211 h_v4 hinv40 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v212, s41, hinv41, h_v212⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v197 h_v198 h_v208 h_v209 h_v210 dropping h_v211 he_v212 e_v212 v211
              step as ⟨e_v213, he_v213⟩
              store_step with Store.builtin_spec_list_rev n ih.eo__24eo_5fis_5flist_5fnil s41 e_v213 (by rw [he_v213]; rfl) h_v210 h_v212 hinv41 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v213, s42, hinv42, h_v213⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v197 h_v198 h_v208 h_v209 dropping h_v210 h_v212 he_v213 e_v213 v210 v212
              ite_done hinv42 hG with (eo_ite_true_rep _ hx_210 h_v213)
            · ite_branch hbv_210
              step as ⟨e_v214, he_v214⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s38 e_v214 (by rw [he_v214]; exact empty_args) hinv38 h64 as ⟨v214, s39, hinv39, h_v214⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v197 h_v198 h_v208 h_v209 dropping he_v214 e_v214
              step as ⟨e_v215, he_v215⟩
              store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s39 e_v215 (by rw [he_v215]; rfl) h_v214 h_v4 hinv39 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v215, s40, hinv40, h_v215⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v197 h_v198 h_v208 h_v209 dropping h_v214 he_v215 e_v215 v214
              ite_done hinv40 hG with (eo_ite_false_rep _ hx_210 h_v215)
            · ite_branch hbv_210
              ite_stuck hinv38 hG with hx_210)
          store_step with h_ite_v216 as ⟨v216, s39, hinv39, h_v216⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v197 h_v198 h_v208 h_v209 dropping h_ite_v216
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s39 0#u32 (0) (by scalar_tac) hinv39 h64 as ⟨v217, s40, hinv40, h_v217⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v197 h_v198 h_v208 h_v209 h_v216 dropping
          step as ⟨e_v218, he_v218⟩
          store_step with Store.builtin_spec_list_nth n ih.eo__24eo_5fis_5flist_5fnil s40 e_v218 (by rw [he_v218]; rfl) h_v209 h_v216 h_v217 hinv40 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v218, s41, hinv41, h_v218⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v197 h_v198 h_v208 dropping h_v209 h_v216 h_v217 he_v218 e_v218 v209 v216 v217
          store_step with ih.eo__24str_5funify_5fsplit s41 v208 v218 a0 _ _ _ hinv41 h64 (hG.rem hrem) h_v208 h_v218 h_a0 as ⟨v219, s42, hinv42, h_v219⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v197 h_v198 dropping h_v208 h_v218 v208 v218
          store_step with Store.apply_mk_rep s42 v198 v219 _ _ hinv42 h64 h_v198 h_v219 as ⟨v220, s43, hinv43, h_v220⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v197 dropping h_v198 h_v219 v198 v219
          store_step with Store.apply_mk_rep s43 v197 v220 _ _ hinv43 h64 h_v197 h_v220 as ⟨v221, s44, hinv44, h_v221⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 dropping h_v197 h_v220 v197 v220
          step as ⟨e_v222, he_v222⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s44 e_v222 (by rw [he_v222]; exact empty_args) hinv44 h64 as ⟨v222, s45, hinv45, h_v222⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v221 dropping he_v222 e_v222
          step as ⟨e_v223, he_v223⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s45 e_v223 (by rw [he_v223]; exact empty_args) hinv45 h64 as ⟨v223, s46, hinv46, h_v223⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v221 h_v222 dropping he_v223 e_v223
          have h_ite_v230 := (show if_20_eo__24eo_5fprog_5fconcat_5fsplit s46 a0 v7 ⦃ r s' => s'.Inv ∧ s46.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
            unfold if_20_eo__24eo_5fprog_5fconcat_5fsplit
            have hrem := (hG.rem hrem)
            have hG := Store.Grows.refl s46
            rcases Store.boolean_value_term h_a0 with ⟨hx_224, hbv_224⟩ | ⟨hx_224, hbv_224⟩ | ⟨hx_224, hbv_224⟩
            · ite_branch hbv_224
              step as ⟨e_v224, he_v224⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s46 e_v224 (by rw [he_v224]; exact empty_args) hinv46 h64 as ⟨v224, s47, hinv47, h_v224⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v221 h_v222 h_v223 dropping he_v224 e_v224
              step as ⟨e_v225, he_v225⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s47 e_v225 (by rw [he_v225]; exact empty_args) hinv47 h64 as ⟨v225, s48, hinv48, h_v225⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v221 h_v222 h_v223 h_v224 dropping he_v225 e_v225
              step as ⟨e_v226, he_v226⟩
              store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s48 e_v226 (by rw [he_v226]; rfl) h_v225 h_v7 hinv48 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v226, s49, hinv49, h_v226⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v221 h_v222 h_v223 h_v224 dropping h_v225 he_v226 e_v226 v225
              step as ⟨e_v227, he_v227⟩
              store_step with Store.builtin_spec_list_rev n ih.eo__24eo_5fis_5flist_5fnil s49 e_v227 (by rw [he_v227]; rfl) h_v224 h_v226 hinv49 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v227, s50, hinv50, h_v227⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v221 h_v222 h_v223 dropping h_v224 h_v226 he_v227 e_v227 v224 v226
              ite_done hinv50 hG with (eo_ite_true_rep _ hx_224 h_v227)
            · ite_branch hbv_224
              step as ⟨e_v228, he_v228⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s46 e_v228 (by rw [he_v228]; exact empty_args) hinv46 h64 as ⟨v228, s47, hinv47, h_v228⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v221 h_v222 h_v223 dropping he_v228 e_v228
              step as ⟨e_v229, he_v229⟩
              store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s47 e_v229 (by rw [he_v229]; rfl) h_v228 h_v7 hinv47 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v229, s48, hinv48, h_v229⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v221 h_v222 h_v223 dropping h_v228 he_v229 e_v229 v228
              ite_done hinv48 hG with (eo_ite_false_rep _ hx_224 h_v229)
            · ite_branch hbv_224
              ite_stuck hinv46 hG with hx_224)
          store_step with h_ite_v230 as ⟨v230, s47, hinv47, h_v230⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v221 h_v222 h_v223 dropping h_ite_v230
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s47 0#u32 (0) (by scalar_tac) hinv47 h64 as ⟨v231, s48, hinv48, h_v231⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v221 h_v222 h_v223 h_v230 dropping
          step as ⟨e_v232, he_v232⟩
          store_step with Store.builtin_spec_list_nth n ih.eo__24eo_5fis_5flist_5fnil s48 e_v232 (by rw [he_v232]; rfl) h_v223 h_v230 h_v231 hinv48 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v232, s49, hinv49, h_v232⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v221 h_v222 dropping h_v223 h_v230 h_v231 he_v232 e_v232 v223 v230 v231
          store_step with Store.apply_mk_rep s49 v222 v232 _ _ hinv49 h64 h_v222 h_v232 as ⟨v233, s50, hinv50, h_v233⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v221 dropping h_v222 h_v232 v222 v232
          step as ⟨e_v234, he_v234⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s50 e_v234 (by rw [he_v234]; exact empty_args) hinv50 h64 as ⟨v234, s51, hinv51, h_v234⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v221 h_v233 dropping he_v234 e_v234
          step as ⟨e_v235, he_v235⟩
          store_step with CtorSpec.eo__40purify.construct s51 e_v235 (by rw [he_v235]; exact empty_args) hinv51 h64 as ⟨v235, s52, hinv52, h_v235⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v221 h_v233 h_v234 dropping he_v235 e_v235
          step as ⟨e_v236, he_v236⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s52 e_v236 (by rw [he_v236]; exact empty_args) hinv52 h64 as ⟨v236, s53, hinv53, h_v236⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v221 h_v233 h_v234 h_v235 dropping he_v236 e_v236
          have h_ite_v243 := (show if_21_eo__24eo_5fprog_5fconcat_5fsplit s53 a0 v7 ⦃ r s' => s'.Inv ∧ s53.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
            unfold if_21_eo__24eo_5fprog_5fconcat_5fsplit
            have hrem := (hG.rem hrem)
            have hG := Store.Grows.refl s53
            rcases Store.boolean_value_term h_a0 with ⟨hx_237, hbv_237⟩ | ⟨hx_237, hbv_237⟩ | ⟨hx_237, hbv_237⟩
            · ite_branch hbv_237
              step as ⟨e_v237, he_v237⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s53 e_v237 (by rw [he_v237]; exact empty_args) hinv53 h64 as ⟨v237, s54, hinv54, h_v237⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v221 h_v233 h_v234 h_v235 h_v236 dropping he_v237 e_v237
              step as ⟨e_v238, he_v238⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s54 e_v238 (by rw [he_v238]; exact empty_args) hinv54 h64 as ⟨v238, s55, hinv55, h_v238⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v221 h_v233 h_v234 h_v235 h_v236 h_v237 dropping he_v238 e_v238
              step as ⟨e_v239, he_v239⟩
              store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s55 e_v239 (by rw [he_v239]; rfl) h_v238 h_v7 hinv55 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v239, s56, hinv56, h_v239⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v221 h_v233 h_v234 h_v235 h_v236 h_v237 dropping h_v238 he_v239 e_v239 v238
              step as ⟨e_v240, he_v240⟩
              store_step with Store.builtin_spec_list_rev n ih.eo__24eo_5fis_5flist_5fnil s56 e_v240 (by rw [he_v240]; rfl) h_v237 h_v239 hinv56 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v240, s57, hinv57, h_v240⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v221 h_v233 h_v234 h_v235 h_v236 dropping h_v237 h_v239 he_v240 e_v240 v237 v239
              ite_done hinv57 hG with (eo_ite_true_rep _ hx_237 h_v240)
            · ite_branch hbv_237
              step as ⟨e_v241, he_v241⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s53 e_v241 (by rw [he_v241]; exact empty_args) hinv53 h64 as ⟨v241, s54, hinv54, h_v241⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v221 h_v233 h_v234 h_v235 h_v236 dropping he_v241 e_v241
              step as ⟨e_v242, he_v242⟩
              store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s54 e_v242 (by rw [he_v242]; rfl) h_v241 h_v7 hinv54 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v242, s55, hinv55, h_v242⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v221 h_v233 h_v234 h_v235 h_v236 dropping h_v241 he_v242 e_v242 v241
              ite_done hinv55 hG with (eo_ite_false_rep _ hx_237 h_v242)
            · ite_branch hbv_237
              ite_stuck hinv53 hG with hx_237)
          store_step with h_ite_v243 as ⟨v243, s54, hinv54, h_v243⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v221 h_v233 h_v234 h_v235 h_v236 dropping h_ite_v243
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s54 0#u32 (0) (by scalar_tac) hinv54 h64 as ⟨v244, s55, hinv55, h_v244⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v221 h_v233 h_v234 h_v235 h_v236 h_v243 dropping
          step as ⟨e_v245, he_v245⟩
          store_step with Store.builtin_spec_list_nth n ih.eo__24eo_5fis_5flist_5fnil s55 e_v245 (by rw [he_v245]; rfl) h_v236 h_v243 h_v244 hinv55 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v245, s56, hinv56, h_v245⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v221 h_v233 h_v234 h_v235 dropping h_v236 h_v243 h_v244 he_v245 e_v245 v236 v243 v244
          step as ⟨e_v246, he_v246⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s56 e_v246 (by rw [he_v246]; exact empty_args) hinv56 h64 as ⟨v246, s57, hinv57, h_v246⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v221 h_v233 h_v234 h_v235 h_v245 dropping he_v246 e_v246
          have h_ite_v253 := (show if_22_eo__24eo_5fprog_5fconcat_5fsplit s57 a0 v4 ⦃ r s' => s'.Inv ∧ s57.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
            unfold if_22_eo__24eo_5fprog_5fconcat_5fsplit
            have hrem := (hG.rem hrem)
            have hG := Store.Grows.refl s57
            rcases Store.boolean_value_term h_a0 with ⟨hx_247, hbv_247⟩ | ⟨hx_247, hbv_247⟩ | ⟨hx_247, hbv_247⟩
            · ite_branch hbv_247
              step as ⟨e_v247, he_v247⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s57 e_v247 (by rw [he_v247]; exact empty_args) hinv57 h64 as ⟨v247, s58, hinv58, h_v247⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v221 h_v233 h_v234 h_v235 h_v245 h_v246 dropping he_v247 e_v247
              step as ⟨e_v248, he_v248⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s58 e_v248 (by rw [he_v248]; exact empty_args) hinv58 h64 as ⟨v248, s59, hinv59, h_v248⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v221 h_v233 h_v234 h_v235 h_v245 h_v246 h_v247 dropping he_v248 e_v248
              step as ⟨e_v249, he_v249⟩
              store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s59 e_v249 (by rw [he_v249]; rfl) h_v248 h_v4 hinv59 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v249, s60, hinv60, h_v249⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v221 h_v233 h_v234 h_v235 h_v245 h_v246 h_v247 dropping h_v248 he_v249 e_v249 v248
              step as ⟨e_v250, he_v250⟩
              store_step with Store.builtin_spec_list_rev n ih.eo__24eo_5fis_5flist_5fnil s60 e_v250 (by rw [he_v250]; rfl) h_v247 h_v249 hinv60 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v250, s61, hinv61, h_v250⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v221 h_v233 h_v234 h_v235 h_v245 h_v246 dropping h_v247 h_v249 he_v250 e_v250 v247 v249
              ite_done hinv61 hG with (eo_ite_true_rep _ hx_247 h_v250)
            · ite_branch hbv_247
              step as ⟨e_v251, he_v251⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s57 e_v251 (by rw [he_v251]; exact empty_args) hinv57 h64 as ⟨v251, s58, hinv58, h_v251⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v221 h_v233 h_v234 h_v235 h_v245 h_v246 dropping he_v251 e_v251
              step as ⟨e_v252, he_v252⟩
              store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s58 e_v252 (by rw [he_v252]; rfl) h_v251 h_v4 hinv58 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v252, s59, hinv59, h_v252⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v221 h_v233 h_v234 h_v235 h_v245 h_v246 dropping h_v251 he_v252 e_v252 v251
              ite_done hinv59 hG with (eo_ite_false_rep _ hx_247 h_v252)
            · ite_branch hbv_247
              ite_stuck hinv57 hG with hx_247)
          store_step with h_ite_v253 as ⟨v253, s58, hinv58, h_v253⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v221 h_v233 h_v234 h_v235 h_v245 h_v246 dropping h_ite_v253
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s58 0#u32 (0) (by scalar_tac) hinv58 h64 as ⟨v254, s59, hinv59, h_v254⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v221 h_v233 h_v234 h_v235 h_v245 h_v246 h_v253 dropping
          step as ⟨e_v255, he_v255⟩
          store_step with Store.builtin_spec_list_nth n ih.eo__24eo_5fis_5flist_5fnil s59 e_v255 (by rw [he_v255]; rfl) h_v246 h_v253 h_v254 hinv59 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v255, s60, hinv60, h_v255⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v221 h_v233 h_v234 h_v235 h_v245 dropping h_v246 h_v253 h_v254 he_v255 e_v255 v246 v253 v254
          store_step with ih.eo__24str_5funify_5fsplit s60 v245 v255 a0 _ _ _ hinv60 h64 (hG.rem hrem) h_v245 h_v255 h_a0 as ⟨v256, s61, hinv61, h_v256⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v221 h_v233 h_v234 h_v235 dropping h_v245 h_v255 v245 v255
          store_step with Store.apply_mk_rep s61 v235 v256 _ _ hinv61 h64 h_v235 h_v256 as ⟨v257, s62, hinv62, h_v257⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v221 h_v233 h_v234 dropping h_v235 h_v256 v235 v256
          store_step with ih.eo__24eo_5ftypeof s62 v257 _ hinv62 h64 (hG.rem hrem) h_v257 as ⟨v258, s63, hinv63, h_v258⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v221 h_v233 h_v234 dropping h_v257 v257
          store_step with ih.eo__24eo_5fnil s63 v234 v258 _ _ hinv63 h64 (hG.rem hrem) h_v234 h_v258 as ⟨v259, s64, hinv64, h_v259⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v221 h_v233 dropping h_v234 h_v258 v234 v258
          store_step with Store.apply_mk_rep s64 v233 v259 _ _ hinv64 h64 h_v233 h_v259 as ⟨v260, s65, hinv65, h_v260⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v221 dropping h_v233 h_v259 v233 v259
          store_step with Store.apply_mk_rep s65 v221 v260 _ _ hinv65 h64 h_v221 h_v260 as ⟨v261, s66, hinv66, h_v261⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 dropping h_v221 h_v260 v221 v260
          ite_done hinv66 hG with (eo_ite_true_rep _ hx_197 h_v261)
        · ite_branch hbv_197
          step as ⟨e_v262, he_v262⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s31 e_v262 (by rw [he_v262]; exact empty_args) hinv31 h64 as ⟨v262, s32, hinv32, h_v262⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 dropping he_v262 e_v262
          step as ⟨e_v263, he_v263⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s32 e_v263 (by rw [he_v263]; exact empty_args) hinv32 h64 as ⟨v263, s33, hinv33, h_v263⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v262 dropping he_v263 e_v263
          have h_ite_v270 := (show if_23_eo__24eo_5fprog_5fconcat_5fsplit s33 a0 v7 ⦃ r s' => s'.Inv ∧ s33.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
            unfold if_23_eo__24eo_5fprog_5fconcat_5fsplit
            have hrem := (hG.rem hrem)
            have hG := Store.Grows.refl s33
            rcases Store.boolean_value_term h_a0 with ⟨hx_264, hbv_264⟩ | ⟨hx_264, hbv_264⟩ | ⟨hx_264, hbv_264⟩
            · ite_branch hbv_264
              step as ⟨e_v264, he_v264⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s33 e_v264 (by rw [he_v264]; exact empty_args) hinv33 h64 as ⟨v264, s34, hinv34, h_v264⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v262 h_v263 dropping he_v264 e_v264
              step as ⟨e_v265, he_v265⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s34 e_v265 (by rw [he_v265]; exact empty_args) hinv34 h64 as ⟨v265, s35, hinv35, h_v265⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v262 h_v263 h_v264 dropping he_v265 e_v265
              step as ⟨e_v266, he_v266⟩
              store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s35 e_v266 (by rw [he_v266]; rfl) h_v265 h_v7 hinv35 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v266, s36, hinv36, h_v266⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v262 h_v263 h_v264 dropping h_v265 he_v266 e_v266 v265
              step as ⟨e_v267, he_v267⟩
              store_step with Store.builtin_spec_list_rev n ih.eo__24eo_5fis_5flist_5fnil s36 e_v267 (by rw [he_v267]; rfl) h_v264 h_v266 hinv36 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v267, s37, hinv37, h_v267⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v262 h_v263 dropping h_v264 h_v266 he_v267 e_v267 v264 v266
              ite_done hinv37 hG with (eo_ite_true_rep _ hx_264 h_v267)
            · ite_branch hbv_264
              step as ⟨e_v268, he_v268⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s33 e_v268 (by rw [he_v268]; exact empty_args) hinv33 h64 as ⟨v268, s34, hinv34, h_v268⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v262 h_v263 dropping he_v268 e_v268
              step as ⟨e_v269, he_v269⟩
              store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s34 e_v269 (by rw [he_v269]; rfl) h_v268 h_v7 hinv34 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v269, s35, hinv35, h_v269⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v262 h_v263 dropping h_v268 he_v269 e_v269 v268
              ite_done hinv35 hG with (eo_ite_false_rep _ hx_264 h_v269)
            · ite_branch hbv_264
              ite_stuck hinv33 hG with hx_264)
          store_step with h_ite_v270 as ⟨v270, s34, hinv34, h_v270⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v262 h_v263 dropping h_ite_v270
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s34 0#u32 (0) (by scalar_tac) hinv34 h64 as ⟨v271, s35, hinv35, h_v271⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v262 h_v263 h_v270 dropping
          step as ⟨e_v272, he_v272⟩
          store_step with Store.builtin_spec_list_nth n ih.eo__24eo_5fis_5flist_5fnil s35 e_v272 (by rw [he_v272]; rfl) h_v263 h_v270 h_v271 hinv35 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v272, s36, hinv36, h_v272⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v262 dropping h_v263 h_v270 h_v271 he_v272 e_v272 v263 v270 v271
          store_step with Store.apply_mk_rep s36 v262 v272 _ _ hinv36 h64 h_v262 h_v272 as ⟨v273, s37, hinv37, h_v273⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 dropping h_v262 h_v272 v262 v272
          step as ⟨e_v274, he_v274⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s37 e_v274 (by rw [he_v274]; exact empty_args) hinv37 h64 as ⟨v274, s38, hinv38, h_v274⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v273 dropping he_v274 e_v274
          step as ⟨e_v275, he_v275⟩
          store_step with CtorSpec.eo__40purify.construct s38 e_v275 (by rw [he_v275]; exact empty_args) hinv38 h64 as ⟨v275, s39, hinv39, h_v275⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v273 h_v274 dropping he_v275 e_v275
          step as ⟨e_v276, he_v276⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s39 e_v276 (by rw [he_v276]; exact empty_args) hinv39 h64 as ⟨v276, s40, hinv40, h_v276⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v273 h_v274 h_v275 dropping he_v276 e_v276
          have h_ite_v283 := (show if_24_eo__24eo_5fprog_5fconcat_5fsplit s40 a0 v7 ⦃ r s' => s'.Inv ∧ s40.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
            unfold if_24_eo__24eo_5fprog_5fconcat_5fsplit
            have hrem := (hG.rem hrem)
            have hG := Store.Grows.refl s40
            rcases Store.boolean_value_term h_a0 with ⟨hx_277, hbv_277⟩ | ⟨hx_277, hbv_277⟩ | ⟨hx_277, hbv_277⟩
            · ite_branch hbv_277
              step as ⟨e_v277, he_v277⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s40 e_v277 (by rw [he_v277]; exact empty_args) hinv40 h64 as ⟨v277, s41, hinv41, h_v277⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v273 h_v274 h_v275 h_v276 dropping he_v277 e_v277
              step as ⟨e_v278, he_v278⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s41 e_v278 (by rw [he_v278]; exact empty_args) hinv41 h64 as ⟨v278, s42, hinv42, h_v278⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v273 h_v274 h_v275 h_v276 h_v277 dropping he_v278 e_v278
              step as ⟨e_v279, he_v279⟩
              store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s42 e_v279 (by rw [he_v279]; rfl) h_v278 h_v7 hinv42 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v279, s43, hinv43, h_v279⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v273 h_v274 h_v275 h_v276 h_v277 dropping h_v278 he_v279 e_v279 v278
              step as ⟨e_v280, he_v280⟩
              store_step with Store.builtin_spec_list_rev n ih.eo__24eo_5fis_5flist_5fnil s43 e_v280 (by rw [he_v280]; rfl) h_v277 h_v279 hinv43 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v280, s44, hinv44, h_v280⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v273 h_v274 h_v275 h_v276 dropping h_v277 h_v279 he_v280 e_v280 v277 v279
              ite_done hinv44 hG with (eo_ite_true_rep _ hx_277 h_v280)
            · ite_branch hbv_277
              step as ⟨e_v281, he_v281⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s40 e_v281 (by rw [he_v281]; exact empty_args) hinv40 h64 as ⟨v281, s41, hinv41, h_v281⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v273 h_v274 h_v275 h_v276 dropping he_v281 e_v281
              step as ⟨e_v282, he_v282⟩
              store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s41 e_v282 (by rw [he_v282]; rfl) h_v281 h_v7 hinv41 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v282, s42, hinv42, h_v282⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v273 h_v274 h_v275 h_v276 dropping h_v281 he_v282 e_v282 v281
              ite_done hinv42 hG with (eo_ite_false_rep _ hx_277 h_v282)
            · ite_branch hbv_277
              ite_stuck hinv40 hG with hx_277)
          store_step with h_ite_v283 as ⟨v283, s41, hinv41, h_v283⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v273 h_v274 h_v275 h_v276 dropping h_ite_v283
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s41 0#u32 (0) (by scalar_tac) hinv41 h64 as ⟨v284, s42, hinv42, h_v284⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v273 h_v274 h_v275 h_v276 h_v283 dropping
          step as ⟨e_v285, he_v285⟩
          store_step with Store.builtin_spec_list_nth n ih.eo__24eo_5fis_5flist_5fnil s42 e_v285 (by rw [he_v285]; rfl) h_v276 h_v283 h_v284 hinv42 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v285, s43, hinv43, h_v285⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v273 h_v274 h_v275 dropping h_v276 h_v283 h_v284 he_v285 e_v285 v276 v283 v284
          step as ⟨e_v286, he_v286⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s43 e_v286 (by rw [he_v286]; exact empty_args) hinv43 h64 as ⟨v286, s44, hinv44, h_v286⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v273 h_v274 h_v275 h_v285 dropping he_v286 e_v286
          have h_ite_v293 := (show if_25_eo__24eo_5fprog_5fconcat_5fsplit s44 a0 v4 ⦃ r s' => s'.Inv ∧ s44.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
            unfold if_25_eo__24eo_5fprog_5fconcat_5fsplit
            have hrem := (hG.rem hrem)
            have hG := Store.Grows.refl s44
            rcases Store.boolean_value_term h_a0 with ⟨hx_287, hbv_287⟩ | ⟨hx_287, hbv_287⟩ | ⟨hx_287, hbv_287⟩
            · ite_branch hbv_287
              step as ⟨e_v287, he_v287⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s44 e_v287 (by rw [he_v287]; exact empty_args) hinv44 h64 as ⟨v287, s45, hinv45, h_v287⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v273 h_v274 h_v275 h_v285 h_v286 dropping he_v287 e_v287
              step as ⟨e_v288, he_v288⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s45 e_v288 (by rw [he_v288]; exact empty_args) hinv45 h64 as ⟨v288, s46, hinv46, h_v288⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v273 h_v274 h_v275 h_v285 h_v286 h_v287 dropping he_v288 e_v288
              step as ⟨e_v289, he_v289⟩
              store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s46 e_v289 (by rw [he_v289]; rfl) h_v288 h_v4 hinv46 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v289, s47, hinv47, h_v289⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v273 h_v274 h_v275 h_v285 h_v286 h_v287 dropping h_v288 he_v289 e_v289 v288
              step as ⟨e_v290, he_v290⟩
              store_step with Store.builtin_spec_list_rev n ih.eo__24eo_5fis_5flist_5fnil s47 e_v290 (by rw [he_v290]; rfl) h_v287 h_v289 hinv47 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v290, s48, hinv48, h_v290⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v273 h_v274 h_v275 h_v285 h_v286 dropping h_v287 h_v289 he_v290 e_v290 v287 v289
              ite_done hinv48 hG with (eo_ite_true_rep _ hx_287 h_v290)
            · ite_branch hbv_287
              step as ⟨e_v291, he_v291⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s44 e_v291 (by rw [he_v291]; exact empty_args) hinv44 h64 as ⟨v291, s45, hinv45, h_v291⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v273 h_v274 h_v275 h_v285 h_v286 dropping he_v291 e_v291
              step as ⟨e_v292, he_v292⟩
              store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s45 e_v292 (by rw [he_v292]; rfl) h_v291 h_v4 hinv45 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v292, s46, hinv46, h_v292⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v273 h_v274 h_v275 h_v285 h_v286 dropping h_v291 he_v292 e_v292 v291
              ite_done hinv46 hG with (eo_ite_false_rep _ hx_287 h_v292)
            · ite_branch hbv_287
              ite_stuck hinv44 hG with hx_287)
          store_step with h_ite_v293 as ⟨v293, s45, hinv45, h_v293⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v273 h_v274 h_v275 h_v285 h_v286 dropping h_ite_v293
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s45 0#u32 (0) (by scalar_tac) hinv45 h64 as ⟨v294, s46, hinv46, h_v294⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v273 h_v274 h_v275 h_v285 h_v286 h_v293 dropping
          step as ⟨e_v295, he_v295⟩
          store_step with Store.builtin_spec_list_nth n ih.eo__24eo_5fis_5flist_5fnil s46 e_v295 (by rw [he_v295]; rfl) h_v286 h_v293 h_v294 hinv46 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v295, s47, hinv47, h_v295⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v273 h_v274 h_v275 h_v285 dropping h_v286 h_v293 h_v294 he_v295 e_v295 v286 v293 v294
          store_step with ih.eo__24str_5funify_5fsplit s47 v285 v295 a0 _ _ _ hinv47 h64 (hG.rem hrem) h_v285 h_v295 h_a0 as ⟨v296, s48, hinv48, h_v296⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v273 h_v274 h_v275 dropping h_v285 h_v295 v285 v295
          store_step with Store.apply_mk_rep s48 v275 v296 _ _ hinv48 h64 h_v275 h_v296 as ⟨v297, s49, hinv49, h_v297⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v273 h_v274 dropping h_v275 h_v296 v275 v296
          store_step with Store.apply_mk_rep s49 v274 v297 _ _ hinv49 h64 h_v274 h_v297 as ⟨v298, s50, hinv50, h_v298⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v273 dropping h_v274 h_v297 v274 v297
          step as ⟨e_v299, he_v299⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s50 e_v299 (by rw [he_v299]; exact empty_args) hinv50 h64 as ⟨v299, s51, hinv51, h_v299⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v273 h_v298 dropping he_v299 e_v299
          step as ⟨e_v300, he_v300⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s51 e_v300 (by rw [he_v300]; exact empty_args) hinv51 h64 as ⟨v300, s52, hinv52, h_v300⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v273 h_v298 h_v299 dropping he_v300 e_v300
          have h_ite_v307 := (show if_26_eo__24eo_5fprog_5fconcat_5fsplit s52 a0 v7 ⦃ r s' => s'.Inv ∧ s52.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
            unfold if_26_eo__24eo_5fprog_5fconcat_5fsplit
            have hrem := (hG.rem hrem)
            have hG := Store.Grows.refl s52
            rcases Store.boolean_value_term h_a0 with ⟨hx_301, hbv_301⟩ | ⟨hx_301, hbv_301⟩ | ⟨hx_301, hbv_301⟩
            · ite_branch hbv_301
              step as ⟨e_v301, he_v301⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s52 e_v301 (by rw [he_v301]; exact empty_args) hinv52 h64 as ⟨v301, s53, hinv53, h_v301⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v273 h_v298 h_v299 h_v300 dropping he_v301 e_v301
              step as ⟨e_v302, he_v302⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s53 e_v302 (by rw [he_v302]; exact empty_args) hinv53 h64 as ⟨v302, s54, hinv54, h_v302⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v273 h_v298 h_v299 h_v300 h_v301 dropping he_v302 e_v302
              step as ⟨e_v303, he_v303⟩
              store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s54 e_v303 (by rw [he_v303]; rfl) h_v302 h_v7 hinv54 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v303, s55, hinv55, h_v303⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v273 h_v298 h_v299 h_v300 h_v301 dropping h_v302 he_v303 e_v303 v302
              step as ⟨e_v304, he_v304⟩
              store_step with Store.builtin_spec_list_rev n ih.eo__24eo_5fis_5flist_5fnil s55 e_v304 (by rw [he_v304]; rfl) h_v301 h_v303 hinv55 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v304, s56, hinv56, h_v304⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v273 h_v298 h_v299 h_v300 dropping h_v301 h_v303 he_v304 e_v304 v301 v303
              ite_done hinv56 hG with (eo_ite_true_rep _ hx_301 h_v304)
            · ite_branch hbv_301
              step as ⟨e_v305, he_v305⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s52 e_v305 (by rw [he_v305]; exact empty_args) hinv52 h64 as ⟨v305, s53, hinv53, h_v305⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v273 h_v298 h_v299 h_v300 dropping he_v305 e_v305
              step as ⟨e_v306, he_v306⟩
              store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s53 e_v306 (by rw [he_v306]; rfl) h_v305 h_v7 hinv53 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v306, s54, hinv54, h_v306⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v273 h_v298 h_v299 h_v300 dropping h_v305 he_v306 e_v306 v305
              ite_done hinv54 hG with (eo_ite_false_rep _ hx_301 h_v306)
            · ite_branch hbv_301
              ite_stuck hinv52 hG with hx_301)
          store_step with h_ite_v307 as ⟨v307, s53, hinv53, h_v307⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v273 h_v298 h_v299 h_v300 dropping h_ite_v307
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s53 0#u32 (0) (by scalar_tac) hinv53 h64 as ⟨v308, s54, hinv54, h_v308⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v273 h_v298 h_v299 h_v300 h_v307 dropping
          step as ⟨e_v309, he_v309⟩
          store_step with Store.builtin_spec_list_nth n ih.eo__24eo_5fis_5flist_5fnil s54 e_v309 (by rw [he_v309]; rfl) h_v300 h_v307 h_v308 hinv54 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v309, s55, hinv55, h_v309⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v273 h_v298 h_v299 dropping h_v300 h_v307 h_v308 he_v309 e_v309 v300 v307 v308
          store_step with ih.eo__24eo_5ftypeof s55 v309 _ hinv55 h64 (hG.rem hrem) h_v309 as ⟨v310, s56, hinv56, h_v310⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v273 h_v298 h_v299 dropping h_v309 v309
          store_step with ih.eo__24eo_5fnil s56 v299 v310 _ _ hinv56 h64 (hG.rem hrem) h_v299 h_v310 as ⟨v311, s57, hinv57, h_v311⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v273 h_v298 dropping h_v299 h_v310 v299 v310
          store_step with Store.apply_mk_rep s57 v298 v311 _ _ hinv57 h64 h_v298 h_v311 as ⟨v312, s58, hinv58, h_v312⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 h_v273 dropping h_v298 h_v311 v298 v311
          store_step with Store.apply_mk_rep s58 v273 v312 _ _ hinv58 h64 h_v273 h_v312 as ⟨v313, s59, hinv59, h_v313⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 dropping h_v273 h_v312 v273 v312
          ite_done hinv59 hG with (eo_ite_false_rep _ hx_197 h_v313)
        · ite_branch hbv_197
          ite_stuck hinv31 hG with hx_197)
      store_step with h_ite_v314 as ⟨v314, s32, hinv32, h_v314⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 h_v196 dropping h_ite_v314 hinv31 s31
      store_step with Store.apply_mk_rep s32 v196 v314 _ _ hinv32 h64 h_v196 h_v314 as ⟨v315, s33, hinv33, h_v315⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v184 dropping h_v196 h_v314 hinv32 s32 v196 v314
      store_step with Store.apply_mk_rep s33 v184 v315 _ _ hinv33 h64 h_v184 h_v315 as ⟨v316, s34, hinv34, h_v316⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 dropping h_v184 h_v315 hinv33 s33 v184 v315
      store_step with Store.literal_boolean_spec s34 false hinv34 h64 as ⟨v317, s35, hinv35, h_v317⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 h_v316 dropping hinv34 s34
      store_step with Store.apply_mk_rep s35 v316 v317 _ _ hinv35 h64 h_v316 h_v317 as ⟨v318, s36, hinv36, h_v318⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 h_v183 dropping h_v316 h_v317 hinv35 s35 v316 v317
      store_step with Store.apply_mk_rep s36 v183 v318 _ _ hinv36 h64 h_v183 h_v318 as ⟨v319, s37, hinv37, h_v319⟩ growing hG carrying h_a0 h_v4 h_v7 h_v50 dropping h_v183 h_v318 hinv36 s36 v183 v318
      store_step with Store.apply_mk_rep s37 v50 v319 _ _ hinv37 h64 h_v50 h_v319 as ⟨v320, s38, hinv38, h_v320⟩ growing hG carrying h_a0 h_v4 h_v7 dropping h_v319 h_v50 hinv37 s37 v319 v50
      step as ⟨e_v321, he_v321⟩
      store_step with CtorSpec.eo_and.construct s38 e_v321 (by rw [he_v321]; exact empty_args) hinv38 h64 as ⟨v321, s39, hinv39, h_v321⟩ growing hG carrying h_a0 h_v4 h_v7 h_v320 dropping he_v321 hinv38 e_v321 s38
      step as ⟨e_v322, he_v322⟩
      store_step with CtorSpec.eo_not.construct s39 e_v322 (by rw [he_v322]; exact empty_args) hinv39 h64 as ⟨v322, s40, hinv40, h_v322⟩ growing hG carrying h_a0 h_v4 h_v7 h_v320 h_v321 dropping he_v322 hinv39 e_v322 s39
      step as ⟨e_v323, he_v323⟩
      store_step with CtorSpec.eo__3d.construct s40 e_v323 (by rw [he_v323]; exact empty_args) hinv40 h64 as ⟨v323, s41, hinv41, h_v323⟩ growing hG carrying h_a0 h_v4 h_v7 h_v320 h_v321 h_v322 dropping he_v323 hinv40 e_v323 s40
      step as ⟨e_v324, he_v324⟩
      store_step with CtorSpec.eo__40purify.construct s41 e_v324 (by rw [he_v324]; exact empty_args) hinv41 h64 as ⟨v324, s42, hinv42, h_v324⟩ growing hG carrying h_a0 h_v4 h_v7 h_v320 h_v321 h_v322 h_v323 dropping he_v324 hinv41 e_v324 s41
      step as ⟨e_v325, he_v325⟩
      store_step with CtorSpec.eo_str_2e_2b_2b.construct s42 e_v325 (by rw [he_v325]; exact empty_args) hinv42 h64 as ⟨v325, s43, hinv43, h_v325⟩ growing hG carrying h_a0 h_v4 h_v7 h_v320 h_v321 h_v322 h_v323 h_v324 dropping he_v325 hinv42 e_v325 s42
      have h_ite_v332 := (show if_32_eo__24eo_5fprog_5fconcat_5fsplit s43 a0 v7 ⦃ r s' => s'.Inv ∧ s43.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_32_eo__24eo_5fprog_5fconcat_5fsplit
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s43
        rcases Store.boolean_value_term h_a0 with ⟨hx_326, hbv_326⟩ | ⟨hx_326, hbv_326⟩ | ⟨hx_326, hbv_326⟩
        · ite_branch hbv_326
          step as ⟨e_v326, he_v326⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s43 e_v326 (by rw [he_v326]; exact empty_args) hinv43 h64 as ⟨v326, s44, hinv44, h_v326⟩ growing hG carrying h_a0 h_v4 h_v7 h_v320 h_v321 h_v322 h_v323 h_v324 h_v325 dropping he_v326 e_v326
          step as ⟨e_v327, he_v327⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s44 e_v327 (by rw [he_v327]; exact empty_args) hinv44 h64 as ⟨v327, s45, hinv45, h_v327⟩ growing hG carrying h_a0 h_v4 h_v7 h_v320 h_v321 h_v322 h_v323 h_v324 h_v325 h_v326 dropping he_v327 e_v327
          step as ⟨e_v328, he_v328⟩
          store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s45 e_v328 (by rw [he_v328]; rfl) h_v327 h_v7 hinv45 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v328, s46, hinv46, h_v328⟩ growing hG carrying h_a0 h_v4 h_v7 h_v320 h_v321 h_v322 h_v323 h_v324 h_v325 h_v326 dropping h_v327 he_v328 e_v328 v327
          step as ⟨e_v329, he_v329⟩
          store_step with Store.builtin_spec_list_rev n ih.eo__24eo_5fis_5flist_5fnil s46 e_v329 (by rw [he_v329]; rfl) h_v326 h_v328 hinv46 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v329, s47, hinv47, h_v329⟩ growing hG carrying h_a0 h_v4 h_v7 h_v320 h_v321 h_v322 h_v323 h_v324 h_v325 dropping h_v326 h_v328 he_v329 e_v329 v326 v328
          ite_done hinv47 hG with (eo_ite_true_rep _ hx_326 h_v329)
        · ite_branch hbv_326
          step as ⟨e_v330, he_v330⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s43 e_v330 (by rw [he_v330]; exact empty_args) hinv43 h64 as ⟨v330, s44, hinv44, h_v330⟩ growing hG carrying h_a0 h_v4 h_v7 h_v320 h_v321 h_v322 h_v323 h_v324 h_v325 dropping he_v330 e_v330
          step as ⟨e_v331, he_v331⟩
          store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s44 e_v331 (by rw [he_v331]; rfl) h_v330 h_v7 hinv44 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v331, s45, hinv45, h_v331⟩ growing hG carrying h_a0 h_v4 h_v7 h_v320 h_v321 h_v322 h_v323 h_v324 h_v325 dropping h_v330 he_v331 e_v331 v330
          ite_done hinv45 hG with (eo_ite_false_rep _ hx_326 h_v331)
        · ite_branch hbv_326
          ite_stuck hinv43 hG with hx_326)
      store_step with h_ite_v332 as ⟨v332, s44, hinv44, h_v332⟩ growing hG carrying h_a0 h_v4 h_v7 h_v320 h_v321 h_v322 h_v323 h_v324 h_v325 dropping h_ite_v332 hinv43 s43
      try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
      store_step with Store.literal_int_u32_spec s44 0#u32 (0) (by scalar_tac) hinv44 h64 as ⟨v333, s45, hinv45, h_v333⟩ growing hG carrying h_a0 h_v4 h_v7 h_v320 h_v321 h_v322 h_v323 h_v324 h_v325 h_v332 dropping hinv44 s44
      step as ⟨e_v334, he_v334⟩
      store_step with Store.builtin_spec_list_nth n ih.eo__24eo_5fis_5flist_5fnil s45 e_v334 (by rw [he_v334]; rfl) h_v325 h_v332 h_v333 hinv45 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v334, s46, hinv46, h_v334⟩ growing hG carrying h_a0 h_v4 h_v7 h_v320 h_v321 h_v322 h_v323 h_v324 dropping h_v325 h_v332 h_v333 he_v334 hinv45 e_v334 s45 v325 v332 v333
      step as ⟨e_v335, he_v335⟩
      store_step with CtorSpec.eo_str_2e_2b_2b.construct s46 e_v335 (by rw [he_v335]; exact empty_args) hinv46 h64 as ⟨v335, s47, hinv47, h_v335⟩ growing hG carrying h_a0 h_v4 h_v7 h_v320 h_v321 h_v322 h_v323 h_v324 h_v334 dropping he_v335 hinv46 e_v335 s46
      have h_ite_v342 := (show if_33_eo__24eo_5fprog_5fconcat_5fsplit s47 a0 v4 ⦃ r s' => s'.Inv ∧ s47.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_33_eo__24eo_5fprog_5fconcat_5fsplit
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s47
        rcases Store.boolean_value_term h_a0 with ⟨hx_336, hbv_336⟩ | ⟨hx_336, hbv_336⟩ | ⟨hx_336, hbv_336⟩
        · ite_branch hbv_336
          step as ⟨e_v336, he_v336⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s47 e_v336 (by rw [he_v336]; exact empty_args) hinv47 h64 as ⟨v336, s48, hinv48, h_v336⟩ growing hG carrying h_a0 h_v4 h_v7 h_v320 h_v321 h_v322 h_v323 h_v324 h_v334 h_v335 dropping he_v336 e_v336
          step as ⟨e_v337, he_v337⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s48 e_v337 (by rw [he_v337]; exact empty_args) hinv48 h64 as ⟨v337, s49, hinv49, h_v337⟩ growing hG carrying h_a0 h_v4 h_v7 h_v320 h_v321 h_v322 h_v323 h_v324 h_v334 h_v335 h_v336 dropping he_v337 e_v337
          step as ⟨e_v338, he_v338⟩
          store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s49 e_v338 (by rw [he_v338]; rfl) h_v337 h_v4 hinv49 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v338, s50, hinv50, h_v338⟩ growing hG carrying h_a0 h_v4 h_v7 h_v320 h_v321 h_v322 h_v323 h_v324 h_v334 h_v335 h_v336 dropping h_v337 he_v338 e_v338 v337
          step as ⟨e_v339, he_v339⟩
          store_step with Store.builtin_spec_list_rev n ih.eo__24eo_5fis_5flist_5fnil s50 e_v339 (by rw [he_v339]; rfl) h_v336 h_v338 hinv50 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v339, s51, hinv51, h_v339⟩ growing hG carrying h_a0 h_v4 h_v7 h_v320 h_v321 h_v322 h_v323 h_v324 h_v334 h_v335 dropping h_v336 h_v338 he_v339 e_v339 v336 v338
          ite_done hinv51 hG with (eo_ite_true_rep _ hx_336 h_v339)
        · ite_branch hbv_336
          step as ⟨e_v340, he_v340⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s47 e_v340 (by rw [he_v340]; exact empty_args) hinv47 h64 as ⟨v340, s48, hinv48, h_v340⟩ growing hG carrying h_a0 h_v4 h_v7 h_v320 h_v321 h_v322 h_v323 h_v324 h_v334 h_v335 dropping he_v340 e_v340
          step as ⟨e_v341, he_v341⟩
          store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s48 e_v341 (by rw [he_v341]; rfl) h_v340 h_v4 hinv48 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v341, s49, hinv49, h_v341⟩ growing hG carrying h_a0 h_v4 h_v7 h_v320 h_v321 h_v322 h_v323 h_v324 h_v334 h_v335 dropping h_v340 he_v341 e_v341 v340
          ite_done hinv49 hG with (eo_ite_false_rep _ hx_336 h_v341)
        · ite_branch hbv_336
          ite_stuck hinv47 hG with hx_336)
      store_step with h_ite_v342 as ⟨v342, s48, hinv48, h_v342⟩ growing hG carrying h_a0 h_v4 h_v7 h_v320 h_v321 h_v322 h_v323 h_v324 h_v334 h_v335 dropping h_ite_v342 hinv47 s47
      try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
      store_step with Store.literal_int_u32_spec s48 0#u32 (0) (by scalar_tac) hinv48 h64 as ⟨v343, s49, hinv49, h_v343⟩ growing hG carrying h_a0 h_v4 h_v7 h_v320 h_v321 h_v322 h_v323 h_v324 h_v334 h_v335 h_v342 dropping hinv48 s48
      step as ⟨e_v344, he_v344⟩
      store_step with Store.builtin_spec_list_nth n ih.eo__24eo_5fis_5flist_5fnil s49 e_v344 (by rw [he_v344]; rfl) h_v335 h_v342 h_v343 hinv49 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v344, s50, hinv50, h_v344⟩ growing hG carrying h_a0 h_v4 h_v7 h_v320 h_v321 h_v322 h_v323 h_v324 h_v334 dropping h_v335 h_v342 h_v343 he_v344 hinv49 e_v344 s49 v335 v342 v343
      store_step with ih.eo__24str_5funify_5fsplit s50 v334 v344 a0 _ _ _ hinv50 h64 (hG.rem hrem) h_v334 h_v344 h_a0 as ⟨v345, s51, hinv51, h_v345⟩ growing hG carrying h_a0 h_v4 h_v7 h_v320 h_v321 h_v322 h_v323 h_v324 dropping h_v334 h_v344 hinv50 s50 v334 v344
      store_step with Store.apply_mk_rep s51 v324 v345 _ _ hinv51 h64 h_v324 h_v345 as ⟨v346, s52, hinv52, h_v346⟩ growing hG carrying h_a0 h_v4 h_v7 h_v320 h_v321 h_v322 h_v323 dropping h_v324 h_v345 hinv51 s51 v324 v345
      store_step with Store.apply_mk_rep s52 v323 v346 _ _ hinv52 h64 h_v323 h_v346 as ⟨v347, s53, hinv53, h_v347⟩ growing hG carrying h_a0 h_v4 h_v7 h_v320 h_v321 h_v322 dropping h_v323 h_v346 hinv52 s52 v323 v346
      step as ⟨e_v348, he_v348⟩
      store_step with CtorSpec.eo__40purify.construct s53 e_v348 (by rw [he_v348]; exact empty_args) hinv53 h64 as ⟨v348, s54, hinv54, h_v348⟩ growing hG carrying h_a0 h_v4 h_v7 h_v320 h_v321 h_v322 h_v347 dropping he_v348 hinv53 e_v348 s53
      step as ⟨e_v349, he_v349⟩
      store_step with CtorSpec.eo_str_2e_2b_2b.construct s54 e_v349 (by rw [he_v349]; exact empty_args) hinv54 h64 as ⟨v349, s55, hinv55, h_v349⟩ growing hG carrying h_a0 h_v4 h_v7 h_v320 h_v321 h_v322 h_v347 h_v348 dropping he_v349 hinv54 e_v349 s54
      have h_ite_v356 := (show if_34_eo__24eo_5fprog_5fconcat_5fsplit s55 a0 v7 ⦃ r s' => s'.Inv ∧ s55.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_34_eo__24eo_5fprog_5fconcat_5fsplit
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s55
        rcases Store.boolean_value_term h_a0 with ⟨hx_350, hbv_350⟩ | ⟨hx_350, hbv_350⟩ | ⟨hx_350, hbv_350⟩
        · ite_branch hbv_350
          step as ⟨e_v350, he_v350⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s55 e_v350 (by rw [he_v350]; exact empty_args) hinv55 h64 as ⟨v350, s56, hinv56, h_v350⟩ growing hG carrying h_a0 h_v4 h_v7 h_v320 h_v321 h_v322 h_v347 h_v348 h_v349 dropping he_v350 e_v350
          step as ⟨e_v351, he_v351⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s56 e_v351 (by rw [he_v351]; exact empty_args) hinv56 h64 as ⟨v351, s57, hinv57, h_v351⟩ growing hG carrying h_a0 h_v4 h_v7 h_v320 h_v321 h_v322 h_v347 h_v348 h_v349 h_v350 dropping he_v351 e_v351
          step as ⟨e_v352, he_v352⟩
          store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s57 e_v352 (by rw [he_v352]; rfl) h_v351 h_v7 hinv57 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v352, s58, hinv58, h_v352⟩ growing hG carrying h_a0 h_v4 h_v7 h_v320 h_v321 h_v322 h_v347 h_v348 h_v349 h_v350 dropping h_v351 he_v352 e_v352 v351
          step as ⟨e_v353, he_v353⟩
          store_step with Store.builtin_spec_list_rev n ih.eo__24eo_5fis_5flist_5fnil s58 e_v353 (by rw [he_v353]; rfl) h_v350 h_v352 hinv58 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v353, s59, hinv59, h_v353⟩ growing hG carrying h_a0 h_v4 h_v7 h_v320 h_v321 h_v322 h_v347 h_v348 h_v349 dropping h_v350 h_v352 he_v353 e_v353 v350 v352
          ite_done hinv59 hG with (eo_ite_true_rep _ hx_350 h_v353)
        · ite_branch hbv_350
          step as ⟨e_v354, he_v354⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s55 e_v354 (by rw [he_v354]; exact empty_args) hinv55 h64 as ⟨v354, s56, hinv56, h_v354⟩ growing hG carrying h_a0 h_v4 h_v7 h_v320 h_v321 h_v322 h_v347 h_v348 h_v349 dropping he_v354 e_v354
          step as ⟨e_v355, he_v355⟩
          store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s56 e_v355 (by rw [he_v355]; rfl) h_v354 h_v7 hinv56 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v355, s57, hinv57, h_v355⟩ growing hG carrying h_a0 h_v4 h_v7 h_v320 h_v321 h_v322 h_v347 h_v348 h_v349 dropping h_v354 he_v355 e_v355 v354
          ite_done hinv57 hG with (eo_ite_false_rep _ hx_350 h_v355)
        · ite_branch hbv_350
          ite_stuck hinv55 hG with hx_350)
      store_step with h_ite_v356 as ⟨v356, s56, hinv56, h_v356⟩ growing hG carrying h_a0 h_v4 h_v7 h_v320 h_v321 h_v322 h_v347 h_v348 h_v349 dropping h_ite_v356 hinv55 s55
      try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
      store_step with Store.literal_int_u32_spec s56 0#u32 (0) (by scalar_tac) hinv56 h64 as ⟨v357, s57, hinv57, h_v357⟩ growing hG carrying h_a0 h_v4 h_v7 h_v320 h_v321 h_v322 h_v347 h_v348 h_v349 h_v356 dropping hinv56 s56
      step as ⟨e_v358, he_v358⟩
      store_step with Store.builtin_spec_list_nth n ih.eo__24eo_5fis_5flist_5fnil s57 e_v358 (by rw [he_v358]; rfl) h_v349 h_v356 h_v357 hinv57 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v358, s58, hinv58, h_v358⟩ growing hG carrying h_a0 h_v4 h_v7 h_v320 h_v321 h_v322 h_v347 h_v348 dropping h_v349 h_v356 h_v357 he_v358 hinv57 e_v358 s57 v349 v356 v357
      step as ⟨e_v359, he_v359⟩
      store_step with CtorSpec.eo_str_2e_2b_2b.construct s58 e_v359 (by rw [he_v359]; exact empty_args) hinv58 h64 as ⟨v359, s59, hinv59, h_v359⟩ growing hG carrying h_a0 h_v4 h_v7 h_v320 h_v321 h_v322 h_v347 h_v348 h_v358 dropping he_v359 hinv58 e_v359 s58
      have h_ite_v366 := (show if_35_eo__24eo_5fprog_5fconcat_5fsplit s59 a0 v4 ⦃ r s' => s'.Inv ∧ s59.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_35_eo__24eo_5fprog_5fconcat_5fsplit
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s59
        rcases Store.boolean_value_term h_a0 with ⟨hx_360, hbv_360⟩ | ⟨hx_360, hbv_360⟩ | ⟨hx_360, hbv_360⟩
        · ite_branch hbv_360
          step as ⟨e_v360, he_v360⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s59 e_v360 (by rw [he_v360]; exact empty_args) hinv59 h64 as ⟨v360, s60, hinv60, h_v360⟩ growing hG carrying h_a0 h_v4 h_v7 h_v320 h_v321 h_v322 h_v347 h_v348 h_v358 h_v359 dropping he_v360 e_v360
          step as ⟨e_v361, he_v361⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s60 e_v361 (by rw [he_v361]; exact empty_args) hinv60 h64 as ⟨v361, s61, hinv61, h_v361⟩ growing hG carrying h_a0 h_v4 h_v7 h_v320 h_v321 h_v322 h_v347 h_v348 h_v358 h_v359 h_v360 dropping he_v361 e_v361
          step as ⟨e_v362, he_v362⟩
          store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s61 e_v362 (by rw [he_v362]; rfl) h_v361 h_v4 hinv61 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v362, s62, hinv62, h_v362⟩ growing hG carrying h_a0 h_v4 h_v7 h_v320 h_v321 h_v322 h_v347 h_v348 h_v358 h_v359 h_v360 dropping h_v361 he_v362 e_v362 v361
          step as ⟨e_v363, he_v363⟩
          store_step with Store.builtin_spec_list_rev n ih.eo__24eo_5fis_5flist_5fnil s62 e_v363 (by rw [he_v363]; rfl) h_v360 h_v362 hinv62 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v363, s63, hinv63, h_v363⟩ growing hG carrying h_a0 h_v4 h_v7 h_v320 h_v321 h_v322 h_v347 h_v348 h_v358 h_v359 dropping h_v360 h_v362 he_v363 e_v363 v360 v362
          ite_done hinv63 hG with (eo_ite_true_rep _ hx_360 h_v363)
        · ite_branch hbv_360
          step as ⟨e_v364, he_v364⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s59 e_v364 (by rw [he_v364]; exact empty_args) hinv59 h64 as ⟨v364, s60, hinv60, h_v364⟩ growing hG carrying h_a0 h_v4 h_v7 h_v320 h_v321 h_v322 h_v347 h_v348 h_v358 h_v359 dropping he_v364 e_v364
          step as ⟨e_v365, he_v365⟩
          store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s60 e_v365 (by rw [he_v365]; rfl) h_v364 h_v4 hinv60 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v365, s61, hinv61, h_v365⟩ growing hG carrying h_a0 h_v4 h_v7 h_v320 h_v321 h_v322 h_v347 h_v348 h_v358 h_v359 dropping h_v364 he_v365 e_v365 v364
          ite_done hinv61 hG with (eo_ite_false_rep _ hx_360 h_v365)
        · ite_branch hbv_360
          ite_stuck hinv59 hG with hx_360)
      store_step with h_ite_v366 as ⟨v366, s60, hinv60, h_v366⟩ growing hG carrying h_a0 h_v4 h_v7 h_v320 h_v321 h_v322 h_v347 h_v348 h_v358 h_v359 dropping h_ite_v366 hinv59 s59
      try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
      store_step with Store.literal_int_u32_spec s60 0#u32 (0) (by scalar_tac) hinv60 h64 as ⟨v367, s61, hinv61, h_v367⟩ growing hG carrying h_a0 h_v4 h_v7 h_v320 h_v321 h_v322 h_v347 h_v348 h_v358 h_v359 h_v366 dropping hinv60 s60
      step as ⟨e_v368, he_v368⟩
      store_step with Store.builtin_spec_list_nth n ih.eo__24eo_5fis_5flist_5fnil s61 e_v368 (by rw [he_v368]; rfl) h_v359 h_v366 h_v367 hinv61 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v368, s62, hinv62, h_v368⟩ growing hG carrying h_a0 h_v4 h_v7 h_v320 h_v321 h_v322 h_v347 h_v348 h_v358 dropping h_v359 h_v366 h_v367 he_v368 hinv61 e_v368 s61 v359 v366 v367
      store_step with ih.eo__24str_5funify_5fsplit s62 v358 v368 a0 _ _ _ hinv62 h64 (hG.rem hrem) h_v358 h_v368 h_a0 as ⟨v369, s63, hinv63, h_v369⟩ growing hG carrying h_a0 h_v4 h_v7 h_v320 h_v321 h_v322 h_v347 h_v348 dropping h_v358 h_v368 hinv62 s62 v358 v368
      store_step with Store.apply_mk_rep s63 v348 v369 _ _ hinv63 h64 h_v348 h_v369 as ⟨v370, s64, hinv64, h_v370⟩ growing hG carrying h_a0 h_v4 h_v7 h_v320 h_v321 h_v322 h_v347 dropping h_v348 h_v369 hinv63 s63 v348 v369
      store_step with ih.eo__24eo_5ftypeof s64 v370 _ hinv64 h64 (hG.rem hrem) h_v370 as ⟨v371, s65, hinv65, h_v371⟩ growing hG carrying h_a0 h_v4 h_v7 h_v320 h_v321 h_v322 h_v347 dropping h_v370 hinv64 s64 v370
      store_step with ih.eo__24seq_5fempty s65 v371 _ hinv65 h64 (hG.rem hrem) h_v371 as ⟨v372, s66, hinv66, h_v372⟩ growing hG carrying h_a0 h_v4 h_v7 h_v320 h_v321 h_v322 h_v347 dropping h_v371 hinv65 s65 v371
      store_step with Store.apply_mk_rep s66 v347 v372 _ _ hinv66 h64 h_v347 h_v372 as ⟨v373, s67, hinv67, h_v373⟩ growing hG carrying h_a0 h_v4 h_v7 h_v320 h_v321 h_v322 dropping h_v347 h_v372 hinv66 s66 v347 v372
      store_step with Store.apply_mk_rep s67 v322 v373 _ _ hinv67 h64 h_v322 h_v373 as ⟨v374, s68, hinv68, h_v374⟩ growing hG carrying h_a0 h_v4 h_v7 h_v320 h_v321 dropping h_v322 h_v373 hinv67 s67 v322 v373
      store_step with Store.apply_mk_rep s68 v321 v374 _ _ hinv68 h64 h_v321 h_v374 as ⟨v375, s69, hinv69, h_v375⟩ growing hG carrying h_a0 h_v4 h_v7 h_v320 dropping h_v321 h_v374 hinv68 s68 v321 v374
      step as ⟨e_v376, he_v376⟩
      store_step with CtorSpec.eo_and.construct s69 e_v376 (by rw [he_v376]; exact empty_args) hinv69 h64 as ⟨v376, s70, hinv70, h_v376⟩ growing hG carrying h_a0 h_v4 h_v7 h_v320 h_v375 dropping he_v376 hinv69 e_v376 s69
      step as ⟨e_v377, he_v377⟩
      store_step with CtorSpec.eo__3e.construct s70 e_v377 (by rw [he_v377]; exact empty_args) hinv70 h64 as ⟨v377, s71, hinv71, h_v377⟩ growing hG carrying h_a0 h_v4 h_v7 h_v320 h_v375 h_v376 dropping he_v377 hinv70 e_v377 s70
      step as ⟨e_v378, he_v378⟩
      store_step with CtorSpec.eo_str_2elen.construct s71 e_v378 (by rw [he_v378]; exact empty_args) hinv71 h64 as ⟨v378, s72, hinv72, h_v378⟩ growing hG carrying h_a0 h_v4 h_v7 h_v320 h_v375 h_v376 h_v377 dropping he_v378 hinv71 e_v378 s71
      step as ⟨e_v379, he_v379⟩
      store_step with CtorSpec.eo__40purify.construct s72 e_v379 (by rw [he_v379]; exact empty_args) hinv72 h64 as ⟨v379, s73, hinv73, h_v379⟩ growing hG carrying h_a0 h_v4 h_v7 h_v320 h_v375 h_v376 h_v377 h_v378 dropping he_v379 hinv72 e_v379 s72
      step as ⟨e_v380, he_v380⟩
      store_step with CtorSpec.eo_str_2e_2b_2b.construct s73 e_v380 (by rw [he_v380]; exact empty_args) hinv73 h64 as ⟨v380, s74, hinv74, h_v380⟩ growing hG carrying h_a0 h_v4 h_v7 h_v320 h_v375 h_v376 h_v377 h_v378 h_v379 dropping he_v380 hinv73 e_v380 s73
      have h_ite_v387 := (show if_36_eo__24eo_5fprog_5fconcat_5fsplit s74 a0 v7 ⦃ r s' => s'.Inv ∧ s74.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_36_eo__24eo_5fprog_5fconcat_5fsplit
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s74
        rcases Store.boolean_value_term h_a0 with ⟨hx_381, hbv_381⟩ | ⟨hx_381, hbv_381⟩ | ⟨hx_381, hbv_381⟩
        · ite_branch hbv_381
          step as ⟨e_v381, he_v381⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s74 e_v381 (by rw [he_v381]; exact empty_args) hinv74 h64 as ⟨v381, s75, hinv75, h_v381⟩ growing hG carrying h_a0 h_v4 h_v7 h_v320 h_v375 h_v376 h_v377 h_v378 h_v379 h_v380 dropping he_v381 e_v381
          step as ⟨e_v382, he_v382⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s75 e_v382 (by rw [he_v382]; exact empty_args) hinv75 h64 as ⟨v382, s76, hinv76, h_v382⟩ growing hG carrying h_a0 h_v4 h_v7 h_v320 h_v375 h_v376 h_v377 h_v378 h_v379 h_v380 h_v381 dropping he_v382 e_v382
          step as ⟨e_v383, he_v383⟩
          store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s76 e_v383 (by rw [he_v383]; rfl) h_v382 h_v7 hinv76 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v383, s77, hinv77, h_v383⟩ growing hG carrying h_a0 h_v4 h_v7 h_v320 h_v375 h_v376 h_v377 h_v378 h_v379 h_v380 h_v381 dropping h_v382 he_v383 e_v383 v382
          step as ⟨e_v384, he_v384⟩
          store_step with Store.builtin_spec_list_rev n ih.eo__24eo_5fis_5flist_5fnil s77 e_v384 (by rw [he_v384]; rfl) h_v381 h_v383 hinv77 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v384, s78, hinv78, h_v384⟩ growing hG carrying h_a0 h_v4 h_v7 h_v320 h_v375 h_v376 h_v377 h_v378 h_v379 h_v380 dropping h_v381 h_v383 he_v384 e_v384 v381 v383
          ite_done hinv78 hG with (eo_ite_true_rep _ hx_381 h_v384)
        · ite_branch hbv_381
          step as ⟨e_v385, he_v385⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s74 e_v385 (by rw [he_v385]; exact empty_args) hinv74 h64 as ⟨v385, s75, hinv75, h_v385⟩ growing hG carrying h_a0 h_v4 h_v7 h_v320 h_v375 h_v376 h_v377 h_v378 h_v379 h_v380 dropping he_v385 e_v385
          step as ⟨e_v386, he_v386⟩
          store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s75 e_v386 (by rw [he_v386]; rfl) h_v385 h_v7 hinv75 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v386, s76, hinv76, h_v386⟩ growing hG carrying h_a0 h_v4 h_v320 h_v375 h_v376 h_v377 h_v378 h_v379 h_v380 dropping h_v385 h_v7 he_v386 e_v386 v385 v7
          ite_done hinv76 hG with (eo_ite_false_rep _ hx_381 h_v386)
        · ite_branch hbv_381
          ite_stuck hinv74 hG with hx_381)
      store_step with h_ite_v387 as ⟨v387, s75, hinv75, h_v387⟩ growing hG carrying h_a0 h_v4 h_v320 h_v375 h_v376 h_v377 h_v378 h_v379 h_v380 dropping h_ite_v387 h_v7 hinv74 s74 v7
      try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
      store_step with Store.literal_int_u32_spec s75 0#u32 (0) (by scalar_tac) hinv75 h64 as ⟨v388, s76, hinv76, h_v388⟩ growing hG carrying h_a0 h_v4 h_v320 h_v375 h_v376 h_v377 h_v378 h_v379 h_v380 h_v387 dropping hinv75 s75
      step as ⟨e_v389, he_v389⟩
      store_step with Store.builtin_spec_list_nth n ih.eo__24eo_5fis_5flist_5fnil s76 e_v389 (by rw [he_v389]; rfl) h_v380 h_v387 h_v388 hinv76 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v389, s77, hinv77, h_v389⟩ growing hG carrying h_a0 h_v4 h_v320 h_v375 h_v376 h_v377 h_v378 h_v379 dropping h_v380 h_v387 h_v388 he_v389 hinv76 e_v389 s76 v380 v387 v388
      step as ⟨e_v390, he_v390⟩
      store_step with CtorSpec.eo_str_2e_2b_2b.construct s77 e_v390 (by rw [he_v390]; exact empty_args) hinv77 h64 as ⟨v390, s78, hinv78, h_v390⟩ growing hG carrying h_a0 h_v4 h_v320 h_v375 h_v376 h_v377 h_v378 h_v379 h_v389 dropping he_v390 hinv77 e_v390 s77
      have h_ite_v397 := (show if_37_eo__24eo_5fprog_5fconcat_5fsplit s78 a0 v4 ⦃ r s' => s'.Inv ∧ s78.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_37_eo__24eo_5fprog_5fconcat_5fsplit
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s78
        rcases Store.boolean_value_term h_a0 with ⟨hx_391, hbv_391⟩ | ⟨hx_391, hbv_391⟩ | ⟨hx_391, hbv_391⟩
        · ite_branch hbv_391
          step as ⟨e_v391, he_v391⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s78 e_v391 (by rw [he_v391]; exact empty_args) hinv78 h64 as ⟨v391, s79, hinv79, h_v391⟩ growing hG carrying h_a0 h_v4 h_v320 h_v375 h_v376 h_v377 h_v378 h_v379 h_v389 h_v390 dropping he_v391 e_v391
          step as ⟨e_v392, he_v392⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s79 e_v392 (by rw [he_v392]; exact empty_args) hinv79 h64 as ⟨v392, s80, hinv80, h_v392⟩ growing hG carrying h_a0 h_v4 h_v320 h_v375 h_v376 h_v377 h_v378 h_v379 h_v389 h_v390 h_v391 dropping he_v392 e_v392
          step as ⟨e_v393, he_v393⟩
          store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s80 e_v393 (by rw [he_v393]; rfl) h_v392 h_v4 hinv80 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v393, s81, hinv81, h_v393⟩ growing hG carrying h_a0 h_v4 h_v320 h_v375 h_v376 h_v377 h_v378 h_v379 h_v389 h_v390 h_v391 dropping h_v392 he_v393 e_v393 v392
          step as ⟨e_v394, he_v394⟩
          store_step with Store.builtin_spec_list_rev n ih.eo__24eo_5fis_5flist_5fnil s81 e_v394 (by rw [he_v394]; rfl) h_v391 h_v393 hinv81 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v394, s82, hinv82, h_v394⟩ growing hG carrying h_a0 h_v4 h_v320 h_v375 h_v376 h_v377 h_v378 h_v379 h_v389 h_v390 dropping h_v391 h_v393 he_v394 e_v394 v391 v393
          ite_done hinv82 hG with (eo_ite_true_rep _ hx_391 h_v394)
        · ite_branch hbv_391
          step as ⟨e_v395, he_v395⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s78 e_v395 (by rw [he_v395]; exact empty_args) hinv78 h64 as ⟨v395, s79, hinv79, h_v395⟩ growing hG carrying h_a0 h_v4 h_v320 h_v375 h_v376 h_v377 h_v378 h_v379 h_v389 h_v390 dropping he_v395 e_v395
          step as ⟨e_v396, he_v396⟩
          store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s79 e_v396 (by rw [he_v396]; rfl) h_v395 h_v4 hinv79 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v396, s80, hinv80, h_v396⟩ growing hG carrying h_a0 h_v320 h_v375 h_v376 h_v377 h_v378 h_v379 h_v389 h_v390 dropping h_v395 h_v4 he_v396 e_v396 v395 v4
          ite_done hinv80 hG with (eo_ite_false_rep _ hx_391 h_v396)
        · ite_branch hbv_391
          ite_stuck hinv78 hG with hx_391)
      store_step with h_ite_v397 as ⟨v397, s79, hinv79, h_v397⟩ growing hG carrying h_a0 h_v320 h_v375 h_v376 h_v377 h_v378 h_v379 h_v389 h_v390 dropping h_ite_v397 h_v4 hinv78 s78 v4
      try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
      store_step with Store.literal_int_u32_spec s79 0#u32 (0) (by scalar_tac) hinv79 h64 as ⟨v398, s80, hinv80, h_v398⟩ growing hG carrying h_a0 h_v320 h_v375 h_v376 h_v377 h_v378 h_v379 h_v389 h_v390 h_v397 dropping hinv79 s79
      step as ⟨e_v399, he_v399⟩
      store_step with Store.builtin_spec_list_nth n ih.eo__24eo_5fis_5flist_5fnil s80 e_v399 (by rw [he_v399]; rfl) h_v390 h_v397 h_v398 hinv80 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v399, s81, hinv81, h_v399⟩ growing hG carrying h_a0 h_v320 h_v375 h_v376 h_v377 h_v378 h_v379 h_v389 dropping h_v390 h_v397 h_v398 he_v399 hinv80 e_v399 s80 v390 v397 v398
      store_step with ih.eo__24str_5funify_5fsplit s81 v389 v399 a0 _ _ _ hinv81 h64 (hG.rem hrem) h_v389 h_v399 h_a0 as ⟨v400, s82, hinv82, h_v400⟩ growing hG carrying h_v320 h_v375 h_v376 h_v377 h_v378 h_v379 dropping h_a0 h_v389 h_v399 hinv81 s81 v389 v399
      store_step with Store.apply_mk_rep s82 v379 v400 _ _ hinv82 h64 h_v379 h_v400 as ⟨v401, s83, hinv83, h_v401⟩ growing hG carrying h_v320 h_v375 h_v376 h_v377 h_v378 dropping h_v379 h_v400 hinv82 s82 v379 v400
      store_step with Store.apply_mk_rep s83 v378 v401 _ _ hinv83 h64 h_v378 h_v401 as ⟨v402, s84, hinv84, h_v402⟩ growing hG carrying h_v320 h_v375 h_v376 h_v377 dropping h_v378 h_v401 hinv83 s83 v378 v401
      store_step with Store.apply_mk_rep s84 v377 v402 _ _ hinv84 h64 h_v377 h_v402 as ⟨v403, s85, hinv85, h_v403⟩ growing hG carrying h_v320 h_v375 h_v376 dropping h_v377 h_v402 hinv84 s84 v377 v402
      try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
      store_step with Store.literal_int_u32_spec s85 0#u32 (0) (by scalar_tac) hinv85 h64 as ⟨v404, s86, hinv86, h_v404⟩ growing hG carrying h_v320 h_v375 h_v376 h_v403 dropping hinv85 s85
      store_step with Store.apply_mk_rep s86 v403 v404 _ _ hinv86 h64 h_v403 h_v404 as ⟨v405, s87, hinv87, h_v405⟩ growing hG carrying h_v320 h_v375 h_v376 dropping h_v403 h_v404 hinv86 s86 v403 v404
      store_step with Store.apply_mk_rep s87 v376 v405 _ _ hinv87 h64 h_v376 h_v405 as ⟨v406, s88, hinv88, h_v406⟩ growing hG carrying h_v320 h_v375 dropping h_v376 h_v405 hinv87 s87 v376 v405
      store_step with Store.literal_boolean_spec s88 true hinv88 h64 as ⟨v407, s89, hinv89, h_v407⟩ growing hG carrying h_v320 h_v375 h_v406 dropping hinv88 s88
      store_step with Store.apply_mk_rep s89 v406 v407 _ _ hinv89 h64 h_v406 h_v407 as ⟨v408, s90, hinv90, h_v408⟩ growing hG carrying h_v320 h_v375 dropping h_v406 h_v407 hinv89 s89 v406 v407
      store_step with Store.apply_mk_rep s90 v375 v408 _ _ hinv90 h64 h_v375 h_v408 as ⟨v409, s91, hinv91, h_v409⟩ growing hG carrying h_v320 dropping h_v375 h_v408 hinv90 s90 v375 v408
      store_step with Store.apply_mk_rep s91 v320 v409 _ _ hinv91 h64 h_v320 h_v409 as ⟨v410, s92, hinv92, h_v410⟩ growing hG carrying dropping h_v320 h_v409 hinv91 s91 v320 v409
      req_done hinv92 hG with h_v410 using hq_v49)
    store_step with h_req_v411 as ⟨v411, s93, hinv93, h_v411⟩ growing hG carrying dropping h_req_v411 h_v28 h_v4 h_v49 h_v7 hinv13 s13 v28 v4 v49 v7
    req_done hinv93 hG with h_v411 using hq_v39)
  store_step with h_req_v412 as ⟨v412, s94, hinv94, h_v412⟩ growing hG carrying dropping h_req_v412 h_v24 h_v28 h_v39 h_v4 h_v7 hinv9 s9 v24 v28 v39 v4 v7
  case_done hinv94 hG with h_v412 in EoCases.__eo_prog_concat_split.case_0 using hn_a0 hn_v3 hn_v4 hn_v6 hn_v7 hn_v12 hn_v13 hn_v16 hn_v17 hn_v19 hn_v20 hn_v23 hn_v24 hn_v27 hn_v28

/-- logos's `__eo_prog_concat_split` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fconcat_5fsplit.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __eo_prog_concat_split x_a0 x_a1 x_a2 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_concat_split.case_0 x_a0 x_a1 x_a2] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_concat_split
  unfold EoCases.__eo_prog_concat_split.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fconcat_5fsplit_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24eo_5fprog_5fconcat_5fsplit s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_concat_split x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fconcat_5fsplit.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24eo_5fprog_5fconcat_5fsplit
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fconcat_5fsplit_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_concat_split.case_0

theorem eo__24eo_5fprog_5fconcat_5fsplit_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fconcat_5fsplit.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24eo_5fprog_5fconcat_5fsplit
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fconcat_5fsplit s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__eo_prog_concat_split x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fconcat_5fsplit_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fconcat_5funify_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fconcat_5funify s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_concat_unify.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_concat_unify.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fconcat_5funify
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a1 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_concat_unify.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_concat_unify.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_concat_unify.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a2 h_v4 h_v6 h_v7 dropping h_a1 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_concat_unify.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a2 as ⟨v10, x_v10, h_v10⟩ else hinv1 hG in EoCases.__eo_prog_concat_unify.case_0
  pat_unapply h_v10 as ⟨v12, v13, x_v12, x_v13, h_v12, h_v13, hn_v12, hn_v13⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_concat_unify.case_0
  pat_unapply h_v12 as ⟨v15, v16, x_v15, x_v16, h_v15, h_v16, hn_v15, hn_v16⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_concat_unify.case_0
  step as ⟨e_v17, he_v17⟩
  store_step with CtorSpec.eo__3d.construct s1 e_v17 (by rw [he_v17]; exact empty_args) hinv1 h64 as ⟨v17, s2, hinv2, h_v17⟩ growing hG carrying h_a0 h_v4 h_v7 h_v13 h_v15 h_v16 dropping h_a2 h_v10 h_v12 h_v6 h_v8 he_v17 hinv1 e_v17 s1 v10 v12 v6 v8
  pat_same v15 v17 with h_v15 h_v17 using hinv2 else hinv2 hG in EoCases.__eo_prog_concat_unify.case_0
  pat_unapply h_v16 as ⟨v19, v20, x_v19, x_v20, h_v19, h_v20, hn_v19, hn_v20⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_concat_unify.case_0
  step as ⟨e_v21, he_v21⟩
  store_step with CtorSpec.eo_str_2elen.construct s2 e_v21 (by rw [he_v21]; exact empty_args) hinv2 h64 as ⟨v21, s3, hinv3, h_v21⟩ growing hG carrying h_a0 h_v4 h_v7 h_v13 h_v19 h_v20 dropping h_v15 h_v16 h_v17 he_v21 hinv2 e_v21 s2 v15 v16 v17
  pat_same v19 v21 with h_v19 h_v21 using hinv3 else hinv3 hG in EoCases.__eo_prog_concat_unify.case_0
  pat_unapply h_v13 as ⟨v23, v24, x_v23, x_v24, h_v23, h_v24, hn_v23, hn_v24⟩ using hinv3 else hinv3 hG in EoCases.__eo_prog_concat_unify.case_0
  step as ⟨e_v25, he_v25⟩
  store_step with CtorSpec.eo_str_2elen.construct s3 e_v25 (by rw [he_v25]; exact empty_args) hinv3 h64 as ⟨v25, s4, hinv4, h_v25⟩ growing hG carrying h_a0 h_v4 h_v7 h_v20 h_v23 h_v24 dropping h_v13 h_v19 h_v21 he_v25 hinv3 e_v25 s3 v13 v19 v21
  pat_same v23 v25 with h_v23 h_v25 using hinv4 else hinv4 hG in EoCases.__eo_prog_concat_unify.case_0
  step as ⟨e_v26, he_v26⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s4 e_v26 (by rw [he_v26]; exact empty_args) hinv4 h64 as ⟨v26, s5, hinv5, h_v26⟩ growing hG carrying h_a0 h_v4 h_v7 h_v20 h_v24 dropping h_v23 h_v25 he_v26 hinv4 e_v26 s4 v23 v25
  have h_ite_v33 := (show if_0_eo__24eo_5fprog_5fconcat_5funify s5 a0 v7 ⦃ r s' => s'.Inv ∧ s5.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_0_eo__24eo_5fprog_5fconcat_5funify
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s5
    rcases Store.boolean_value_term h_a0 with ⟨hx_27, hbv_27⟩ | ⟨hx_27, hbv_27⟩ | ⟨hx_27, hbv_27⟩
    · ite_branch hbv_27
      step as ⟨e_v27, he_v27⟩
      store_step with CtorSpec.eo_str_2e_2b_2b.construct s5 e_v27 (by rw [he_v27]; exact empty_args) hinv5 h64 as ⟨v27, s6, hinv6, h_v27⟩ growing hG carrying h_a0 h_v4 h_v7 h_v20 h_v24 h_v26 dropping he_v27 e_v27
      step as ⟨e_v28, he_v28⟩
      store_step with CtorSpec.eo_str_2e_2b_2b.construct s6 e_v28 (by rw [he_v28]; exact empty_args) hinv6 h64 as ⟨v28, s7, hinv7, h_v28⟩ growing hG carrying h_a0 h_v4 h_v7 h_v20 h_v24 h_v26 h_v27 dropping he_v28 e_v28
      step as ⟨e_v29, he_v29⟩
      store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s7 e_v29 (by rw [he_v29]; rfl) h_v28 h_v7 hinv7 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v29, s8, hinv8, h_v29⟩ growing hG carrying h_a0 h_v4 h_v7 h_v20 h_v24 h_v26 h_v27 dropping h_v28 he_v29 e_v29 v28
      step as ⟨e_v30, he_v30⟩
      store_step with Store.builtin_spec_list_rev n ih.eo__24eo_5fis_5flist_5fnil s8 e_v30 (by rw [he_v30]; rfl) h_v27 h_v29 hinv8 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v30, s9, hinv9, h_v30⟩ growing hG carrying h_a0 h_v4 h_v7 h_v20 h_v24 h_v26 dropping h_v27 h_v29 he_v30 e_v30 v27 v29
      ite_done hinv9 hG with (eo_ite_true_rep _ hx_27 h_v30)
    · ite_branch hbv_27
      step as ⟨e_v31, he_v31⟩
      store_step with CtorSpec.eo_str_2e_2b_2b.construct s5 e_v31 (by rw [he_v31]; exact empty_args) hinv5 h64 as ⟨v31, s6, hinv6, h_v31⟩ growing hG carrying h_a0 h_v4 h_v7 h_v20 h_v24 h_v26 dropping he_v31 e_v31
      step as ⟨e_v32, he_v32⟩
      store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s6 e_v32 (by rw [he_v32]; rfl) h_v31 h_v7 hinv6 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v32, s7, hinv7, h_v32⟩ growing hG carrying h_a0 h_v4 h_v20 h_v24 h_v26 dropping h_v31 h_v7 he_v32 e_v32 v31 v7
      ite_done hinv7 hG with (eo_ite_false_rep _ hx_27 h_v32)
    · ite_branch hbv_27
      ite_stuck hinv5 hG with hx_27)
  store_step with h_ite_v33 as ⟨v33, s6, hinv6, h_v33⟩ growing hG carrying h_a0 h_v4 h_v20 h_v24 h_v26 dropping h_ite_v33 h_v7 hinv5 s5 v7
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s6 0#u32 (0) (by scalar_tac) hinv6 h64 as ⟨v34, s7, hinv7, h_v34⟩ growing hG carrying h_a0 h_v4 h_v20 h_v24 h_v26 h_v33 dropping hinv6 s6
  step as ⟨e_v35, he_v35⟩
  store_step with Store.builtin_spec_list_nth n ih.eo__24eo_5fis_5flist_5fnil s7 e_v35 (by rw [he_v35]; rfl) h_v26 h_v33 h_v34 hinv7 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v35, s8, hinv8, h_v35⟩ growing hG carrying h_a0 h_v4 h_v20 h_v24 dropping h_v26 h_v33 h_v34 he_v35 hinv7 e_v35 s7 v26 v33 v34
  have h_req_v50 := (show requires_3_eo__24eo_5fprog_5fconcat_5funify s8 v35 v20 a0 v4 v24 ⦃ r s' => s'.Inv ∧ s8.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold requires_3_eo__24eo_5fprog_5fconcat_5funify
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s8
    req_same v35 v20 with h_v35 h_v20 using hinv8 hG
    req_stuck h_v35 as hq_v35 using hinv8 hG
    step as ⟨e_v36, he_v36⟩
    store_step with CtorSpec.eo_str_2e_2b_2b.construct s8 e_v36 (by rw [he_v36]; exact empty_args) hinv8 h64 as ⟨v36, s9, hinv9, h_v36⟩ growing hG carrying h_a0 h_v4 h_v20 h_v24 dropping h_v35 he_v36 hinv8 e_v36 s8 v35
    have h_ite_v43 := (show if_1_eo__24eo_5fprog_5fconcat_5funify s9 a0 v4 ⦃ r s' => s'.Inv ∧ s9.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
      unfold if_1_eo__24eo_5fprog_5fconcat_5funify
      have hrem := (hG.rem hrem)
      have hG := Store.Grows.refl s9
      rcases Store.boolean_value_term h_a0 with ⟨hx_37, hbv_37⟩ | ⟨hx_37, hbv_37⟩ | ⟨hx_37, hbv_37⟩
      · ite_branch hbv_37
        step as ⟨e_v37, he_v37⟩
        store_step with CtorSpec.eo_str_2e_2b_2b.construct s9 e_v37 (by rw [he_v37]; exact empty_args) hinv9 h64 as ⟨v37, s10, hinv10, h_v37⟩ growing hG carrying h_v4 h_v20 h_v24 h_v36 dropping h_a0 he_v37 e_v37
        step as ⟨e_v38, he_v38⟩
        store_step with CtorSpec.eo_str_2e_2b_2b.construct s10 e_v38 (by rw [he_v38]; exact empty_args) hinv10 h64 as ⟨v38, s11, hinv11, h_v38⟩ growing hG carrying h_v4 h_v20 h_v24 h_v36 h_v37 dropping he_v38 e_v38
        step as ⟨e_v39, he_v39⟩
        store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s11 e_v39 (by rw [he_v39]; rfl) h_v38 h_v4 hinv11 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v39, s12, hinv12, h_v39⟩ growing hG carrying h_v4 h_v20 h_v24 h_v36 h_v37 dropping h_v38 he_v39 e_v39 v38
        step as ⟨e_v40, he_v40⟩
        store_step with Store.builtin_spec_list_rev n ih.eo__24eo_5fis_5flist_5fnil s12 e_v40 (by rw [he_v40]; rfl) h_v37 h_v39 hinv12 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v40, s13, hinv13, h_v40⟩ growing hG carrying h_v4 h_v20 h_v24 h_v36 dropping h_v37 h_v39 he_v40 e_v40 v37 v39
        ite_done hinv13 hG with (eo_ite_true_rep _ hx_37 h_v40)
      · ite_branch hbv_37
        step as ⟨e_v41, he_v41⟩
        store_step with CtorSpec.eo_str_2e_2b_2b.construct s9 e_v41 (by rw [he_v41]; exact empty_args) hinv9 h64 as ⟨v41, s10, hinv10, h_v41⟩ growing hG carrying h_v4 h_v20 h_v24 h_v36 dropping h_a0 he_v41 e_v41
        step as ⟨e_v42, he_v42⟩
        store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s10 e_v42 (by rw [he_v42]; rfl) h_v41 h_v4 hinv10 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v42, s11, hinv11, h_v42⟩ growing hG carrying h_v20 h_v24 h_v36 dropping h_v4 h_v41 he_v42 e_v42 v4 v41
        ite_done hinv11 hG with (eo_ite_false_rep _ hx_37 h_v42)
      · ite_branch hbv_37
        ite_stuck hinv9 hG with hx_37)
    store_step with h_ite_v43 as ⟨v43, s10, hinv10, h_v43⟩ growing hG carrying h_v20 h_v24 h_v36 dropping h_ite_v43 h_v4 hinv9 s9 v4
    try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
    store_step with Store.literal_int_u32_spec s10 0#u32 (0) (by scalar_tac) hinv10 h64 as ⟨v44, s11, hinv11, h_v44⟩ growing hG carrying h_v20 h_v24 h_v36 h_v43 dropping hinv10 s10
    step as ⟨e_v45, he_v45⟩
    store_step with Store.builtin_spec_list_nth n ih.eo__24eo_5fis_5flist_5fnil s11 e_v45 (by rw [he_v45]; rfl) h_v36 h_v43 h_v44 hinv11 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v45, s12, hinv12, h_v45⟩ growing hG carrying h_v20 h_v24 dropping h_v36 h_v43 h_v44 he_v45 hinv11 e_v45 s11 v36 v43 v44
    have h_req_v49 := (show requires_2_eo__24eo_5fprog_5fconcat_5funify s12 v45 v24 v20 ⦃ r s' => s'.Inv ∧ s12.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
      unfold requires_2_eo__24eo_5fprog_5fconcat_5funify
      have hrem := (hG.rem hrem)
      have hG := Store.Grows.refl s12
      req_same v45 v24 with h_v45 h_v24 using hinv12 hG
      req_stuck h_v45 as hq_v45 using hinv12 hG
      step as ⟨e_v46, he_v46⟩
      store_step with CtorSpec.eo__3d.construct s12 e_v46 (by rw [he_v46]; exact empty_args) hinv12 h64 as ⟨v46, s13, hinv13, h_v46⟩ growing hG carrying h_v20 h_v24 dropping h_v45 he_v46 hinv12 e_v46 s12 v45
      store_step with Store.apply_rep s13 v46 v20 _ _ hinv13 h64 h_v46 h_v20 (by ns_tac) (by ns_tac) as ⟨v47, s14, hinv14, h_v47⟩ growing hG carrying h_v24 dropping h_v20 h_v46 hinv13 s13 v20 v46
      store_step with Store.apply_rep s14 v47 v24 _ _ hinv14 h64 h_v47 h_v24 (by ns_tac) (by ns_tac) as ⟨v48, s15, hinv15, h_v48⟩ growing hG carrying dropping h_v24 h_v47 hinv14 s14 v24 v47
      req_done hinv15 hG with h_v48 using hq_v45)
    store_step with h_req_v49 as ⟨v49, s16, hinv16, h_v49⟩ growing hG carrying dropping h_req_v49 h_v20 h_v24 h_v45 hinv12 s12 v20 v24 v45
    req_done hinv16 hG with h_v49 using hq_v35)
  store_step with h_req_v50 as ⟨v50, s17, hinv17, h_v50⟩ growing hG carrying dropping h_req_v50 h_v20 h_v24 h_v35 h_v4 hinv8 s8 v20 v24 v35 v4
  case_done hinv17 hG with h_v50 in EoCases.__eo_prog_concat_unify.case_0 using hn_a0 hn_v3 hn_v4 hn_v6 hn_v7 hn_v12 hn_v13 hn_v15 hn_v16 hn_v19 hn_v20 hn_v23 hn_v24

/-- logos's `__eo_prog_concat_unify` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fconcat_5funify.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __eo_prog_concat_unify x_a0 x_a1 x_a2 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_concat_unify.case_0 x_a0 x_a1 x_a2] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_concat_unify
  unfold EoCases.__eo_prog_concat_unify.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fconcat_5funify_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24eo_5fprog_5fconcat_5funify s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_concat_unify x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fconcat_5funify.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24eo_5fprog_5fconcat_5funify
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fconcat_5funify_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_concat_unify.case_0

theorem eo__24eo_5fprog_5fconcat_5funify_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fconcat_5funify.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24eo_5fprog_5fconcat_5funify
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fconcat_5funify s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__eo_prog_concat_unify x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fconcat_5funify_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fcong_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fcong s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_cong.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_cong.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fcong
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a1 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_cong.case_0
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__3d.construct s e_v2 (by rw [he_v2]; exact empty_args) hinv h64 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying h_a0 h_v1 dropping h_a1 he_v2 e_v2
  store_step with Store.apply_rep s1 v2 a0 _ _ hinv1 h64 h_v2 h_a0 (by ns_tac) (by ns_tac) as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying h_a0 h_v1 dropping h_v2 hinv1 s1 v2
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo_and.construct s2 e_v4 (by rw [he_v4]; exact empty_args) hinv2 h64 as ⟨v4, s3, hinv3, h_v4⟩ growing hG carrying h_a0 h_v1 h_v3 dropping he_v4 hinv2 e_v4 s2
  step as ⟨e_v5, he_v5⟩
  store_step with Store.builtin_spec_list_rev n ih.eo__24eo_5fis_5flist_5fnil s3 e_v5 (by rw [he_v5]; rfl) h_v4 h_v1 hinv3 h64 (hG.rem hrem) op_not_left_eo_and as ⟨v5, s4, hinv4, h_v5⟩ growing hG carrying h_a0 h_v3 dropping h_v1 h_v4 he_v5 hinv3 e_v5 s3 v1 v4
  store_step with ih.eo__24mk_5fcong_5frhs s4 a0 v5 _ _ hinv4 h64 (hG.rem hrem) h_a0 h_v5 as ⟨v6, s5, hinv5, h_v6⟩ growing hG carrying h_v3 dropping h_a0 h_v5 hinv4 s4 v5
  store_step with Store.apply_mk_rep s5 v3 v6 _ _ hinv5 h64 h_v3 h_v6 as ⟨v7, s6, hinv6, h_v7⟩ growing hG carrying dropping h_v3 h_v6 hinv5 s5 v3 v6
  case_done hinv6 hG with h_v7 in EoCases.__eo_prog_cong.case_0 using hn_a0

/-- logos's `__eo_prog_cong` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fcong.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_cong x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_cong.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_cong
  unfold EoCases.__eo_prog_cong.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fcong_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5fcong s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_cong x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fcong.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5fcong
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fcong_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_cong.case_0

theorem eo__24eo_5fprog_5fcong_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fcong.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5fcong
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fcong s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_cong x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fcong_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fcontra_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_0_eo__24eo_5fprog_5fcontra s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_contra.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_contra.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fcontra
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_contra.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a1 as ⟨v3, x_v3, h_v3⟩ else hinv hG in EoCases.__eo_prog_contra.case_0
  pat_unapply h_v3 as ⟨v5, v6, x_v5, x_v6, h_v5, h_v6, hn_v5, hn_v6⟩ using hinv else hinv hG in EoCases.__eo_prog_contra.case_0
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo_not.construct s e_v7 (by rw [he_v7]; exact empty_args) hinv h64 as ⟨v7, s1, hinv1, h_v7⟩ growing hG carrying h_v1 h_v5 h_v6 dropping h_a0 h_a1 h_v3 he_v7 e_v7 v3
  pat_same v5 v7 with h_v5 h_v7 using hinv1 else hinv1 hG in EoCases.__eo_prog_contra.case_0
  pat_same v6 v1 with h_v6 h_v1 using hinv1 else hinv1 hG in EoCases.__eo_prog_contra.case_0
  store_step with Store.literal_boolean_spec s1 false hinv1 h64 as ⟨v8, s2, hinv2, h_v8⟩ growing hG carrying dropping h_v1 h_v5 h_v6 h_v7 hinv1 s1 v1 v5 v6 v7
  case_done hinv2 hG with h_v8 in EoCases.__eo_prog_contra.case_0 using hn_v5 hn_v6

/-- logos's `__eo_prog_contra` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fcontra.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_contra x_a0 x_a1 =
      (firstSome [EoCases.__eo_prog_contra.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_contra
  unfold EoCases.__eo_prog_contra.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fcontra_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5fcontra s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_contra x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fcontra.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5fcontra
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fprog_5fcontra_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using
  body_stuck hinv1 hG using hc0 in EoCases.__eo_prog_contra.case_0

theorem eo__24eo_5fprog_5fcontra_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fcontra.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5fcontra
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fcontra s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_contra x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fcontra_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fdistinct_2dbinary_2delim_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fdistinct_2dbinary_2delim s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_distinct_binary_elim.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_distinct_binary_elim.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fdistinct_2dbinary_2delim
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 dropping he_v0 e_v0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_distinct.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0 dropping he_v1 hinv1 e_v1 s1
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__40_40TypedList_2econs.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 dropping he_v2 hinv2 e_v2 s2
  store_step with Store.apply_rep s3 v2 a0 _ _ hinv3 h64 h_v2 h_a0 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 dropping h_v2 hinv3 s3 v2
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo__40_40TypedList_2econs.construct s4 e_v4 (by rw [he_v4]; exact empty_args) hinv4 h64 as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v3 dropping he_v4 hinv4 e_v4 s4
  store_step with Store.apply_rep s5 v4 a1 _ _ hinv5 h64 h_v4 h_a1 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v3 dropping h_v4 hinv5 s5 v4
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__40_40TypedList_2econs.construct s6 e_v6 (by rw [he_v6]; exact empty_args) hinv6 h64 as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v3 h_v5 dropping he_v6 hinv6 e_v6 s6
  store_step with ih.eo__24eo_5ftypeof s7 a0 _ hinv7 h64 (hG.rem hrem) h_a0 as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v3 h_v5 h_v6 dropping hinv7 s7
  store_step with ih.eo__24eo_5fnil s8 v6 v7 _ _ hinv8 h64 (hG.rem hrem) h_v6 h_v7 as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v3 h_v5 dropping h_v6 h_v7 hinv8 s8 v6 v7
  store_step with Store.apply_mk_rep s9 v5 v8 _ _ hinv9 h64 h_v5 h_v8 as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v3 dropping h_v5 h_v8 hinv9 s9 v5 v8
  store_step with Store.apply_mk_rep s10 v3 v9 _ _ hinv10 h64 h_v3 h_v9 as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 dropping h_v3 h_v9 hinv10 s10 v3 v9
  store_step with Store.apply_mk_rep s11 v1 v10 _ _ hinv11 h64 h_v1 h_v10 as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_a0 h_a1 h_v0 dropping h_v1 h_v10 hinv11 s11 v1 v10
  store_step with Store.apply_mk_rep s12 v0 v11 _ _ hinv12 h64 h_v0 h_v11 as ⟨v12, s13, hinv13, h_v12⟩ growing hG carrying h_a0 h_a1 dropping h_v0 h_v11 hinv12 s12 v0 v11
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo_not.construct s13 e_v13 (by rw [he_v13]; exact empty_args) hinv13 h64 as ⟨v13, s14, hinv14, h_v13⟩ growing hG carrying h_a0 h_a1 h_v12 dropping he_v13 hinv13 e_v13 s13
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo__3d.construct s14 e_v14 (by rw [he_v14]; exact empty_args) hinv14 h64 as ⟨v14, s15, hinv15, h_v14⟩ growing hG carrying h_a0 h_a1 h_v12 h_v13 dropping he_v14 hinv14 e_v14 s14
  store_step with Store.apply_rep s15 v14 a0 _ _ hinv15 h64 h_v14 h_a0 (by ns_tac) (by ns_tac) as ⟨v15, s16, hinv16, h_v15⟩ growing hG carrying h_a1 h_v12 h_v13 dropping h_a0 h_v14 hinv15 s15 v14
  store_step with Store.apply_rep s16 v15 a1 _ _ hinv16 h64 h_v15 h_a1 (by ns_tac) (by ns_tac) as ⟨v16, s17, hinv17, h_v16⟩ growing hG carrying h_v12 h_v13 dropping h_a1 h_v15 hinv16 s16 v15
  store_step with Store.apply_rep s17 v13 v16 _ _ hinv17 h64 h_v13 h_v16 (by ns_tac) (by ns_tac) as ⟨v17, s18, hinv18, h_v17⟩ growing hG carrying h_v12 dropping h_v13 h_v16 hinv17 s17 v13 v16
  store_step with Store.apply_mk_rep s18 v12 v17 _ _ hinv18 h64 h_v12 h_v17 as ⟨v18, s19, hinv19, h_v18⟩ growing hG carrying dropping h_v12 h_v17 hinv18 s18 v12 v17
  case_done hinv19 hG with h_v18 in EoCases.__eo_prog_distinct_binary_elim.case_0 using hn_a0 hn_a1

/-- logos's `__eo_prog_distinct_binary_elim` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fdistinct_2dbinary_2delim.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_distinct_binary_elim x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_distinct_binary_elim.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_distinct_binary_elim
  unfold EoCases.__eo_prog_distinct_binary_elim.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fdistinct_2dbinary_2delim_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5fdistinct_2dbinary_2delim s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_distinct_binary_elim x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fdistinct_2dbinary_2delim.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5fdistinct_2dbinary_2delim
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fdistinct_2dbinary_2delim_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_distinct_binary_elim.case_0

theorem eo__24eo_5fprog_5fdistinct_2dbinary_2delim_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fdistinct_2dbinary_2delim.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5fdistinct_2dbinary_2delim
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fdistinct_2dbinary_2delim s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_distinct_binary_elim x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fdistinct_2dbinary_2delim_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fdistinct_2dcard_2dconflict_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fdistinct_2dcard_2dconflict s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_distinct_card_conflict.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_distinct_card_conflict.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fdistinct_2dcard_2dconflict
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_prog_distinct_card_conflict.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_prog_distinct_card_conflict.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__3d.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_prog_distinct_card_conflict.case_0
  pat_unapply h_v5 as ⟨v8, v9, x_v8, x_v9, h_v8, h_v9, hn_v8, hn_v9⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_distinct_card_conflict.case_0
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo_distinct.construct s1 e_v10 (by rw [he_v10]; exact empty_args) hinv1 h64 as ⟨v10, s2, hinv2, h_v10⟩ growing hG carrying h_v2 h_v8 h_v9 dropping h_v4 h_v5 h_v6 he_v10 hinv1 e_v10 s1 v4 v5 v6
  pat_same v8 v10 with h_v8 h_v10 using hinv2 else hinv2 hG in EoCases.__eo_prog_distinct_card_conflict.case_0
  store_step with Store.literal_boolean_spec s2 false hinv2 h64 as ⟨v11, s3, hinv3, h_v11⟩ growing hG carrying h_v2 h_v9 dropping h_v10 h_v8 hinv2 s2 v10 v8
  pat_same v2 v11 with h_v2 h_v11 using hinv3 else hinv3 hG in EoCases.__eo_prog_distinct_card_conflict.case_0
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo__40_40TypedList_2econs.construct s3 e_v12 (by rw [he_v12]; exact empty_args) hinv3 h64 as ⟨v12, s4, hinv4, h_v12⟩ growing hG carrying h_v9 dropping h_v11 h_v2 he_v12 hinv3 e_v12 s3 v11 v2
  step as ⟨e_v13, he_v13⟩
  store_step with Store.builtin_spec_list_len n ih.eo__24eo_5fis_5flist_5fnil s4 e_v13 (by rw [he_v13]; rfl) h_v12 h_v9 hinv4 h64 (hG.rem hrem) op_not_left_eo__40_40TypedList_2econs as ⟨v13, s5, hinv5, h_v13⟩ growing hG carrying h_v9 dropping h_v12 he_v13 hinv4 e_v13 s4 v12
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo__40_40TypedList_2econs.construct s5 e_v14 (by rw [he_v14]; exact empty_args) hinv5 h64 as ⟨v14, s6, hinv6, h_v14⟩ growing hG carrying h_v9 h_v13 dropping he_v14 hinv5 e_v14 s5
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s6 0#u32 (0) (by scalar_tac) hinv6 h64 as ⟨v15, s7, hinv7, h_v15⟩ growing hG carrying h_v9 h_v13 h_v14 dropping hinv6 s6
  store_step with ih.eo__24assoc_5fnil_5fnth_5ftype s7 v14 v9 v15 _ _ _ hinv7 h64 (hG.rem hrem) h_v14 h_v9 h_v15 as ⟨v16, s8, hinv8, h_v16⟩ growing hG carrying h_v9 h_v13 dropping h_v14 h_v15 hinv7 s7 v14 v15
  store_step with ih.eo__24compute_5fcard s8 v16 _ hinv8 h64 (hG.rem hrem) h_v16 as ⟨v17, s9, hinv9, h_v17⟩ growing hG carrying h_v9 h_v13 dropping h_v16 hinv8 s8 v16
  step as ⟨e_v18, he_v18⟩
  store_step with Store.builtin_spec_gt s9 e_v18 (by rw [he_v18]; rfl) h_v13 h_v17 hinv9 h64 as ⟨v18, s10, hinv10, h_v18⟩ growing hG carrying h_v9 dropping h_v13 h_v17 he_v18 hinv9 e_v18 s9 v13 v17
  store_step with Store.literal_boolean_spec s10 true hinv10 h64 as ⟨v19, s11, hinv11, h_v19⟩ growing hG carrying h_v9 h_v18 dropping hinv10 s10
  have h_req_v26 := (show requires_0_eo__24eo_5fprog_5fdistinct_2dcard_2dconflict s11 v18 v19 v9 ⦃ r s' => s'.Inv ∧ s11.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold requires_0_eo__24eo_5fprog_5fdistinct_2dcard_2dconflict
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s11
    req_same v18 v19 with h_v18 h_v19 using hinv11 hG
    req_stuck h_v18 as hq_v18 using hinv11 hG
    step as ⟨e_v20, he_v20⟩
    store_step with CtorSpec.eo__3d.construct s11 e_v20 (by rw [he_v20]; exact empty_args) hinv11 h64 as ⟨v20, s12, hinv12, h_v20⟩ growing hG carrying h_v9 dropping h_v18 h_v19 he_v20 hinv11 e_v20 s11 v18 v19
    step as ⟨e_v21, he_v21⟩
    store_step with CtorSpec.eo_distinct.construct s12 e_v21 (by rw [he_v21]; exact empty_args) hinv12 h64 as ⟨v21, s13, hinv13, h_v21⟩ growing hG carrying h_v9 h_v20 dropping he_v21 hinv12 e_v21 s12
    store_step with Store.apply_rep s13 v21 v9 _ _ hinv13 h64 h_v21 h_v9 (by ns_tac) (by ns_tac) as ⟨v22, s14, hinv14, h_v22⟩ growing hG carrying h_v20 dropping h_v21 h_v9 hinv13 s13 v21 v9
    store_step with Store.apply_rep s14 v20 v22 _ _ hinv14 h64 h_v20 h_v22 (by ns_tac) (by ns_tac) as ⟨v23, s15, hinv15, h_v23⟩ growing hG carrying dropping h_v20 h_v22 hinv14 s14 v20 v22
    store_step with Store.literal_boolean_spec s15 false hinv15 h64 as ⟨v24, s16, hinv16, h_v24⟩ growing hG carrying h_v23 dropping hinv15 s15
    store_step with Store.apply_rep s16 v23 v24 _ _ hinv16 h64 h_v23 h_v24 (by ns_tac) (by ns_tac) as ⟨v25, s17, hinv17, h_v25⟩ growing hG carrying dropping h_v23 h_v24 hinv16 s16 v23 v24
    req_done hinv17 hG with h_v25 using hq_v18)
  store_step with h_req_v26 as ⟨v26, s18, hinv18, h_v26⟩ growing hG carrying dropping h_req_v26 h_v18 h_v19 h_v9 hinv11 s11 v18 v19 v9
  case_done hinv18 hG with h_v26 in EoCases.__eo_prog_distinct_card_conflict.case_0 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5 hn_v8 hn_v9

/-- logos's `__eo_prog_distinct_card_conflict` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fdistinct_2dcard_2dconflict.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_distinct_card_conflict x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_distinct_card_conflict.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_distinct_card_conflict
  unfold EoCases.__eo_prog_distinct_card_conflict.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fdistinct_2dcard_2dconflict_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fdistinct_2dcard_2dconflict s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_distinct_card_conflict x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fdistinct_2dcard_2dconflict.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fdistinct_2dcard_2dconflict
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fdistinct_2dcard_2dconflict_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_distinct_card_conflict.case_0

theorem eo__24eo_5fprog_5fdistinct_2dcard_2dconflict_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fdistinct_2dcard_2dconflict.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fdistinct_2dcard_2dconflict
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fdistinct_2dcard_2dconflict s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_distinct_card_conflict x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fdistinct_2dcard_2dconflict_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fdistinct_2delim_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fdistinct_2delim s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_distinct_elim.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_distinct_elim.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fdistinct_2delim
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_prog_distinct_elim.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_prog_distinct_elim.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__3d.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_prog_distinct_elim.case_0
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo_and.construct s1 e_v7 (by rw [he_v7]; exact empty_args) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 h_v5 dropping h_v4 h_v6 he_v7 hinv1 e_v7 s1 v4 v6
  store_step with ih.eo__24mk_5fdistinct_5felim s2 v5 _ hinv2 h64 (hG.rem hrem) h_v5 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v2 h_v5 h_v7 dropping hinv2 s2
  step as ⟨e_v9, he_v9⟩
  store_step with Store.builtin_spec_list_singleton_elim n ih.eo__24eo_5fis_5flist_5fnil s3 e_v9 (by rw [he_v9]; rfl) h_v7 h_v8 hinv3 h64 (hG.rem hrem) op_not_left_eo_and op_nil_apply_eo_and as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_v2 h_v5 dropping h_v7 h_v8 he_v9 hinv3 e_v9 s3 v7 v8
  have h_req_v13 := (show requires_0_eo__24eo_5fprog_5fdistinct_2delim s4 v9 v2 v5 ⦃ r s' => s'.Inv ∧ s4.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold requires_0_eo__24eo_5fprog_5fdistinct_2delim
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s4
    req_same v9 v2 with h_v9 h_v2 using hinv4 hG
    req_stuck h_v9 as hq_v9 using hinv4 hG
    step as ⟨e_v10, he_v10⟩
    store_step with CtorSpec.eo__3d.construct s4 e_v10 (by rw [he_v10]; exact empty_args) hinv4 h64 as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_v2 h_v5 dropping h_v9 he_v10 hinv4 e_v10 s4 v9
    store_step with Store.apply_rep s5 v10 v5 _ _ hinv5 h64 h_v10 h_v5 (by ns_tac) (by ns_tac) as ⟨v11, s6, hinv6, h_v11⟩ growing hG carrying h_v2 dropping h_v10 h_v5 hinv5 s5 v10 v5
    store_step with Store.apply_rep s6 v11 v2 _ _ hinv6 h64 h_v11 h_v2 (by ns_tac) (by ns_tac) as ⟨v12, s7, hinv7, h_v12⟩ growing hG carrying dropping h_v11 h_v2 hinv6 s6 v11 v2
    req_done hinv7 hG with h_v12 using hq_v9)
  store_step with h_req_v13 as ⟨v13, s8, hinv8, h_v13⟩ growing hG carrying dropping h_req_v13 h_v2 h_v5 h_v9 hinv4 s4 v2 v5 v9
  case_done hinv8 hG with h_v13 in EoCases.__eo_prog_distinct_elim.case_0 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

/-- logos's `__eo_prog_distinct_elim` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fdistinct_2delim.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_distinct_elim x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_distinct_elim.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_distinct_elim
  unfold EoCases.__eo_prog_distinct_elim.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fdistinct_2delim_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fdistinct_2delim s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_distinct_elim x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fdistinct_2delim.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fdistinct_2delim
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fdistinct_2delim_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_distinct_elim.case_0

theorem eo__24eo_5fprog_5fdistinct_2delim_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fdistinct_2delim.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fdistinct_2delim
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fdistinct_2delim s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_distinct_elim x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fdistinct_2delim_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fdistinct_2dfalse_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fdistinct_2dfalse s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_distinct_false.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_distinct_false.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fdistinct_2dfalse
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_prog_distinct_false.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_prog_distinct_false.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__3d.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_prog_distinct_false.case_0
  pat_unapply h_v5 as ⟨v8, v9, x_v8, x_v9, h_v8, h_v9, hn_v8, hn_v9⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_distinct_false.case_0
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo_distinct.construct s1 e_v10 (by rw [he_v10]; exact empty_args) hinv1 h64 as ⟨v10, s2, hinv2, h_v10⟩ growing hG carrying h_v2 h_v8 h_v9 dropping h_v4 h_v5 h_v6 he_v10 hinv1 e_v10 s1 v4 v5 v6
  pat_same v8 v10 with h_v8 h_v10 using hinv2 else hinv2 hG in EoCases.__eo_prog_distinct_false.case_0
  store_step with Store.literal_boolean_spec s2 false hinv2 h64 as ⟨v11, s3, hinv3, h_v11⟩ growing hG carrying h_v2 h_v9 dropping h_v10 h_v8 hinv2 s2 v10 v8
  pat_same v2 v11 with h_v2 h_v11 using hinv3 else hinv3 hG in EoCases.__eo_prog_distinct_false.case_0
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo__40_40TypedList_2econs.construct s3 e_v12 (by rw [he_v12]; exact empty_args) hinv3 h64 as ⟨v12, s4, hinv4, h_v12⟩ growing hG carrying h_v9 dropping h_v11 h_v2 he_v12 hinv3 e_v12 s3 v11 v2
  step as ⟨e_v13, he_v13⟩
  store_step with Store.builtin_spec_list_setof n ih.eo__24eo_5fis_5flist_5fnil s4 e_v13 (by rw [he_v13]; rfl) h_v12 h_v9 hinv4 h64 (hG.rem hrem) op_not_left_eo__40_40TypedList_2econs as ⟨v13, s5, hinv5, h_v13⟩ growing hG carrying h_v9 dropping h_v12 he_v13 hinv4 e_v13 s4 v12
  step as ⟨e_v14, he_v14⟩
  store_step with Store.builtin_spec_eq s5 e_v14 (by rw [he_v14]; rfl) h_v13 h_v9 hinv5 h64 as ⟨v14, s6, hinv6, h_v14⟩ growing hG carrying h_v9 dropping h_v13 he_v14 hinv5 e_v14 s5 v13
  store_step with Store.literal_boolean_spec s6 false hinv6 h64 as ⟨v15, s7, hinv7, h_v15⟩ growing hG carrying h_v9 h_v14 dropping hinv6 s6
  have h_req_v22 := (show requires_0_eo__24eo_5fprog_5fdistinct_2dfalse s7 v14 v15 v9 ⦃ r s' => s'.Inv ∧ s7.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold requires_0_eo__24eo_5fprog_5fdistinct_2dfalse
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s7
    req_same v14 v15 with h_v14 h_v15 using hinv7 hG
    req_stuck h_v14 as hq_v14 using hinv7 hG
    step as ⟨e_v16, he_v16⟩
    store_step with CtorSpec.eo__3d.construct s7 e_v16 (by rw [he_v16]; exact empty_args) hinv7 h64 as ⟨v16, s8, hinv8, h_v16⟩ growing hG carrying h_v9 dropping h_v14 h_v15 he_v16 hinv7 e_v16 s7 v14 v15
    step as ⟨e_v17, he_v17⟩
    store_step with CtorSpec.eo_distinct.construct s8 e_v17 (by rw [he_v17]; exact empty_args) hinv8 h64 as ⟨v17, s9, hinv9, h_v17⟩ growing hG carrying h_v9 h_v16 dropping he_v17 hinv8 e_v17 s8
    store_step with Store.apply_rep s9 v17 v9 _ _ hinv9 h64 h_v17 h_v9 (by ns_tac) (by ns_tac) as ⟨v18, s10, hinv10, h_v18⟩ growing hG carrying h_v16 dropping h_v17 h_v9 hinv9 s9 v17 v9
    store_step with Store.apply_rep s10 v16 v18 _ _ hinv10 h64 h_v16 h_v18 (by ns_tac) (by ns_tac) as ⟨v19, s11, hinv11, h_v19⟩ growing hG carrying dropping h_v16 h_v18 hinv10 s10 v16 v18
    store_step with Store.literal_boolean_spec s11 false hinv11 h64 as ⟨v20, s12, hinv12, h_v20⟩ growing hG carrying h_v19 dropping hinv11 s11
    store_step with Store.apply_rep s12 v19 v20 _ _ hinv12 h64 h_v19 h_v20 (by ns_tac) (by ns_tac) as ⟨v21, s13, hinv13, h_v21⟩ growing hG carrying dropping h_v19 h_v20 hinv12 s12 v19 v20
    req_done hinv13 hG with h_v21 using hq_v14)
  store_step with h_req_v22 as ⟨v22, s14, hinv14, h_v22⟩ growing hG carrying dropping h_req_v22 h_v14 h_v15 h_v9 hinv7 s7 v14 v15 v9
  case_done hinv14 hG with h_v22 in EoCases.__eo_prog_distinct_false.case_0 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5 hn_v8 hn_v9

/-- logos's `__eo_prog_distinct_false` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fdistinct_2dfalse.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_distinct_false x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_distinct_false.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_distinct_false
  unfold EoCases.__eo_prog_distinct_false.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fdistinct_2dfalse_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fdistinct_2dfalse s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_distinct_false x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fdistinct_2dfalse.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fdistinct_2dfalse
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fdistinct_2dfalse_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_distinct_false.case_0

theorem eo__24eo_5fprog_5fdistinct_2dfalse_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fdistinct_2dfalse.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fdistinct_2dfalse
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fdistinct_2dfalse s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_distinct_false x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fdistinct_2dfalse_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fdistinct_2dtrue_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fdistinct_2dtrue s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_distinct_true.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_distinct_true.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fdistinct_2dtrue
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_prog_distinct_true.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_prog_distinct_true.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__3d.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_prog_distinct_true.case_0
  pat_unapply h_v5 as ⟨v8, v9, x_v8, x_v9, h_v8, h_v9, hn_v8, hn_v9⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_distinct_true.case_0
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo_distinct.construct s1 e_v10 (by rw [he_v10]; exact empty_args) hinv1 h64 as ⟨v10, s2, hinv2, h_v10⟩ growing hG carrying h_v2 h_v8 h_v9 dropping h_v4 h_v5 h_v6 he_v10 hinv1 e_v10 s1 v4 v5 v6
  pat_same v8 v10 with h_v8 h_v10 using hinv2 else hinv2 hG in EoCases.__eo_prog_distinct_true.case_0
  store_step with Store.literal_boolean_spec s2 true hinv2 h64 as ⟨v11, s3, hinv3, h_v11⟩ growing hG carrying h_v2 h_v9 dropping h_v10 h_v8 hinv2 s2 v10 v8
  pat_same v2 v11 with h_v2 h_v11 using hinv3 else hinv3 hG in EoCases.__eo_prog_distinct_true.case_0
  store_step with ih.eo__24eo_5ftypeof s3 v9 _ hinv3 h64 (hG.rem hrem) h_v9 as ⟨v12, s4, hinv4, h_v12⟩ growing hG carrying h_v9 dropping h_v11 h_v2 hinv3 s3 v11 v2
  store_step with ih.eo__24typed_5flist_5felement_5ftype s4 v12 _ hinv4 h64 (hG.rem hrem) h_v12 as ⟨v13, s5, hinv5, h_v13⟩ growing hG carrying h_v9 dropping h_v12 hinv4 s4 v12
  store_step with ih.eo__24are_5fdistinct_5fterms_5flist s5 v9 v13 _ _ hinv5 h64 (hG.rem hrem) h_v9 h_v13 as ⟨v14, s6, hinv6, h_v14⟩ growing hG carrying h_v9 dropping h_v13 hinv5 s5 v13
  store_step with Store.literal_boolean_spec s6 true hinv6 h64 as ⟨v15, s7, hinv7, h_v15⟩ growing hG carrying h_v9 h_v14 dropping hinv6 s6
  have h_req_v22 := (show requires_0_eo__24eo_5fprog_5fdistinct_2dtrue s7 v14 v15 v9 ⦃ r s' => s'.Inv ∧ s7.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold requires_0_eo__24eo_5fprog_5fdistinct_2dtrue
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s7
    req_same v14 v15 with h_v14 h_v15 using hinv7 hG
    req_stuck h_v14 as hq_v14 using hinv7 hG
    step as ⟨e_v16, he_v16⟩
    store_step with CtorSpec.eo__3d.construct s7 e_v16 (by rw [he_v16]; exact empty_args) hinv7 h64 as ⟨v16, s8, hinv8, h_v16⟩ growing hG carrying h_v9 dropping h_v14 h_v15 he_v16 hinv7 e_v16 s7 v14 v15
    step as ⟨e_v17, he_v17⟩
    store_step with CtorSpec.eo_distinct.construct s8 e_v17 (by rw [he_v17]; exact empty_args) hinv8 h64 as ⟨v17, s9, hinv9, h_v17⟩ growing hG carrying h_v9 h_v16 dropping he_v17 hinv8 e_v17 s8
    store_step with Store.apply_rep s9 v17 v9 _ _ hinv9 h64 h_v17 h_v9 (by ns_tac) (by ns_tac) as ⟨v18, s10, hinv10, h_v18⟩ growing hG carrying h_v16 dropping h_v17 h_v9 hinv9 s9 v17 v9
    store_step with Store.apply_rep s10 v16 v18 _ _ hinv10 h64 h_v16 h_v18 (by ns_tac) (by ns_tac) as ⟨v19, s11, hinv11, h_v19⟩ growing hG carrying dropping h_v16 h_v18 hinv10 s10 v16 v18
    store_step with Store.literal_boolean_spec s11 true hinv11 h64 as ⟨v20, s12, hinv12, h_v20⟩ growing hG carrying h_v19 dropping hinv11 s11
    store_step with Store.apply_rep s12 v19 v20 _ _ hinv12 h64 h_v19 h_v20 (by ns_tac) (by ns_tac) as ⟨v21, s13, hinv13, h_v21⟩ growing hG carrying dropping h_v19 h_v20 hinv12 s12 v19 v20
    req_done hinv13 hG with h_v21 using hq_v14)
  store_step with h_req_v22 as ⟨v22, s14, hinv14, h_v22⟩ growing hG carrying dropping h_req_v22 h_v14 h_v15 h_v9 hinv7 s7 v14 v15 v9
  case_done hinv14 hG with h_v22 in EoCases.__eo_prog_distinct_true.case_0 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5 hn_v8 hn_v9

/-- logos's `__eo_prog_distinct_true` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fdistinct_2dtrue.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_distinct_true x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_distinct_true.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_distinct_true
  unfold EoCases.__eo_prog_distinct_true.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fdistinct_2dtrue_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fdistinct_2dtrue s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_distinct_true x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fdistinct_2dtrue.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fdistinct_2dtrue
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fdistinct_2dtrue_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_distinct_true.case_0

theorem eo__24eo_5fprog_5fdistinct_2dtrue_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fdistinct_2dtrue.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fdistinct_2dtrue
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fdistinct_2dtrue s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_distinct_true x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fdistinct_2dtrue_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fdistinct_5fvalues_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fdistinct_5fvalues s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_distinct_values.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_distinct_values.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fdistinct_5fvalues
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with Store.builtin_spec_eq s e_v0 (by rw [he_v0]; rfl) h_a0 h_a1 hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 dropping he_v0 e_v0
  have h_ite_v4 := (show if_0_eo__24eo_5fprog_5fdistinct_5fvalues s1 v0 a0 a1 ⦃ r s' => s'.Inv ∧ s1.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_0_eo__24eo_5fprog_5fdistinct_5fvalues
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s1
    rcases Store.boolean_value_term h_v0 with ⟨hx_1, hbv_1⟩ | ⟨hx_1, hbv_1⟩ | ⟨hx_1, hbv_1⟩
    · ite_branch hbv_1
      store_step with Store.literal_boolean_spec s1 false hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 dropping h_v0 v0
      ite_done hinv2 hG with (eo_ite_true_rep _ hx_1 h_v1)
    · ite_branch hbv_1
      store_step with ih.eo__24eo_5ftypeof s1 a0 _ hinv1 h64 (hG.rem hrem) h_a0 as ⟨v2, s2, hinv2, h_v2⟩ growing hG carrying h_a0 h_a1 dropping h_v0 v0
      store_step with ih.eo__24are_5fdistinct_5fterms_5ftype s2 a0 a1 v2 _ _ _ hinv2 h64 (hG.rem hrem) h_a0 h_a1 h_v2 as ⟨v3, s3, hinv3, h_v3⟩ growing hG carrying h_a0 h_a1 dropping h_v2 v2
      ite_done hinv3 hG with (eo_ite_false_rep _ hx_1 h_v3)
    · ite_branch hbv_1
      ite_stuck hinv1 hG with hx_1)
  store_step with h_ite_v4 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_a1 dropping h_ite_v4 h_v0 hinv1 s1 v0
  store_step with Store.literal_boolean_spec s2 true hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_a1 h_v4 dropping hinv2 s2
  have h_req_v11 := (show requires_1_eo__24eo_5fprog_5fdistinct_5fvalues s3 v4 v5 a0 a1 ⦃ r s' => s'.Inv ∧ s3.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold requires_1_eo__24eo_5fprog_5fdistinct_5fvalues
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s3
    req_same v4 v5 with h_v4 h_v5 using hinv3 hG
    req_stuck h_v4 as hq_v4 using hinv3 hG
    step as ⟨e_v6, he_v6⟩
    store_step with CtorSpec.eo_not.construct s3 e_v6 (by rw [he_v6]; exact empty_args) hinv3 h64 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_a1 dropping h_v4 h_v5 he_v6 hinv3 e_v6 s3 v4 v5
    step as ⟨e_v7, he_v7⟩
    store_step with CtorSpec.eo__3d.construct s4 e_v7 (by rw [he_v7]; exact empty_args) hinv4 h64 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_a0 h_a1 h_v6 dropping he_v7 hinv4 e_v7 s4
    store_step with Store.apply_rep s5 v7 a0 _ _ hinv5 h64 h_v7 h_a0 (by ns_tac) (by ns_tac) as ⟨v8, s6, hinv6, h_v8⟩ growing hG carrying h_a1 h_v6 dropping h_a0 h_v7 hinv5 s5 v7
    store_step with Store.apply_rep s6 v8 a1 _ _ hinv6 h64 h_v8 h_a1 (by ns_tac) (by ns_tac) as ⟨v9, s7, hinv7, h_v9⟩ growing hG carrying h_v6 dropping h_a1 h_v8 hinv6 s6 v8
    store_step with Store.apply_rep s7 v6 v9 _ _ hinv7 h64 h_v6 h_v9 (by ns_tac) (by ns_tac) as ⟨v10, s8, hinv8, h_v10⟩ growing hG carrying dropping h_v6 h_v9 hinv7 s7 v6 v9
    req_done hinv8 hG with h_v10 using hq_v4)
  store_step with h_req_v11 as ⟨v11, s9, hinv9, h_v11⟩ growing hG carrying dropping h_a0 h_a1 h_req_v11 h_v4 h_v5 hinv3 s3 v4 v5
  case_done hinv9 hG with h_v11 in EoCases.__eo_prog_distinct_values.case_0 using hn_a0 hn_a1

/-- logos's `__eo_prog_distinct_values` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fdistinct_5fvalues.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_distinct_values x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_distinct_values.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_distinct_values
  unfold EoCases.__eo_prog_distinct_values.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fdistinct_5fvalues_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5fdistinct_5fvalues s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_distinct_values x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fdistinct_5fvalues.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5fdistinct_5fvalues
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fdistinct_5fvalues_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_distinct_values.case_0

theorem eo__24eo_5fprog_5fdistinct_5fvalues_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fdistinct_5fvalues.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5fdistinct_5fvalues
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fdistinct_5fvalues s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_distinct_values x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fdistinct_5fvalues_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fdt_2dcollapse_2dselector_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fdt_2dcollapse_2dselector s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_dt_collapse_selector.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_dt_collapse_selector.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fdt_2dcollapse_2dselector
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_prog_dt_collapse_selector.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_prog_dt_collapse_selector.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__3d.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_prog_dt_collapse_selector.case_0
  pat_unapply h_v5 as ⟨v8, v9, x_v8, x_v9, h_v8, h_v9, hn_v8, hn_v9⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_dt_collapse_selector.case_0
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s1 e_v10 (by rw [he_v10]; exact empty_args) hinv1 h64 as ⟨v10, s2, hinv2, h_v10⟩ growing hG carrying h_v2 h_v8 h_v9 dropping h_v4 h_v5 h_v6 he_v10 hinv1 e_v10 s1 v4 v5 v6
  store_step with ih.eo__24dt_5farg_5flist s2 v9 _ hinv2 h64 (hG.rem hrem) h_v9 as ⟨v11, s3, hinv3, h_v11⟩ growing hG carrying h_v2 h_v8 h_v9 h_v10 dropping hinv2 s2
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s3 e_v12 (by rw [he_v12]; exact empty_args) hinv3 h64 as ⟨v12, s4, hinv4, h_v12⟩ growing hG carrying h_v2 h_v8 h_v9 h_v10 h_v11 dropping he_v12 hinv3 e_v12 s3
  store_step with ih.eo__24eo_5ftypeof s4 v9 _ hinv4 h64 (hG.rem hrem) h_v9 as ⟨v13, s5, hinv5, h_v13⟩ growing hG carrying h_v2 h_v8 h_v9 h_v10 h_v11 h_v12 dropping hinv4 s4
  store_step with ih.eo__24dt_5fget_5fselectors_5fof_5fapp s5 v13 v9 _ _ hinv5 h64 (hG.rem hrem) h_v13 h_v9 as ⟨v14, s6, hinv6, h_v14⟩ growing hG carrying h_v2 h_v8 h_v9 h_v10 h_v11 h_v12 dropping h_v13 hinv5 s5 v13
  step as ⟨e_v15, he_v15⟩
  store_step with Store.builtin_spec_list_find n ih.eo__24eo_5fis_5flist_5fnil s6 e_v15 (by rw [he_v15]; rfl) h_v12 h_v14 h_v8 hinv6 h64 (hG.rem hrem) (by not_left_tac) as ⟨v15, s7, hinv7, h_v15⟩ growing hG carrying h_v2 h_v8 h_v9 h_v10 h_v11 dropping h_v12 h_v14 he_v15 hinv6 e_v15 s6 v12 v14
  store_step with ih.eo__24assoc_5fnil_5fnth s7 v10 v11 v15 _ _ _ hinv7 h64 (hG.rem hrem) h_v10 h_v11 h_v15 as ⟨v16, s8, hinv8, h_v16⟩ growing hG carrying h_v2 h_v8 h_v9 dropping h_v10 h_v11 h_v15 hinv7 s7 v10 v11 v15
  have h_req_v21 := (show requires_0_eo__24eo_5fprog_5fdt_2dcollapse_2dselector s8 v16 v2 v8 v9 ⦃ r s' => s'.Inv ∧ s8.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold requires_0_eo__24eo_5fprog_5fdt_2dcollapse_2dselector
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s8
    req_same v16 v2 with h_v16 h_v2 using hinv8 hG
    req_stuck h_v16 as hq_v16 using hinv8 hG
    step as ⟨e_v17, he_v17⟩
    store_step with CtorSpec.eo__3d.construct s8 e_v17 (by rw [he_v17]; exact empty_args) hinv8 h64 as ⟨v17, s9, hinv9, h_v17⟩ growing hG carrying h_v2 h_v8 h_v9 dropping h_v16 he_v17 hinv8 e_v17 s8 v16
    store_step with Store.apply_rep s9 v8 v9 _ _ hinv9 h64 h_v8 h_v9 (by ns_tac) (by ns_tac) as ⟨v18, s10, hinv10, h_v18⟩ growing hG carrying h_v2 h_v17 dropping h_v8 h_v9 hinv9 s9 v8 v9
    store_step with Store.apply_rep s10 v17 v18 _ _ hinv10 h64 h_v17 h_v18 (by ns_tac) (by ns_tac) as ⟨v19, s11, hinv11, h_v19⟩ growing hG carrying h_v2 dropping h_v17 h_v18 hinv10 s10 v17 v18
    store_step with Store.apply_rep s11 v19 v2 _ _ hinv11 h64 h_v19 h_v2 (by ns_tac) (by ns_tac) as ⟨v20, s12, hinv12, h_v20⟩ growing hG carrying dropping h_v19 h_v2 hinv11 s11 v19 v2
    req_done hinv12 hG with h_v20 using hq_v16)
  store_step with h_req_v21 as ⟨v21, s13, hinv13, h_v21⟩ growing hG carrying dropping h_req_v21 h_v16 h_v2 h_v8 h_v9 hinv8 s8 v16 v2 v8 v9
  case_done hinv13 hG with h_v21 in EoCases.__eo_prog_dt_collapse_selector.case_0 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5 hn_v8 hn_v9

/-- logos's `__eo_prog_dt_collapse_selector` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fdt_2dcollapse_2dselector.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_dt_collapse_selector x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_dt_collapse_selector.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_dt_collapse_selector
  unfold EoCases.__eo_prog_dt_collapse_selector.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fdt_2dcollapse_2dselector_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fdt_2dcollapse_2dselector s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_dt_collapse_selector x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fdt_2dcollapse_2dselector.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fdt_2dcollapse_2dselector
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fdt_2dcollapse_2dselector_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_dt_collapse_selector.case_0

theorem eo__24eo_5fprog_5fdt_2dcollapse_2dselector_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fdt_2dcollapse_2dselector.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fdt_2dcollapse_2dselector
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fdt_2dcollapse_2dselector s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_dt_collapse_selector x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fdt_2dcollapse_2dselector_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fdt_2dcollapse_2dtester_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fdt_2dcollapse_2dtester s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_dt_collapse_tester.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_dt_collapse_tester.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fdt_2dcollapse_2dtester
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_prog_dt_collapse_tester.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_prog_dt_collapse_tester.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__3d.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_prog_dt_collapse_tester.case_0
  pat_unapply h_v5 as ⟨v8, v9, x_v8, x_v9, h_v8, h_v9, hn_v8, hn_v9⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_dt_collapse_tester.case_0
  pat_destruct CtorSpec.eo_is.destruct h_v8 as ⟨v11, x_v11, h_v11⟩ else hinv1 hG in EoCases.__eo_prog_dt_collapse_tester.case_0
  obtain hn_v11 := CtorSpec.eo_is.fields_ne_stuck hinv1 h_v8
  store_step with ih.eo__24dt_5feq_5fcons s1 v11 v9 _ _ hinv1 h64 (hG.rem hrem) h_v11 h_v9 as ⟨v12, s2, hinv2, h_v12⟩ growing hG carrying h_v2 h_v9 h_v11 dropping h_v4 h_v5 h_v6 h_v8 hinv1 s1 v4 v5 v6 v8
  have h_req_v18 := (show requires_0_eo__24eo_5fprog_5fdt_2dcollapse_2dtester s2 v12 v2 v11 v9 ⦃ r s' => s'.Inv ∧ s2.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold requires_0_eo__24eo_5fprog_5fdt_2dcollapse_2dtester
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s2
    req_same v12 v2 with h_v12 h_v2 using hinv2 hG
    req_stuck h_v12 as hq_v12 using hinv2 hG
    step as ⟨e_v13, he_v13⟩
    store_step with CtorSpec.eo__3d.construct s2 e_v13 (by rw [he_v13]; exact empty_args) hinv2 h64 as ⟨v13, s3, hinv3, h_v13⟩ growing hG carrying h_v2 h_v9 h_v11 dropping h_v12 he_v13 hinv2 e_v13 s2 v12
    step as ⟨e_v14, he_v14⟩
    store_step with CtorSpec.eo_is.construct s3 e_v14 (by rw [he_v14]; rfl) h_v11 hinv3 h64 as ⟨v14, s4, hinv4, h_v14⟩ growing hG carrying h_v2 h_v9 h_v13 dropping h_v11 he_v14 hinv3 e_v14 s3 v11
    store_step with Store.apply_rep s4 v14 v9 _ _ hinv4 h64 h_v14 h_v9 (by ns_tac) (by ns_tac) as ⟨v15, s5, hinv5, h_v15⟩ growing hG carrying h_v2 h_v13 dropping h_v14 h_v9 hinv4 s4 v14 v9
    store_step with Store.apply_rep s5 v13 v15 _ _ hinv5 h64 h_v13 h_v15 (by ns_tac) (by ns_tac) as ⟨v16, s6, hinv6, h_v16⟩ growing hG carrying h_v2 dropping h_v13 h_v15 hinv5 s5 v13 v15
    store_step with Store.apply_rep s6 v16 v2 _ _ hinv6 h64 h_v16 h_v2 (by ns_tac) (by ns_tac) as ⟨v17, s7, hinv7, h_v17⟩ growing hG carrying dropping h_v16 h_v2 hinv6 s6 v16 v2
    req_done hinv7 hG with h_v17 using hq_v12)
  store_step with h_req_v18 as ⟨v18, s8, hinv8, h_v18⟩ growing hG carrying dropping h_req_v18 h_v11 h_v12 h_v2 h_v9 hinv2 s2 v11 v12 v2 v9
  case_done hinv8 hG with h_v18 in EoCases.__eo_prog_dt_collapse_tester.case_0 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5 hn_v8 hn_v9 hn_v11

/-- logos's `__eo_prog_dt_collapse_tester` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fdt_2dcollapse_2dtester.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_dt_collapse_tester x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_dt_collapse_tester.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_dt_collapse_tester
  unfold EoCases.__eo_prog_dt_collapse_tester.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fdt_2dcollapse_2dtester_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fdt_2dcollapse_2dtester s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_dt_collapse_tester x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fdt_2dcollapse_2dtester.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fdt_2dcollapse_2dtester
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fdt_2dcollapse_2dtester_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_dt_collapse_tester.case_0

theorem eo__24eo_5fprog_5fdt_2dcollapse_2dtester_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fdt_2dcollapse_2dtester.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fdt_2dcollapse_2dtester
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fdt_2dcollapse_2dtester s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_dt_collapse_tester x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fdt_2dcollapse_2dtester_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fdt_2dcollapse_2dtester_2dsingleton_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fdt_2dcollapse_2dtester_2dsingleton s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_dt_collapse_tester_singleton.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_dt_collapse_tester_singleton.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fdt_2dcollapse_2dtester_2dsingleton
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_prog_dt_collapse_tester_singleton.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_prog_dt_collapse_tester_singleton.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__3d.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_prog_dt_collapse_tester_singleton.case_0
  pat_unapply h_v5 as ⟨v8, v9, x_v8, x_v9, h_v8, h_v9, hn_v8, hn_v9⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_dt_collapse_tester_singleton.case_0
  pat_destruct CtorSpec.eo_is.destruct h_v8 as ⟨v11, x_v11, h_v11⟩ else hinv1 hG in EoCases.__eo_prog_dt_collapse_tester_singleton.case_0
  obtain hn_v11 := CtorSpec.eo_is.fields_ne_stuck hinv1 h_v8
  store_step with Store.literal_boolean_spec s1 true hinv1 h64 as ⟨v12, s2, hinv2, h_v12⟩ growing hG carrying h_v2 h_v9 h_v11 dropping h_v4 h_v5 h_v6 h_v8 hinv1 s1 v4 v5 v6 v8
  pat_same v2 v12 with h_v2 h_v12 using hinv2 else hinv2 hG in EoCases.__eo_prog_dt_collapse_tester_singleton.case_0
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s2 e_v13 (by rw [he_v13]; exact empty_args) hinv2 h64 as ⟨v13, s3, hinv3, h_v13⟩ growing hG carrying h_v9 h_v11 dropping h_v12 h_v2 he_v13 hinv2 e_v13 s2 v12 v2
  store_step with ih.eo__24eo_5ftypeof s3 v9 _ hinv3 h64 (hG.rem hrem) h_v9 as ⟨v14, s4, hinv4, h_v14⟩ growing hG carrying h_v9 h_v11 h_v13 dropping hinv3 s3
  store_step with ih.eo__24dt_5fget_5fconstructors s4 v14 _ hinv4 h64 (hG.rem hrem) h_v14 as ⟨v15, s5, hinv5, h_v15⟩ growing hG carrying h_v9 h_v11 h_v13 dropping h_v14 hinv4 s4 v14
  step as ⟨e_v16, he_v16⟩
  store_step with Store.builtin_spec_list_len n ih.eo__24eo_5fis_5flist_5fnil s5 e_v16 (by rw [he_v16]; rfl) h_v13 h_v15 hinv5 h64 (hG.rem hrem) (by not_left_tac) as ⟨v16, s6, hinv6, h_v16⟩ growing hG carrying h_v9 h_v11 dropping h_v13 h_v15 he_v16 hinv5 e_v16 s5 v13 v15
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s6 1#u32 (1) (by scalar_tac) hinv6 h64 as ⟨v17, s7, hinv7, h_v17⟩ growing hG carrying h_v9 h_v11 h_v16 dropping hinv6 s6
  have h_req_v24 := (show requires_0_eo__24eo_5fprog_5fdt_2dcollapse_2dtester_2dsingleton s7 v16 v17 v11 v9 ⦃ r s' => s'.Inv ∧ s7.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold requires_0_eo__24eo_5fprog_5fdt_2dcollapse_2dtester_2dsingleton
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s7
    req_same v16 v17 with h_v16 h_v17 using hinv7 hG
    req_stuck h_v16 as hq_v16 using hinv7 hG
    step as ⟨e_v18, he_v18⟩
    store_step with CtorSpec.eo__3d.construct s7 e_v18 (by rw [he_v18]; exact empty_args) hinv7 h64 as ⟨v18, s8, hinv8, h_v18⟩ growing hG carrying h_v9 h_v11 dropping h_v16 h_v17 he_v18 hinv7 e_v18 s7 v16 v17
    step as ⟨e_v19, he_v19⟩
    store_step with CtorSpec.eo_is.construct s8 e_v19 (by rw [he_v19]; rfl) h_v11 hinv8 h64 as ⟨v19, s9, hinv9, h_v19⟩ growing hG carrying h_v9 h_v18 dropping h_v11 he_v19 hinv8 e_v19 s8 v11
    store_step with Store.apply_rep s9 v19 v9 _ _ hinv9 h64 h_v19 h_v9 (by ns_tac) (by ns_tac) as ⟨v20, s10, hinv10, h_v20⟩ growing hG carrying h_v18 dropping h_v19 h_v9 hinv9 s9 v19 v9
    store_step with Store.apply_rep s10 v18 v20 _ _ hinv10 h64 h_v18 h_v20 (by ns_tac) (by ns_tac) as ⟨v21, s11, hinv11, h_v21⟩ growing hG carrying dropping h_v18 h_v20 hinv10 s10 v18 v20
    store_step with Store.literal_boolean_spec s11 true hinv11 h64 as ⟨v22, s12, hinv12, h_v22⟩ growing hG carrying h_v21 dropping hinv11 s11
    store_step with Store.apply_rep s12 v21 v22 _ _ hinv12 h64 h_v21 h_v22 (by ns_tac) (by ns_tac) as ⟨v23, s13, hinv13, h_v23⟩ growing hG carrying dropping h_v21 h_v22 hinv12 s12 v21 v22
    req_done hinv13 hG with h_v23 using hq_v16)
  store_step with h_req_v24 as ⟨v24, s14, hinv14, h_v24⟩ growing hG carrying dropping h_req_v24 h_v11 h_v16 h_v17 h_v9 hinv7 s7 v11 v16 v17 v9
  case_done hinv14 hG with h_v24 in EoCases.__eo_prog_dt_collapse_tester_singleton.case_0 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5 hn_v8 hn_v9 hn_v11

/-- logos's `__eo_prog_dt_collapse_tester_singleton` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fdt_2dcollapse_2dtester_2dsingleton.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_dt_collapse_tester_singleton x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_dt_collapse_tester_singleton.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_dt_collapse_tester_singleton
  unfold EoCases.__eo_prog_dt_collapse_tester_singleton.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fdt_2dcollapse_2dtester_2dsingleton_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fdt_2dcollapse_2dtester_2dsingleton s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_dt_collapse_tester_singleton x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fdt_2dcollapse_2dtester_2dsingleton.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fdt_2dcollapse_2dtester_2dsingleton
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fdt_2dcollapse_2dtester_2dsingleton_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_dt_collapse_tester_singleton.case_0

theorem eo__24eo_5fprog_5fdt_2dcollapse_2dtester_2dsingleton_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fdt_2dcollapse_2dtester_2dsingleton.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fdt_2dcollapse_2dtester_2dsingleton
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fdt_2dcollapse_2dtester_2dsingleton s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_dt_collapse_tester_singleton x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fdt_2dcollapse_2dtester_2dsingleton_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fdt_2dcollapse_2dupdater_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fdt_2dcollapse_2dupdater s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_dt_collapse_updater.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_dt_collapse_updater.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fdt_2dcollapse_2dupdater
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_prog_dt_collapse_updater.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_prog_dt_collapse_updater.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__3d.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_prog_dt_collapse_updater.case_0
  store_step with ih.eo__24mk_5fdt_5fcollapse_5fupdater_5frhs s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 h_v5 dropping h_v4 h_v6 hinv1 s1 v4 v6
  have h_req_v11 := (show requires_0_eo__24eo_5fprog_5fdt_2dcollapse_2dupdater s2 v7 v2 v5 ⦃ r s' => s'.Inv ∧ s2.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold requires_0_eo__24eo_5fprog_5fdt_2dcollapse_2dupdater
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s2
    req_same v7 v2 with h_v7 h_v2 using hinv2 hG
    req_stuck h_v7 as hq_v7 using hinv2 hG
    step as ⟨e_v8, he_v8⟩
    store_step with CtorSpec.eo__3d.construct s2 e_v8 (by rw [he_v8]; exact empty_args) hinv2 h64 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v2 h_v5 dropping h_v7 he_v8 hinv2 e_v8 s2 v7
    store_step with Store.apply_rep s3 v8 v5 _ _ hinv3 h64 h_v8 h_v5 (by ns_tac) (by ns_tac) as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_v2 dropping h_v5 h_v8 hinv3 s3 v5 v8
    store_step with Store.apply_rep s4 v9 v2 _ _ hinv4 h64 h_v9 h_v2 (by ns_tac) (by ns_tac) as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying dropping h_v2 h_v9 hinv4 s4 v2 v9
    req_done hinv5 hG with h_v10 using hq_v7)
  store_step with h_req_v11 as ⟨v11, s6, hinv6, h_v11⟩ growing hG carrying dropping h_req_v11 h_v2 h_v5 h_v7 hinv2 s2 v2 v5 v7
  case_done hinv6 hG with h_v11 in EoCases.__eo_prog_dt_collapse_updater.case_0 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

/-- logos's `__eo_prog_dt_collapse_updater` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fdt_2dcollapse_2dupdater.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_dt_collapse_updater x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_dt_collapse_updater.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_dt_collapse_updater
  unfold EoCases.__eo_prog_dt_collapse_updater.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fdt_2dcollapse_2dupdater_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fdt_2dcollapse_2dupdater s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_dt_collapse_updater x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fdt_2dcollapse_2dupdater.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fdt_2dcollapse_2dupdater
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fdt_2dcollapse_2dupdater_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_dt_collapse_updater.case_0

theorem eo__24eo_5fprog_5fdt_2dcollapse_2dupdater_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fdt_2dcollapse_2dupdater.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fdt_2dcollapse_2dupdater
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fdt_2dcollapse_2dupdater s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_dt_collapse_updater x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fdt_2dcollapse_2dupdater_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fdt_2dcons_2deq_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fdt_2dcons_2deq s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_dt_cons_eq.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_dt_cons_eq.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fdt_2dcons_2deq
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_prog_dt_cons_eq.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_prog_dt_cons_eq.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__3d.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_prog_dt_cons_eq.case_0
  pat_unapply h_v5 as ⟨v8, v9, x_v8, x_v9, h_v8, h_v9, hn_v8, hn_v9⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_dt_cons_eq.case_0
  pat_unapply h_v8 as ⟨v11, v12, x_v11, x_v12, h_v11, h_v12, hn_v11, hn_v12⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_dt_cons_eq.case_0
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo__3d.construct s1 e_v13 (by rw [he_v13]; exact empty_args) hinv1 h64 as ⟨v13, s2, hinv2, h_v13⟩ growing hG carrying h_v2 h_v9 h_v11 h_v12 dropping h_v4 h_v5 h_v6 h_v8 he_v13 hinv1 e_v13 s1 v4 v5 v6 v8
  pat_same v11 v13 with h_v11 h_v13 using hinv2 else hinv2 hG in EoCases.__eo_prog_dt_cons_eq.case_0
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo_and.construct s2 e_v14 (by rw [he_v14]; exact empty_args) hinv2 h64 as ⟨v14, s3, hinv3, h_v14⟩ growing hG carrying h_v2 h_v9 h_v12 dropping h_v11 h_v13 he_v14 hinv2 e_v14 s2 v11 v13
  store_step with ih.eo__24mk_5fdt_5fcons_5feq s3 v12 v9 _ _ hinv3 h64 (hG.rem hrem) h_v12 h_v9 as ⟨v15, s4, hinv4, h_v15⟩ growing hG carrying h_v2 h_v9 h_v12 h_v14 dropping hinv3 s3
  step as ⟨e_v16, he_v16⟩
  store_step with Store.builtin_spec_list_singleton_elim n ih.eo__24eo_5fis_5flist_5fnil s4 e_v16 (by rw [he_v16]; rfl) h_v14 h_v15 hinv4 h64 (hG.rem hrem) op_not_left_eo_and op_nil_apply_eo_and as ⟨v16, s5, hinv5, h_v16⟩ growing hG carrying h_v2 h_v9 h_v12 dropping h_v14 h_v15 he_v16 hinv4 e_v16 s4 v14 v15
  have h_req_v23 := (show requires_0_eo__24eo_5fprog_5fdt_2dcons_2deq s5 v16 v2 v12 v9 ⦃ r s' => s'.Inv ∧ s5.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold requires_0_eo__24eo_5fprog_5fdt_2dcons_2deq
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s5
    req_same v16 v2 with h_v16 h_v2 using hinv5 hG
    req_stuck h_v16 as hq_v16 using hinv5 hG
    step as ⟨e_v17, he_v17⟩
    store_step with CtorSpec.eo__3d.construct s5 e_v17 (by rw [he_v17]; exact empty_args) hinv5 h64 as ⟨v17, s6, hinv6, h_v17⟩ growing hG carrying h_v2 h_v9 h_v12 dropping h_v16 he_v17 hinv5 e_v17 s5 v16
    step as ⟨e_v18, he_v18⟩
    store_step with CtorSpec.eo__3d.construct s6 e_v18 (by rw [he_v18]; exact empty_args) hinv6 h64 as ⟨v18, s7, hinv7, h_v18⟩ growing hG carrying h_v2 h_v9 h_v12 h_v17 dropping he_v18 hinv6 e_v18 s6
    store_step with Store.apply_rep s7 v18 v12 _ _ hinv7 h64 h_v18 h_v12 (by ns_tac) (by ns_tac) as ⟨v19, s8, hinv8, h_v19⟩ growing hG carrying h_v2 h_v9 h_v17 dropping h_v12 h_v18 hinv7 s7 v12 v18
    store_step with Store.apply_rep s8 v19 v9 _ _ hinv8 h64 h_v19 h_v9 (by ns_tac) (by ns_tac) as ⟨v20, s9, hinv9, h_v20⟩ growing hG carrying h_v2 h_v17 dropping h_v19 h_v9 hinv8 s8 v19 v9
    store_step with Store.apply_rep s9 v17 v20 _ _ hinv9 h64 h_v17 h_v20 (by ns_tac) (by ns_tac) as ⟨v21, s10, hinv10, h_v21⟩ growing hG carrying h_v2 dropping h_v17 h_v20 hinv9 s9 v17 v20
    store_step with Store.apply_rep s10 v21 v2 _ _ hinv10 h64 h_v21 h_v2 (by ns_tac) (by ns_tac) as ⟨v22, s11, hinv11, h_v22⟩ growing hG carrying dropping h_v2 h_v21 hinv10 s10 v2 v21
    req_done hinv11 hG with h_v22 using hq_v16)
  store_step with h_req_v23 as ⟨v23, s12, hinv12, h_v23⟩ growing hG carrying dropping h_req_v23 h_v12 h_v16 h_v2 h_v9 hinv5 s5 v12 v16 v2 v9
  case_done hinv12 hG with h_v23 in EoCases.__eo_prog_dt_cons_eq.case_0 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5 hn_v8 hn_v9 hn_v11 hn_v12

/-- logos's `__eo_prog_dt_cons_eq` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fdt_2dcons_2deq.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_dt_cons_eq x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_dt_cons_eq.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_dt_cons_eq
  unfold EoCases.__eo_prog_dt_cons_eq.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fdt_2dcons_2deq_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fdt_2dcons_2deq s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_dt_cons_eq x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fdt_2dcons_2deq.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fdt_2dcons_2deq
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fdt_2dcons_2deq_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_dt_cons_eq.case_0

theorem eo__24eo_5fprog_5fdt_2dcons_2deq_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fdt_2dcons_2deq.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fdt_2dcons_2deq
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fdt_2dcons_2deq s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_dt_cons_eq x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fdt_2dcons_2deq_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fdt_2dcons_2deq_2dclash_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fdt_2dcons_2deq_2dclash s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_dt_cons_eq_clash.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_dt_cons_eq_clash.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fdt_2dcons_2deq_2dclash
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_prog_dt_cons_eq_clash.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_prog_dt_cons_eq_clash.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__3d.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_prog_dt_cons_eq_clash.case_0
  pat_unapply h_v5 as ⟨v8, v9, x_v8, x_v9, h_v8, h_v9, hn_v8, hn_v9⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_dt_cons_eq_clash.case_0
  pat_unapply h_v8 as ⟨v11, v12, x_v11, x_v12, h_v11, h_v12, hn_v11, hn_v12⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_dt_cons_eq_clash.case_0
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo__3d.construct s1 e_v13 (by rw [he_v13]; exact empty_args) hinv1 h64 as ⟨v13, s2, hinv2, h_v13⟩ growing hG carrying h_v2 h_v9 h_v11 h_v12 dropping h_v4 h_v5 h_v6 h_v8 he_v13 hinv1 e_v13 s1 v4 v5 v6 v8
  pat_same v11 v13 with h_v11 h_v13 using hinv2 else hinv2 hG in EoCases.__eo_prog_dt_cons_eq_clash.case_0
  store_step with Store.literal_boolean_spec s2 false hinv2 h64 as ⟨v14, s3, hinv3, h_v14⟩ growing hG carrying h_v2 h_v9 h_v12 dropping h_v11 h_v13 hinv2 s2 v11 v13
  pat_same v2 v14 with h_v2 h_v14 using hinv3 else hinv3 hG in EoCases.__eo_prog_dt_cons_eq_clash.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with Store.builtin_spec_eq s3 e_v15 (by rw [he_v15]; rfl) h_v12 h_v9 hinv3 h64 as ⟨v15, s4, hinv4, h_v15⟩ growing hG carrying h_v9 h_v12 dropping h_v14 h_v2 he_v15 hinv3 e_v15 s3 v14 v2
  have h_ite_v19 := (show if_0_eo__24eo_5fprog_5fdt_2dcons_2deq_2dclash s4 v15 v12 v9 ⦃ r s' => s'.Inv ∧ s4.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_0_eo__24eo_5fprog_5fdt_2dcons_2deq_2dclash
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s4
    rcases Store.boolean_value_term h_v15 with ⟨hx_16, hbv_16⟩ | ⟨hx_16, hbv_16⟩ | ⟨hx_16, hbv_16⟩
    · ite_branch hbv_16
      store_step with Store.literal_boolean_spec s4 false hinv4 h64 as ⟨v16, s5, hinv5, h_v16⟩ growing hG carrying h_v9 h_v12 dropping h_v15 v15
      ite_done hinv5 hG with (eo_ite_true_rep _ hx_16 h_v16)
    · ite_branch hbv_16
      store_step with ih.eo__24eo_5ftypeof s4 v12 _ hinv4 h64 (hG.rem hrem) h_v12 as ⟨v17, s5, hinv5, h_v17⟩ growing hG carrying h_v9 h_v12 dropping h_v15 v15
      store_step with ih.eo__24are_5fdistinct_5fterms_5ftype s5 v12 v9 v17 _ _ _ hinv5 h64 (hG.rem hrem) h_v12 h_v9 h_v17 as ⟨v18, s6, hinv6, h_v18⟩ growing hG carrying h_v9 h_v12 dropping h_v17 v17
      ite_done hinv6 hG with (eo_ite_false_rep _ hx_16 h_v18)
    · ite_branch hbv_16
      ite_stuck hinv4 hG with hx_16)
  store_step with h_ite_v19 as ⟨v19, s5, hinv5, h_v19⟩ growing hG carrying h_v9 h_v12 dropping h_ite_v19 h_v15 hinv4 s4 v15
  store_step with Store.literal_boolean_spec s5 true hinv5 h64 as ⟨v20, s6, hinv6, h_v20⟩ growing hG carrying h_v9 h_v12 h_v19 dropping hinv5 s5
  have h_req_v28 := (show requires_1_eo__24eo_5fprog_5fdt_2dcons_2deq_2dclash s6 v19 v20 v12 v9 ⦃ r s' => s'.Inv ∧ s6.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold requires_1_eo__24eo_5fprog_5fdt_2dcons_2deq_2dclash
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s6
    req_same v19 v20 with h_v19 h_v20 using hinv6 hG
    req_stuck h_v19 as hq_v19 using hinv6 hG
    step as ⟨e_v21, he_v21⟩
    store_step with CtorSpec.eo__3d.construct s6 e_v21 (by rw [he_v21]; exact empty_args) hinv6 h64 as ⟨v21, s7, hinv7, h_v21⟩ growing hG carrying h_v9 h_v12 dropping h_v19 h_v20 he_v21 hinv6 e_v21 s6 v19 v20
    step as ⟨e_v22, he_v22⟩
    store_step with CtorSpec.eo__3d.construct s7 e_v22 (by rw [he_v22]; exact empty_args) hinv7 h64 as ⟨v22, s8, hinv8, h_v22⟩ growing hG carrying h_v9 h_v12 h_v21 dropping he_v22 hinv7 e_v22 s7
    store_step with Store.apply_rep s8 v22 v12 _ _ hinv8 h64 h_v22 h_v12 (by ns_tac) (by ns_tac) as ⟨v23, s9, hinv9, h_v23⟩ growing hG carrying h_v9 h_v21 dropping h_v12 h_v22 hinv8 s8 v12 v22
    store_step with Store.apply_rep s9 v23 v9 _ _ hinv9 h64 h_v23 h_v9 (by ns_tac) (by ns_tac) as ⟨v24, s10, hinv10, h_v24⟩ growing hG carrying h_v21 dropping h_v23 h_v9 hinv9 s9 v23 v9
    store_step with Store.apply_rep s10 v21 v24 _ _ hinv10 h64 h_v21 h_v24 (by ns_tac) (by ns_tac) as ⟨v25, s11, hinv11, h_v25⟩ growing hG carrying dropping h_v21 h_v24 hinv10 s10 v21 v24
    store_step with Store.literal_boolean_spec s11 false hinv11 h64 as ⟨v26, s12, hinv12, h_v26⟩ growing hG carrying h_v25 dropping hinv11 s11
    store_step with Store.apply_rep s12 v25 v26 _ _ hinv12 h64 h_v25 h_v26 (by ns_tac) (by ns_tac) as ⟨v27, s13, hinv13, h_v27⟩ growing hG carrying dropping h_v25 h_v26 hinv12 s12 v25 v26
    req_done hinv13 hG with h_v27 using hq_v19)
  store_step with h_req_v28 as ⟨v28, s14, hinv14, h_v28⟩ growing hG carrying dropping h_req_v28 h_v12 h_v19 h_v20 h_v9 hinv6 s6 v12 v19 v20 v9
  case_done hinv14 hG with h_v28 in EoCases.__eo_prog_dt_cons_eq_clash.case_0 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5 hn_v8 hn_v9 hn_v11 hn_v12

/-- logos's `__eo_prog_dt_cons_eq_clash` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fdt_2dcons_2deq_2dclash.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_dt_cons_eq_clash x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_dt_cons_eq_clash.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_dt_cons_eq_clash
  unfold EoCases.__eo_prog_dt_cons_eq_clash.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fdt_2dcons_2deq_2dclash_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fdt_2dcons_2deq_2dclash s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_dt_cons_eq_clash x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fdt_2dcons_2deq_2dclash.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fdt_2dcons_2deq_2dclash
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fdt_2dcons_2deq_2dclash_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_dt_cons_eq_clash.case_0

theorem eo__24eo_5fprog_5fdt_2dcons_2deq_2dclash_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fdt_2dcons_2deq_2dclash.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fdt_2dcons_2deq_2dclash
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fdt_2dcons_2deq_2dclash s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_dt_cons_eq_clash x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fdt_2dcons_2deq_2dclash_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fdt_2dcycle_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fdt_2dcycle s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_dt_cycle.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_dt_cycle.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fdt_2dcycle
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_prog_dt_cycle.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_prog_dt_cycle.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__3d.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_prog_dt_cycle.case_0
  pat_unapply h_v5 as ⟨v8, v9, x_v8, x_v9, h_v8, h_v9, hn_v8, hn_v9⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_dt_cycle.case_0
  pat_unapply h_v8 as ⟨v11, v12, x_v11, x_v12, h_v11, h_v12, hn_v11, hn_v12⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_dt_cycle.case_0
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo__3d.construct s1 e_v13 (by rw [he_v13]; exact empty_args) hinv1 h64 as ⟨v13, s2, hinv2, h_v13⟩ growing hG carrying h_v2 h_v9 h_v11 h_v12 dropping h_v4 h_v5 h_v6 h_v8 he_v13 hinv1 e_v13 s1 v4 v5 v6 v8
  pat_same v11 v13 with h_v11 h_v13 using hinv2 else hinv2 hG in EoCases.__eo_prog_dt_cycle.case_0
  store_step with Store.literal_boolean_spec s2 false hinv2 h64 as ⟨v14, s3, hinv3, h_v14⟩ growing hG carrying h_v2 h_v9 h_v12 dropping h_v11 h_v13 hinv2 s2 v11 v13
  pat_same v2 v14 with h_v2 h_v14 using hinv3 else hinv3 hG in EoCases.__eo_prog_dt_cycle.case_0
  store_step with ih.eo__24is_5fcons_5fapp s3 v9 _ hinv3 h64 (hG.rem hrem) h_v9 as ⟨v15, s4, hinv4, h_v15⟩ growing hG carrying h_v9 h_v12 dropping h_v14 h_v2 hinv3 s3 v14 v2
  store_step with Store.literal_boolean_spec s4 false hinv4 h64 as ⟨v16, s5, hinv5, h_v16⟩ growing hG carrying h_v9 h_v12 h_v15 dropping hinv4 s4
  store_step with ih.eo__24dt_5ffind_5fcycle s5 v9 v12 v15 v16 _ _ _ _ hinv5 h64 (hG.rem hrem) h_v9 h_v12 h_v15 h_v16 as ⟨v17, s6, hinv6, h_v17⟩ growing hG carrying h_v9 h_v12 dropping h_v15 h_v16 hinv5 s5 v15 v16
  store_step with Store.literal_boolean_spec s6 true hinv6 h64 as ⟨v18, s7, hinv7, h_v18⟩ growing hG carrying h_v9 h_v12 h_v17 dropping hinv6 s6
  have h_req_v26 := (show requires_0_eo__24eo_5fprog_5fdt_2dcycle s7 v17 v18 v12 v9 ⦃ r s' => s'.Inv ∧ s7.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold requires_0_eo__24eo_5fprog_5fdt_2dcycle
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s7
    req_same v17 v18 with h_v17 h_v18 using hinv7 hG
    req_stuck h_v17 as hq_v17 using hinv7 hG
    step as ⟨e_v19, he_v19⟩
    store_step with CtorSpec.eo__3d.construct s7 e_v19 (by rw [he_v19]; exact empty_args) hinv7 h64 as ⟨v19, s8, hinv8, h_v19⟩ growing hG carrying h_v9 h_v12 dropping h_v17 h_v18 he_v19 hinv7 e_v19 s7 v17 v18
    step as ⟨e_v20, he_v20⟩
    store_step with CtorSpec.eo__3d.construct s8 e_v20 (by rw [he_v20]; exact empty_args) hinv8 h64 as ⟨v20, s9, hinv9, h_v20⟩ growing hG carrying h_v9 h_v12 h_v19 dropping he_v20 hinv8 e_v20 s8
    store_step with Store.apply_rep s9 v20 v12 _ _ hinv9 h64 h_v20 h_v12 (by ns_tac) (by ns_tac) as ⟨v21, s10, hinv10, h_v21⟩ growing hG carrying h_v9 h_v19 dropping h_v12 h_v20 hinv9 s9 v12 v20
    store_step with Store.apply_rep s10 v21 v9 _ _ hinv10 h64 h_v21 h_v9 (by ns_tac) (by ns_tac) as ⟨v22, s11, hinv11, h_v22⟩ growing hG carrying h_v19 dropping h_v21 h_v9 hinv10 s10 v21 v9
    store_step with Store.apply_rep s11 v19 v22 _ _ hinv11 h64 h_v19 h_v22 (by ns_tac) (by ns_tac) as ⟨v23, s12, hinv12, h_v23⟩ growing hG carrying dropping h_v19 h_v22 hinv11 s11 v19 v22
    store_step with Store.literal_boolean_spec s12 false hinv12 h64 as ⟨v24, s13, hinv13, h_v24⟩ growing hG carrying h_v23 dropping hinv12 s12
    store_step with Store.apply_rep s13 v23 v24 _ _ hinv13 h64 h_v23 h_v24 (by ns_tac) (by ns_tac) as ⟨v25, s14, hinv14, h_v25⟩ growing hG carrying dropping h_v23 h_v24 hinv13 s13 v23 v24
    req_done hinv14 hG with h_v25 using hq_v17)
  store_step with h_req_v26 as ⟨v26, s15, hinv15, h_v26⟩ growing hG carrying dropping h_req_v26 h_v12 h_v17 h_v18 h_v9 hinv7 s7 v12 v17 v18 v9
  case_done hinv15 hG with h_v26 in EoCases.__eo_prog_dt_cycle.case_0 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5 hn_v8 hn_v9 hn_v11 hn_v12

/-- logos's `__eo_prog_dt_cycle` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fdt_2dcycle.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_dt_cycle x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_dt_cycle.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_dt_cycle
  unfold EoCases.__eo_prog_dt_cycle.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fdt_2dcycle_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fdt_2dcycle s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_dt_cycle x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fdt_2dcycle.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fdt_2dcycle
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fdt_2dcycle_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_dt_cycle.case_0

theorem eo__24eo_5fprog_5fdt_2dcycle_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fdt_2dcycle.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fdt_2dcycle
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fdt_2dcycle s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_dt_cycle x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fdt_2dcycle_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fdt_2dinst_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fdt_2dinst s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_dt_inst.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_dt_inst.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fdt_2dinst
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_prog_dt_inst.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_prog_dt_inst.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__3d.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_prog_dt_inst.case_0
  pat_unapply h_v2 as ⟨v8, v9, x_v8, x_v9, h_v8, h_v9, hn_v8, hn_v9⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_dt_inst.case_0
  pat_unapply h_v8 as ⟨v11, v12, x_v11, x_v12, h_v11, h_v12, hn_v11, hn_v12⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_dt_inst.case_0
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo__3d.construct s1 e_v13 (by rw [he_v13]; exact empty_args) hinv1 h64 as ⟨v13, s2, hinv2, h_v13⟩ growing hG carrying h_v5 h_v9 h_v11 h_v12 dropping h_v2 h_v4 h_v6 h_v8 he_v13 hinv1 e_v13 s1 v2 v4 v6 v8
  pat_same v11 v13 with h_v11 h_v13 using hinv2 else hinv2 hG in EoCases.__eo_prog_dt_inst.case_0
  store_step with ih.eo__24mk_5fdt_5finst_5fprem s2 v5 v12 _ _ hinv2 h64 (hG.rem hrem) h_v5 h_v12 as ⟨v14, s3, hinv3, h_v14⟩ growing hG carrying h_v5 h_v9 h_v12 dropping h_v11 h_v13 hinv2 s2 v11 v13
  have h_req_v21 := (show requires_0_eo__24eo_5fprog_5fdt_2dinst s3 v14 v9 v5 v12 ⦃ r s' => s'.Inv ∧ s3.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold requires_0_eo__24eo_5fprog_5fdt_2dinst
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s3
    req_same v14 v9 with h_v14 h_v9 using hinv3 hG
    req_stuck h_v14 as hq_v14 using hinv3 hG
    step as ⟨e_v15, he_v15⟩
    store_step with CtorSpec.eo__3d.construct s3 e_v15 (by rw [he_v15]; exact empty_args) hinv3 h64 as ⟨v15, s4, hinv4, h_v15⟩ growing hG carrying h_v5 h_v9 h_v12 dropping h_v14 he_v15 hinv3 e_v15 s3 v14
    store_step with Store.apply_rep s4 v15 v5 _ _ hinv4 h64 h_v15 h_v5 (by ns_tac) (by ns_tac) as ⟨v16, s5, hinv5, h_v16⟩ growing hG carrying h_v9 h_v12 dropping h_v15 h_v5 hinv4 s4 v15 v5
    step as ⟨e_v17, he_v17⟩
    store_step with CtorSpec.eo__3d.construct s5 e_v17 (by rw [he_v17]; exact empty_args) hinv5 h64 as ⟨v17, s6, hinv6, h_v17⟩ growing hG carrying h_v9 h_v12 h_v16 dropping he_v17 hinv5 e_v17 s5
    store_step with Store.apply_rep s6 v17 v12 _ _ hinv6 h64 h_v17 h_v12 (by ns_tac) (by ns_tac) as ⟨v18, s7, hinv7, h_v18⟩ growing hG carrying h_v9 h_v16 dropping h_v12 h_v17 hinv6 s6 v12 v17
    store_step with Store.apply_rep s7 v18 v9 _ _ hinv7 h64 h_v18 h_v9 (by ns_tac) (by ns_tac) as ⟨v19, s8, hinv8, h_v19⟩ growing hG carrying h_v16 dropping h_v18 h_v9 hinv7 s7 v18 v9
    store_step with Store.apply_rep s8 v16 v19 _ _ hinv8 h64 h_v16 h_v19 (by ns_tac) (by ns_tac) as ⟨v20, s9, hinv9, h_v20⟩ growing hG carrying dropping h_v16 h_v19 hinv8 s8 v16 v19
    req_done hinv9 hG with h_v20 using hq_v14)
  store_step with h_req_v21 as ⟨v21, s10, hinv10, h_v21⟩ growing hG carrying dropping h_req_v21 h_v12 h_v14 h_v5 h_v9 hinv3 s3 v12 v14 v5 v9
  case_done hinv10 hG with h_v21 in EoCases.__eo_prog_dt_inst.case_0 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5 hn_v8 hn_v9 hn_v11 hn_v12

/-- logos's `__eo_prog_dt_inst` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fdt_2dinst.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_dt_inst x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_dt_inst.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_dt_inst
  unfold EoCases.__eo_prog_dt_inst.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fdt_2dinst_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fdt_2dinst s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_dt_inst x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fdt_2dinst.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fdt_2dinst
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fdt_2dinst_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_dt_inst.case_0

theorem eo__24eo_5fprog_5fdt_2dinst_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fdt_2dinst.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fdt_2dinst
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fdt_2dinst s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_dt_inst x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fdt_2dinst_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fdt_2dupdater_2delim_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fdt_2dupdater_2delim s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_dt_updater_elim.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_dt_updater_elim.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fdt_2dupdater_2delim
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_prog_dt_updater_elim.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_prog_dt_updater_elim.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__3d.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_prog_dt_updater_elim.case_0
  pat_unapply h_v5 as ⟨v8, v9, x_v8, x_v9, h_v8, h_v9, hn_v8, hn_v9⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_dt_updater_elim.case_0
  pat_unapply h_v8 as ⟨v11, v12, x_v11, x_v12, h_v11, h_v12, hn_v11, hn_v12⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_dt_updater_elim.case_0
  store_step with Store.apply_rep s1 v11 v12 _ _ hinv1 h64 h_v11 h_v12 (by ns_tac) (by ns_tac) as ⟨v13, s2, hinv2, h_v13⟩ growing hG carrying h_v2 h_v9 h_v11 h_v12 dropping h_v4 h_v5 h_v6 h_v8 hinv1 s1 v4 v5 v6 v8
  store_step with Store.apply_rep s2 v13 v9 _ _ hinv2 h64 h_v13 h_v9 (by ns_tac) (by ns_tac) as ⟨v14, s3, hinv3, h_v14⟩ growing hG carrying h_v2 h_v9 h_v11 h_v12 dropping h_v13 hinv2 s2 v13
  store_step with ih.eo__24mk_5fdt_5fupdater_5felim_5fconc s3 v14 v2 _ _ hinv3 h64 (hG.rem hrem) h_v14 h_v2 as ⟨v15, s4, hinv4, h_v15⟩ growing hG carrying h_v2 h_v9 h_v11 h_v12 dropping h_v14 hinv3 s3 v14
  store_step with Store.literal_boolean_spec s4 true hinv4 h64 as ⟨v16, s5, hinv5, h_v16⟩ growing hG carrying h_v2 h_v9 h_v11 h_v12 h_v15 dropping hinv4 s4
  have h_req_v22 := (show requires_0_eo__24eo_5fprog_5fdt_2dupdater_2delim s5 v15 v16 v11 v12 v9 v2 ⦃ r s' => s'.Inv ∧ s5.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold requires_0_eo__24eo_5fprog_5fdt_2dupdater_2delim
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s5
    req_same v15 v16 with h_v15 h_v16 using hinv5 hG
    req_stuck h_v15 as hq_v15 using hinv5 hG
    step as ⟨e_v17, he_v17⟩
    store_step with CtorSpec.eo__3d.construct s5 e_v17 (by rw [he_v17]; exact empty_args) hinv5 h64 as ⟨v17, s6, hinv6, h_v17⟩ growing hG carrying h_v2 h_v9 h_v11 h_v12 dropping h_v15 h_v16 he_v17 hinv5 e_v17 s5 v15 v16
    store_step with Store.apply_rep s6 v11 v12 _ _ hinv6 h64 h_v11 h_v12 (by ns_tac) (by ns_tac) as ⟨v18, s7, hinv7, h_v18⟩ growing hG carrying h_v2 h_v9 h_v17 dropping h_v11 h_v12 hinv6 s6 v11 v12
    store_step with Store.apply_rep s7 v18 v9 _ _ hinv7 h64 h_v18 h_v9 (by ns_tac) (by ns_tac) as ⟨v19, s8, hinv8, h_v19⟩ growing hG carrying h_v2 h_v17 dropping h_v18 h_v9 hinv7 s7 v18 v9
    store_step with Store.apply_rep s8 v17 v19 _ _ hinv8 h64 h_v17 h_v19 (by ns_tac) (by ns_tac) as ⟨v20, s9, hinv9, h_v20⟩ growing hG carrying h_v2 dropping h_v17 h_v19 hinv8 s8 v17 v19
    store_step with Store.apply_rep s9 v20 v2 _ _ hinv9 h64 h_v20 h_v2 (by ns_tac) (by ns_tac) as ⟨v21, s10, hinv10, h_v21⟩ growing hG carrying dropping h_v2 h_v20 hinv9 s9 v2 v20
    req_done hinv10 hG with h_v21 using hq_v15)
  store_step with h_req_v22 as ⟨v22, s11, hinv11, h_v22⟩ growing hG carrying dropping h_req_v22 h_v11 h_v12 h_v15 h_v16 h_v2 h_v9 hinv5 s5 v11 v12 v15 v16 v2 v9
  case_done hinv11 hG with h_v22 in EoCases.__eo_prog_dt_updater_elim.case_0 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5 hn_v8 hn_v9 hn_v11 hn_v12

/-- logos's `__eo_prog_dt_updater_elim` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fdt_2dupdater_2delim.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_dt_updater_elim x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_dt_updater_elim.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_dt_updater_elim
  unfold EoCases.__eo_prog_dt_updater_elim.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fdt_2dupdater_2delim_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fdt_2dupdater_2delim s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_dt_updater_elim x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fdt_2dupdater_2delim.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fdt_2dupdater_2delim
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fdt_2dupdater_2delim_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_dt_updater_elim.case_0

theorem eo__24eo_5fprog_5fdt_2dupdater_2delim_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fdt_2dupdater_2delim.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fdt_2dupdater_2delim
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fdt_2dupdater_2delim s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_dt_updater_elim x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fdt_2dupdater_2delim_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fdt_5fsplit_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fdt_5fsplit s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_dt_split.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_dt_split.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fdt_5fsplit
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_or.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 dropping he_v0 e_v0
  store_step with ih.eo__24eo_5ftypeof s1 a0 _ hinv1 h64 (hG.rem hrem) h_a0 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0 dropping hinv1 s1
  store_step with ih.eo__24dt_5fget_5fconstructors s2 v1 _ hinv2 h64 (hG.rem hrem) h_v1 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_v0 dropping h_v1 hinv2 s2 v1
  store_step with ih.eo__24mk_5fdt_5fsplit s3 v2 a0 _ _ hinv3 h64 (hG.rem hrem) h_v2 h_a0 as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_v0 dropping h_a0 h_v2 hinv3 s3 v2
  step as ⟨e_v4, he_v4⟩
  store_step with Store.builtin_spec_list_singleton_elim n ih.eo__24eo_5fis_5flist_5fnil s4 e_v4 (by rw [he_v4]; rfl) h_v0 h_v3 hinv4 h64 (hG.rem hrem) op_not_left_eo_or op_nil_apply_eo_or as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying dropping h_v0 h_v3 he_v4 hinv4 e_v4 s4 v0 v3
  case_done hinv5 hG with h_v4 in EoCases.__eo_prog_dt_split.case_0 using hn_a0

/-- logos's `__eo_prog_dt_split` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fdt_5fsplit.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_dt_split x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_dt_split.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_dt_split
  unfold EoCases.__eo_prog_dt_split.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fdt_5fsplit_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fdt_5fsplit s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_dt_split x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fdt_5fsplit.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fdt_5fsplit
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fdt_5fsplit_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_dt_split.case_0

theorem eo__24eo_5fprog_5fdt_5fsplit_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fdt_5fsplit.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fdt_5fsplit
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fdt_5fsplit s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_dt_split x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fdt_5fsplit_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5feq_2dcond_2ddeq_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5feq_2dcond_2ddeq s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_eq_cond_deq.case_0 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_eq_cond_deq.case_0 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5feq_2dcond_2ddeq
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a3 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_eq_cond_deq.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_eq_cond_deq.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_eq_cond_deq.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_v4 h_v6 h_v7 dropping h_a3 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_eq_cond_deq.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_eq_cond_deq.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_eq_cond_deq.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__3d.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_v4 h_v11 h_v13 h_v14 dropping h_v10 h_v6 h_v7 h_v8 he_v15 hinv1 e_v15 s1 v10 v6 v7 v8
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_eq_cond_deq.case_0
  pat_same v14 a1 with h_v14 h_a1 using hinv2 else hinv2 hG in EoCases.__eo_prog_eq_cond_deq.case_0
  pat_same v11 a2 with h_v11 h_a2 using hinv2 else hinv2 hG in EoCases.__eo_prog_eq_cond_deq.case_0
  store_step with Store.literal_boolean_spec s2 false hinv2 h64 as ⟨v16, s3, hinv3, h_v16⟩ growing hG carrying h_a0 h_a1 h_a2 h_v4 dropping h_v11 h_v13 h_v14 h_v15 hinv2 s2 v11 v13 v14 v15
  pat_same v4 v16 with h_v4 h_v16 using hinv3 else hinv3 hG in EoCases.__eo_prog_eq_cond_deq.case_0
  step as ⟨e_v17, he_v17⟩
  store_step with CtorSpec.eo__3d.construct s3 e_v17 (by rw [he_v17]; exact empty_args) hinv3 h64 as ⟨v17, s4, hinv4, h_v17⟩ growing hG carrying h_a0 h_a1 h_a2 dropping h_v16 h_v4 he_v17 hinv3 e_v17 s3 v16 v4
  step as ⟨e_v18, he_v18⟩
  store_step with CtorSpec.eo__3d.construct s4 e_v18 (by rw [he_v18]; exact empty_args) hinv4 h64 as ⟨v18, s5, hinv5, h_v18⟩ growing hG carrying h_a0 h_a1 h_a2 h_v17 dropping he_v18 hinv4 e_v18 s4
  step as ⟨e_v19, he_v19⟩
  store_step with CtorSpec.eo__3d.construct s5 e_v19 (by rw [he_v19]; exact empty_args) hinv5 h64 as ⟨v19, s6, hinv6, h_v19⟩ growing hG carrying h_a0 h_a1 h_a2 h_v17 h_v18 dropping he_v19 hinv5 e_v19 s5
  store_step with Store.apply_rep s6 v19 a0 _ _ hinv6 h64 h_v19 h_a0 (by ns_tac) (by ns_tac) as ⟨v20, s7, hinv7, h_v20⟩ growing hG carrying h_a0 h_a1 h_a2 h_v17 h_v18 dropping h_v19 hinv6 s6 v19
  store_step with Store.apply_rep s7 v20 a1 _ _ hinv7 h64 h_v20 h_a1 (by ns_tac) (by ns_tac) as ⟨v21, s8, hinv8, h_v21⟩ growing hG carrying h_a0 h_a1 h_a2 h_v17 h_v18 dropping h_v20 hinv7 s7 v20
  store_step with Store.apply_rep s8 v18 v21 _ _ hinv8 h64 h_v18 h_v21 (by ns_tac) (by ns_tac) as ⟨v22, s9, hinv9, h_v22⟩ growing hG carrying h_a0 h_a1 h_a2 h_v17 dropping h_v18 h_v21 hinv8 s8 v18 v21
  step as ⟨e_v23, he_v23⟩
  store_step with CtorSpec.eo__3d.construct s9 e_v23 (by rw [he_v23]; exact empty_args) hinv9 h64 as ⟨v23, s10, hinv10, h_v23⟩ growing hG carrying h_a0 h_a1 h_a2 h_v17 h_v22 dropping he_v23 hinv9 e_v23 s9
  store_step with Store.apply_rep s10 v23 a0 _ _ hinv10 h64 h_v23 h_a0 (by ns_tac) (by ns_tac) as ⟨v24, s11, hinv11, h_v24⟩ growing hG carrying h_a0 h_a1 h_a2 h_v17 h_v22 dropping h_v23 hinv10 s10 v23
  store_step with Store.apply_rep s11 v24 a2 _ _ hinv11 h64 h_v24 h_a2 (by ns_tac) (by ns_tac) as ⟨v25, s12, hinv12, h_v25⟩ growing hG carrying h_a0 h_a1 h_a2 h_v17 h_v22 dropping h_v24 hinv11 s11 v24
  store_step with Store.apply_rep s12 v22 v25 _ _ hinv12 h64 h_v22 h_v25 (by ns_tac) (by ns_tac) as ⟨v26, s13, hinv13, h_v26⟩ growing hG carrying h_a0 h_a1 h_a2 h_v17 dropping h_v22 h_v25 hinv12 s12 v22 v25
  store_step with Store.apply_rep s13 v17 v26 _ _ hinv13 h64 h_v17 h_v26 (by ns_tac) (by ns_tac) as ⟨v27, s14, hinv14, h_v27⟩ growing hG carrying h_a0 h_a1 h_a2 dropping h_v17 h_v26 hinv13 s13 v17 v26
  step as ⟨e_v28, he_v28⟩
  store_step with CtorSpec.eo_and.construct s14 e_v28 (by rw [he_v28]; exact empty_args) hinv14 h64 as ⟨v28, s15, hinv15, h_v28⟩ growing hG carrying h_a0 h_a1 h_a2 h_v27 dropping he_v28 hinv14 e_v28 s14
  step as ⟨e_v29, he_v29⟩
  store_step with CtorSpec.eo_not.construct s15 e_v29 (by rw [he_v29]; exact empty_args) hinv15 h64 as ⟨v29, s16, hinv16, h_v29⟩ growing hG carrying h_a0 h_a1 h_a2 h_v27 h_v28 dropping he_v29 hinv15 e_v29 s15
  step as ⟨e_v30, he_v30⟩
  store_step with CtorSpec.eo__3d.construct s16 e_v30 (by rw [he_v30]; exact empty_args) hinv16 h64 as ⟨v30, s17, hinv17, h_v30⟩ growing hG carrying h_a0 h_a1 h_a2 h_v27 h_v28 h_v29 dropping he_v30 hinv16 e_v30 s16
  store_step with Store.apply_rep s17 v30 a0 _ _ hinv17 h64 h_v30 h_a0 (by ns_tac) (by ns_tac) as ⟨v31, s18, hinv18, h_v31⟩ growing hG carrying h_a0 h_a1 h_a2 h_v27 h_v28 h_v29 dropping h_v30 hinv17 s17 v30
  store_step with Store.apply_rep s18 v31 a1 _ _ hinv18 h64 h_v31 h_a1 (by ns_tac) (by ns_tac) as ⟨v32, s19, hinv19, h_v32⟩ growing hG carrying h_a0 h_a2 h_v27 h_v28 h_v29 dropping h_a1 h_v31 hinv18 s18 v31
  store_step with Store.apply_rep s19 v29 v32 _ _ hinv19 h64 h_v29 h_v32 (by ns_tac) (by ns_tac) as ⟨v33, s20, hinv20, h_v33⟩ growing hG carrying h_a0 h_a2 h_v27 h_v28 dropping h_v29 h_v32 hinv19 s19 v29 v32
  store_step with Store.apply_rep s20 v28 v33 _ _ hinv20 h64 h_v28 h_v33 (by ns_tac) (by ns_tac) as ⟨v34, s21, hinv21, h_v34⟩ growing hG carrying h_a0 h_a2 h_v27 dropping h_v28 h_v33 hinv20 s20 v28 v33
  step as ⟨e_v35, he_v35⟩
  store_step with CtorSpec.eo_and.construct s21 e_v35 (by rw [he_v35]; exact empty_args) hinv21 h64 as ⟨v35, s22, hinv22, h_v35⟩ growing hG carrying h_a0 h_a2 h_v27 h_v34 dropping he_v35 hinv21 e_v35 s21
  step as ⟨e_v36, he_v36⟩
  store_step with CtorSpec.eo_not.construct s22 e_v36 (by rw [he_v36]; exact empty_args) hinv22 h64 as ⟨v36, s23, hinv23, h_v36⟩ growing hG carrying h_a0 h_a2 h_v27 h_v34 h_v35 dropping he_v36 hinv22 e_v36 s22
  step as ⟨e_v37, he_v37⟩
  store_step with CtorSpec.eo__3d.construct s23 e_v37 (by rw [he_v37]; exact empty_args) hinv23 h64 as ⟨v37, s24, hinv24, h_v37⟩ growing hG carrying h_a0 h_a2 h_v27 h_v34 h_v35 h_v36 dropping he_v37 hinv23 e_v37 s23
  store_step with Store.apply_rep s24 v37 a0 _ _ hinv24 h64 h_v37 h_a0 (by ns_tac) (by ns_tac) as ⟨v38, s25, hinv25, h_v38⟩ growing hG carrying h_a2 h_v27 h_v34 h_v35 h_v36 dropping h_a0 h_v37 hinv24 s24 v37
  store_step with Store.apply_rep s25 v38 a2 _ _ hinv25 h64 h_v38 h_a2 (by ns_tac) (by ns_tac) as ⟨v39, s26, hinv26, h_v39⟩ growing hG carrying h_v27 h_v34 h_v35 h_v36 dropping h_a2 h_v38 hinv25 s25 v38
  store_step with Store.apply_rep s26 v36 v39 _ _ hinv26 h64 h_v36 h_v39 (by ns_tac) (by ns_tac) as ⟨v40, s27, hinv27, h_v40⟩ growing hG carrying h_v27 h_v34 h_v35 dropping h_v36 h_v39 hinv26 s26 v36 v39
  store_step with Store.apply_rep s27 v35 v40 _ _ hinv27 h64 h_v35 h_v40 (by ns_tac) (by ns_tac) as ⟨v41, s28, hinv28, h_v41⟩ growing hG carrying h_v27 h_v34 dropping h_v35 h_v40 hinv27 s27 v35 v40
  store_step with Store.literal_boolean_spec s28 true hinv28 h64 as ⟨v42, s29, hinv29, h_v42⟩ growing hG carrying h_v27 h_v34 h_v41 dropping hinv28 s28
  store_step with Store.apply_rep s29 v41 v42 _ _ hinv29 h64 h_v41 h_v42 (by ns_tac) (by ns_tac) as ⟨v43, s30, hinv30, h_v43⟩ growing hG carrying h_v27 h_v34 dropping h_v41 h_v42 hinv29 s29 v41 v42
  store_step with Store.apply_rep s30 v34 v43 _ _ hinv30 h64 h_v34 h_v43 (by ns_tac) (by ns_tac) as ⟨v44, s31, hinv31, h_v44⟩ growing hG carrying h_v27 dropping h_v34 h_v43 hinv30 s30 v34 v43
  store_step with Store.apply_rep s31 v27 v44 _ _ hinv31 h64 h_v27 h_v44 (by ns_tac) (by ns_tac) as ⟨v45, s32, hinv32, h_v45⟩ growing hG carrying dropping h_v27 h_v44 hinv31 s31 v27 v44
  case_done hinv32 hG with h_v45 in EoCases.__eo_prog_eq_cond_deq.case_0 using hn_a0 hn_a1 hn_a2 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v13 hn_v14

/-- logos's `__eo_prog_eq_cond_deq` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5feq_2dcond_2ddeq.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) :
    __eo_prog_eq_cond_deq x_a0 x_a1 x_a2 x_a3 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_eq_cond_deq.case_0 x_a0 x_a1 x_a2 x_a3] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_eq_cond_deq
  unfold EoCases.__eo_prog_eq_cond_deq.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5feq_2dcond_2ddeq_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) :
    body_eo__24eo_5fprog_5feq_2dcond_2ddeq s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_eq_cond_deq x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5feq_2dcond_2ddeq.rust_eq x_a0 x_a1 x_a2 x_a3 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3)]
  unfold body_eo__24eo_5fprog_5feq_2dcond_2ddeq
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5feq_2dcond_2ddeq_spec n ih s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 using hn_a0 hn_a1 hn_a2
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hc0 in EoCases.__eo_prog_eq_cond_deq.case_0

theorem eo__24eo_5fprog_5feq_2dcond_2ddeq_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5feq_2dcond_2ddeq.Spec n := by
  intro s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3
  unfold eo__24eo_5fprog_5feq_2dcond_2ddeq
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5feq_2dcond_2ddeq s1 a0 a1 a2 a3) (fun s' t => Represents.rep s' t (__eo_prog_eq_cond_deq x_a0 x_a1 x_a2 x_a3))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5feq_2dcond_2ddeq_spec m (ih m hm) s1 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5feq_2dite_2dlift_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5feq_2dite_2dlift s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_eq_ite_lift.case_0 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_eq_ite_lift.case_0 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5feq_2dite_2dlift
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 dropping he_v0 e_v0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3d.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 dropping he_v1 hinv1 e_v1 s1
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo_ite.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 dropping he_v2 hinv2 e_v2 s2
  store_step with Store.apply_rep s3 v2 a0 _ _ hinv3 h64 h_v2 h_a0 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 dropping h_v2 hinv3 s3 v2
  store_step with Store.apply_rep s4 v3 a1 _ _ hinv4 h64 h_v3 h_a1 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 dropping h_v3 hinv4 s4 v3
  store_step with Store.apply_rep s5 v4 a2 _ _ hinv5 h64 h_v4 h_a2 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 dropping h_v4 hinv5 s5 v4
  store_step with Store.apply_rep s6 v1 v5 _ _ hinv6 h64 h_v1 h_v5 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 dropping h_v1 h_v5 hinv6 s6 v1 v5
  store_step with Store.apply_rep s7 v6 a3 _ _ hinv7 h64 h_v6 h_a3 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 dropping h_v6 hinv7 s7 v6
  store_step with Store.apply_rep s8 v0 v7 _ _ hinv8 h64 h_v0 h_v7 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 dropping h_v0 h_v7 hinv8 s8 v0 v7
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_ite.construct s9 e_v9 (by rw [he_v9]; exact empty_args) hinv9 h64 as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v8 dropping he_v9 hinv9 e_v9 s9
  store_step with Store.apply_rep s10 v9 a0 _ _ hinv10 h64 h_v9 h_a0 (by ns_tac) (by ns_tac) as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_a1 h_a2 h_a3 h_v8 dropping h_a0 h_v9 hinv10 s10 v9
  step as ⟨e_v11, he_v11⟩
  store_step with CtorSpec.eo__3d.construct s11 e_v11 (by rw [he_v11]; exact empty_args) hinv11 h64 as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_a1 h_a2 h_a3 h_v8 h_v10 dropping he_v11 hinv11 e_v11 s11
  store_step with Store.apply_rep s12 v11 a1 _ _ hinv12 h64 h_v11 h_a1 (by ns_tac) (by ns_tac) as ⟨v12, s13, hinv13, h_v12⟩ growing hG carrying h_a2 h_a3 h_v8 h_v10 dropping h_a1 h_v11 hinv12 s12 v11
  store_step with Store.apply_rep s13 v12 a3 _ _ hinv13 h64 h_v12 h_a3 (by ns_tac) (by ns_tac) as ⟨v13, s14, hinv14, h_v13⟩ growing hG carrying h_a2 h_a3 h_v8 h_v10 dropping h_v12 hinv13 s13 v12
  store_step with Store.apply_rep s14 v10 v13 _ _ hinv14 h64 h_v10 h_v13 (by ns_tac) (by ns_tac) as ⟨v14, s15, hinv15, h_v14⟩ growing hG carrying h_a2 h_a3 h_v8 dropping h_v10 h_v13 hinv14 s14 v10 v13
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__3d.construct s15 e_v15 (by rw [he_v15]; exact empty_args) hinv15 h64 as ⟨v15, s16, hinv16, h_v15⟩ growing hG carrying h_a2 h_a3 h_v8 h_v14 dropping he_v15 hinv15 e_v15 s15
  store_step with Store.apply_rep s16 v15 a2 _ _ hinv16 h64 h_v15 h_a2 (by ns_tac) (by ns_tac) as ⟨v16, s17, hinv17, h_v16⟩ growing hG carrying h_a3 h_v8 h_v14 dropping h_a2 h_v15 hinv16 s16 v15
  store_step with Store.apply_rep s17 v16 a3 _ _ hinv17 h64 h_v16 h_a3 (by ns_tac) (by ns_tac) as ⟨v17, s18, hinv18, h_v17⟩ growing hG carrying h_v8 h_v14 dropping h_a3 h_v16 hinv17 s17 v16
  store_step with Store.apply_rep s18 v14 v17 _ _ hinv18 h64 h_v14 h_v17 (by ns_tac) (by ns_tac) as ⟨v18, s19, hinv19, h_v18⟩ growing hG carrying h_v8 dropping h_v14 h_v17 hinv18 s18 v14 v17
  store_step with Store.apply_rep s19 v8 v18 _ _ hinv19 h64 h_v8 h_v18 (by ns_tac) (by ns_tac) as ⟨v19, s20, hinv20, h_v19⟩ growing hG carrying dropping h_v18 h_v8 hinv19 s19 v18 v8
  case_done hinv20 hG with h_v19 in EoCases.__eo_prog_eq_ite_lift.case_0 using hn_a0 hn_a1 hn_a2 hn_a3

/-- logos's `__eo_prog_eq_ite_lift` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5feq_2dite_2dlift.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) :
    __eo_prog_eq_ite_lift x_a0 x_a1 x_a2 x_a3 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_eq_ite_lift.case_0 x_a0 x_a1 x_a2 x_a3] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_eq_ite_lift
  unfold EoCases.__eo_prog_eq_ite_lift.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5feq_2dite_2dlift_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) :
    body_eo__24eo_5fprog_5feq_2dite_2dlift s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_eq_ite_lift x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5feq_2dite_2dlift.rust_eq x_a0 x_a1 x_a2 x_a3 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3)]
  unfold body_eo__24eo_5fprog_5feq_2dite_2dlift
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  stuck_check h_a3 : x_a3 as hn_a3 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5feq_2dite_2dlift_spec n ih s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2 hn_a3
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 using hn_a0 hn_a1 hn_a2 hn_a3
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hn_a3 hc0 in EoCases.__eo_prog_eq_ite_lift.case_0

theorem eo__24eo_5fprog_5feq_2dite_2dlift_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5feq_2dite_2dlift.Spec n := by
  intro s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3
  unfold eo__24eo_5fprog_5feq_2dite_2dlift
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5feq_2dite_2dlift s1 a0 a1 a2 a3) (fun s' t => Represents.rep s' t (__eo_prog_eq_ite_lift x_a0 x_a1 x_a2 x_a3))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5feq_2dite_2dlift_spec m (ih m hm) s1 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5feq_2drefl_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5feq_2drefl s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_eq_refl.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_eq_refl.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5feq_2drefl
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 dropping he_v0 e_v0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3d.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0 dropping he_v1 hinv1 e_v1 s1
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_v0 dropping h_v1 hinv2 s2 v1
  store_step with Store.apply_rep s3 v2 a0 _ _ hinv3 h64 h_v2 h_a0 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_v0 dropping h_a0 h_v2 hinv3 s3 v2
  store_step with Store.apply_rep s4 v0 v3 _ _ hinv4 h64 h_v0 h_v3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying dropping h_v0 h_v3 hinv4 s4 v0 v3
  store_step with Store.literal_boolean_spec s5 true hinv5 h64 as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_v4 dropping hinv5 s5
  store_step with Store.apply_rep s6 v4 v5 _ _ hinv6 h64 h_v4 h_v5 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying dropping h_v4 h_v5 hinv6 s6 v4 v5
  case_done hinv7 hG with h_v6 in EoCases.__eo_prog_eq_refl.case_0 using hn_a0

/-- logos's `__eo_prog_eq_refl` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5feq_2drefl.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_eq_refl x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_eq_refl.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_eq_refl
  unfold EoCases.__eo_prog_eq_refl.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5feq_2drefl_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5feq_2drefl s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_eq_refl x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5feq_2drefl.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5feq_2drefl
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5feq_2drefl_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_eq_refl.case_0

theorem eo__24eo_5fprog_5feq_2drefl_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5feq_2drefl.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5feq_2drefl
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5feq_2drefl s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_eq_refl x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5feq_2drefl_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5feq_2dsymm_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5feq_2dsymm s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_eq_symm.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_eq_symm.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5feq_2dsymm
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 dropping he_v0 e_v0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3d.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0 dropping he_v1 hinv1 e_v1 s1
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 dropping h_v1 hinv2 s2 v1
  store_step with Store.apply_rep s3 v2 a1 _ _ hinv3 h64 h_v2 h_a1 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_v0 dropping h_v2 hinv3 s3 v2
  store_step with Store.apply_rep s4 v0 v3 _ _ hinv4 h64 h_v0 h_v3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 dropping h_v0 h_v3 hinv4 s4 v0 v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__3d.construct s5 e_v5 (by rw [he_v5]; exact empty_args) hinv5 h64 as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_v4 dropping he_v5 hinv5 e_v5 s5
  store_step with Store.apply_rep s6 v5 a1 _ _ hinv6 h64 h_v5 h_a1 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_v4 dropping h_a1 h_v5 hinv6 s6 v5
  store_step with Store.apply_rep s7 v6 a0 _ _ hinv7 h64 h_v6 h_a0 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_v4 dropping h_a0 h_v6 hinv7 s7 v6
  store_step with Store.apply_rep s8 v4 v7 _ _ hinv8 h64 h_v4 h_v7 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying dropping h_v4 h_v7 hinv8 s8 v4 v7
  case_done hinv9 hG with h_v8 in EoCases.__eo_prog_eq_symm.case_0 using hn_a0 hn_a1

/-- logos's `__eo_prog_eq_symm` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5feq_2dsymm.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_eq_symm x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_eq_symm.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_eq_symm
  unfold EoCases.__eo_prog_eq_symm.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5feq_2dsymm_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5feq_2dsymm s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_eq_symm x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5feq_2dsymm.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5feq_2dsymm
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5feq_2dsymm_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_eq_symm.case_0

theorem eo__24eo_5fprog_5feq_2dsymm_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5feq_2dsymm.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5feq_2dsymm
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5feq_2dsymm s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_eq_symm x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5feq_2dsymm_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5feq_5fresolve_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_0_eo__24eo_5fprog_5feq_5fresolve s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_eq_resolve.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_eq_resolve.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5feq_5fresolve
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_eq_resolve.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a1 as ⟨v3, x_v3, h_v3⟩ else hinv hG in EoCases.__eo_prog_eq_resolve.case_0
  pat_unapply h_v3 as ⟨v5, v6, x_v5, x_v6, h_v5, h_v6, hn_v5, hn_v6⟩ using hinv else hinv hG in EoCases.__eo_prog_eq_resolve.case_0
  pat_unapply h_v5 as ⟨v8, v9, x_v8, x_v9, h_v8, h_v9, hn_v8, hn_v9⟩ using hinv else hinv hG in EoCases.__eo_prog_eq_resolve.case_0
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo__3d.construct s e_v10 (by rw [he_v10]; exact empty_args) hinv h64 as ⟨v10, s1, hinv1, h_v10⟩ growing hG carrying h_v1 h_v6 h_v8 h_v9 dropping h_a0 h_a1 h_v3 h_v5 he_v10 e_v10 v3 v5
  pat_same v8 v10 with h_v8 h_v10 using hinv1 else hinv1 hG in EoCases.__eo_prog_eq_resolve.case_0
  pat_same v9 v1 with h_v9 h_v1 using hinv1 else hinv1 hG in EoCases.__eo_prog_eq_resolve.case_0
  case_done hinv1 hG with h_v6 in EoCases.__eo_prog_eq_resolve.case_0 using hn_v5 hn_v6 hn_v8 hn_v9

/-- logos's `__eo_prog_eq_resolve` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5feq_5fresolve.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_eq_resolve x_a0 x_a1 =
      (firstSome [EoCases.__eo_prog_eq_resolve.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_eq_resolve
  unfold EoCases.__eo_prog_eq_resolve.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5feq_5fresolve_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5feq_5fresolve s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_eq_resolve x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5feq_5fresolve.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5feq_5fresolve
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fprog_5feq_5fresolve_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using
  body_stuck hinv1 hG using hc0 in EoCases.__eo_prog_eq_resolve.case_0

theorem eo__24eo_5fprog_5feq_5fresolve_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5feq_5fresolve.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5feq_5fresolve
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5feq_5fresolve s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_eq_resolve x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5feq_5fresolve_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fequiv_5felim1_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24eo_5fprog_5fequiv_5felim1 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_equiv_elim1.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_equiv_elim1.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fequiv_5felim1
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_equiv_elim1.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_equiv_elim1.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_equiv_elim1.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_v4 h_v6 h_v7 dropping h_a0 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_equiv_elim1.case_0
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_or.construct s1 e_v9 (by rw [he_v9]; exact empty_args) hinv1 h64 as ⟨v9, s2, hinv2, h_v9⟩ growing hG carrying h_v4 h_v7 dropping h_v6 h_v8 he_v9 hinv1 e_v9 s1 v6 v8
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo_not.construct s2 e_v10 (by rw [he_v10]; exact empty_args) hinv2 h64 as ⟨v10, s3, hinv3, h_v10⟩ growing hG carrying h_v4 h_v7 h_v9 dropping he_v10 hinv2 e_v10 s2
  store_step with Store.apply_rep s3 v10 v7 _ _ hinv3 h64 h_v10 h_v7 (by ns_tac) (by ns_tac) as ⟨v11, s4, hinv4, h_v11⟩ growing hG carrying h_v4 h_v9 dropping h_v10 h_v7 hinv3 s3 v10 v7
  store_step with Store.apply_rep s4 v9 v11 _ _ hinv4 h64 h_v9 h_v11 (by ns_tac) (by ns_tac) as ⟨v12, s5, hinv5, h_v12⟩ growing hG carrying h_v4 dropping h_v11 h_v9 hinv4 s4 v11 v9
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo_or.construct s5 e_v13 (by rw [he_v13]; exact empty_args) hinv5 h64 as ⟨v13, s6, hinv6, h_v13⟩ growing hG carrying h_v4 h_v12 dropping he_v13 hinv5 e_v13 s5
  store_step with Store.apply_rep s6 v13 v4 _ _ hinv6 h64 h_v13 h_v4 (by ns_tac) (by ns_tac) as ⟨v14, s7, hinv7, h_v14⟩ growing hG carrying h_v12 dropping h_v13 h_v4 hinv6 s6 v13 v4
  store_step with Store.literal_boolean_spec s7 false hinv7 h64 as ⟨v15, s8, hinv8, h_v15⟩ growing hG carrying h_v12 h_v14 dropping hinv7 s7
  store_step with Store.apply_rep s8 v14 v15 _ _ hinv8 h64 h_v14 h_v15 (by ns_tac) (by ns_tac) as ⟨v16, s9, hinv9, h_v16⟩ growing hG carrying h_v12 dropping h_v14 h_v15 hinv8 s8 v14 v15
  store_step with Store.apply_rep s9 v12 v16 _ _ hinv9 h64 h_v12 h_v16 (by ns_tac) (by ns_tac) as ⟨v17, s10, hinv10, h_v17⟩ growing hG carrying dropping h_v12 h_v16 hinv9 s9 v12 v16
  case_done hinv10 hG with h_v17 in EoCases.__eo_prog_equiv_elim1.case_0 using hn_v3 hn_v4 hn_v6 hn_v7

/-- logos's `__eo_prog_equiv_elim1` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fequiv_5felim1.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_equiv_elim1 x_a0 =
      (firstSome [EoCases.__eo_prog_equiv_elim1.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_equiv_elim1
  unfold EoCases.__eo_prog_equiv_elim1.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fequiv_5felim1_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fequiv_5felim1 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_equiv_elim1 x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fequiv_5felim1.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fequiv_5felim1
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fprog_5fequiv_5felim1_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using
  body_stuck hinv1 hG using hc0 in EoCases.__eo_prog_equiv_elim1.case_0

theorem eo__24eo_5fprog_5fequiv_5felim1_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fequiv_5felim1.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fequiv_5felim1
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fequiv_5felim1 s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_equiv_elim1 x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fequiv_5felim1_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fequiv_5felim2_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24eo_5fprog_5fequiv_5felim2 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_equiv_elim2.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_equiv_elim2.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fequiv_5felim2
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_equiv_elim2.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_equiv_elim2.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_equiv_elim2.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_v4 h_v6 h_v7 dropping h_a0 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_equiv_elim2.case_0
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_or.construct s1 e_v9 (by rw [he_v9]; exact empty_args) hinv1 h64 as ⟨v9, s2, hinv2, h_v9⟩ growing hG carrying h_v4 h_v7 dropping h_v6 h_v8 he_v9 hinv1 e_v9 s1 v6 v8
  store_step with Store.apply_rep s2 v9 v7 _ _ hinv2 h64 h_v9 h_v7 (by ns_tac) (by ns_tac) as ⟨v10, s3, hinv3, h_v10⟩ growing hG carrying h_v4 dropping h_v7 h_v9 hinv2 s2 v7 v9
  step as ⟨e_v11, he_v11⟩
  store_step with CtorSpec.eo_or.construct s3 e_v11 (by rw [he_v11]; exact empty_args) hinv3 h64 as ⟨v11, s4, hinv4, h_v11⟩ growing hG carrying h_v4 h_v10 dropping he_v11 hinv3 e_v11 s3
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo_not.construct s4 e_v12 (by rw [he_v12]; exact empty_args) hinv4 h64 as ⟨v12, s5, hinv5, h_v12⟩ growing hG carrying h_v4 h_v10 h_v11 dropping he_v12 hinv4 e_v12 s4
  store_step with Store.apply_rep s5 v12 v4 _ _ hinv5 h64 h_v12 h_v4 (by ns_tac) (by ns_tac) as ⟨v13, s6, hinv6, h_v13⟩ growing hG carrying h_v10 h_v11 dropping h_v12 h_v4 hinv5 s5 v12 v4
  store_step with Store.apply_rep s6 v11 v13 _ _ hinv6 h64 h_v11 h_v13 (by ns_tac) (by ns_tac) as ⟨v14, s7, hinv7, h_v14⟩ growing hG carrying h_v10 dropping h_v11 h_v13 hinv6 s6 v11 v13
  store_step with Store.literal_boolean_spec s7 false hinv7 h64 as ⟨v15, s8, hinv8, h_v15⟩ growing hG carrying h_v10 h_v14 dropping hinv7 s7
  store_step with Store.apply_rep s8 v14 v15 _ _ hinv8 h64 h_v14 h_v15 (by ns_tac) (by ns_tac) as ⟨v16, s9, hinv9, h_v16⟩ growing hG carrying h_v10 dropping h_v14 h_v15 hinv8 s8 v14 v15
  store_step with Store.apply_rep s9 v10 v16 _ _ hinv9 h64 h_v10 h_v16 (by ns_tac) (by ns_tac) as ⟨v17, s10, hinv10, h_v17⟩ growing hG carrying dropping h_v10 h_v16 hinv9 s9 v10 v16
  case_done hinv10 hG with h_v17 in EoCases.__eo_prog_equiv_elim2.case_0 using hn_v3 hn_v4 hn_v6 hn_v7

/-- logos's `__eo_prog_equiv_elim2` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fequiv_5felim2.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_equiv_elim2 x_a0 =
      (firstSome [EoCases.__eo_prog_equiv_elim2.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_equiv_elim2
  unfold EoCases.__eo_prog_equiv_elim2.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fequiv_5felim2_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fequiv_5felim2 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_equiv_elim2 x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fequiv_5felim2.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fequiv_5felim2
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fprog_5fequiv_5felim2_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using
  body_stuck hinv1 hG using hc0 in EoCases.__eo_prog_equiv_elim2.case_0

theorem eo__24eo_5fprog_5fequiv_5felim2_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fequiv_5felim2.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fequiv_5felim2
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fequiv_5felim2 s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_equiv_elim2 x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fequiv_5felim2_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fexists_2delim_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fexists_2delim s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_exists_elim.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_exists_elim.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fexists_2delim
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_prog_exists_elim.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_prog_exists_elim.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__3d.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_prog_exists_elim.case_0
  pat_unapply h_v5 as ⟨v8, v9, x_v8, x_v9, h_v8, h_v9, hn_v8, hn_v9⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_exists_elim.case_0
  pat_unapply h_v8 as ⟨v11, v12, x_v11, x_v12, h_v11, h_v12, hn_v11, hn_v12⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_exists_elim.case_0
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo_exists.construct s1 e_v13 (by rw [he_v13]; exact empty_args) hinv1 h64 as ⟨v13, s2, hinv2, h_v13⟩ growing hG carrying h_v2 h_v9 h_v11 h_v12 dropping h_v4 h_v5 h_v6 h_v8 he_v13 hinv1 e_v13 s1 v4 v5 v6 v8
  pat_same v11 v13 with h_v11 h_v13 using hinv2 else hinv2 hG in EoCases.__eo_prog_exists_elim.case_0
  pat_unapply h_v2 as ⟨v15, v16, x_v15, x_v16, h_v15, h_v16, hn_v15, hn_v16⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_exists_elim.case_0
  step as ⟨e_v17, he_v17⟩
  store_step with CtorSpec.eo_not.construct s2 e_v17 (by rw [he_v17]; exact empty_args) hinv2 h64 as ⟨v17, s3, hinv3, h_v17⟩ growing hG carrying h_v9 h_v12 h_v15 h_v16 dropping h_v11 h_v13 h_v2 he_v17 hinv2 e_v17 s2 v11 v13 v2
  pat_same v15 v17 with h_v15 h_v17 using hinv3 else hinv3 hG in EoCases.__eo_prog_exists_elim.case_0
  pat_unapply h_v16 as ⟨v19, v20, x_v19, x_v20, h_v19, h_v20, hn_v19, hn_v20⟩ using hinv3 else hinv3 hG in EoCases.__eo_prog_exists_elim.case_0
  pat_unapply h_v19 as ⟨v22, v23, x_v22, x_v23, h_v22, h_v23, hn_v22, hn_v23⟩ using hinv3 else hinv3 hG in EoCases.__eo_prog_exists_elim.case_0
  step as ⟨e_v24, he_v24⟩
  store_step with CtorSpec.eo_forall.construct s3 e_v24 (by rw [he_v24]; exact empty_args) hinv3 h64 as ⟨v24, s4, hinv4, h_v24⟩ growing hG carrying h_v9 h_v12 h_v20 h_v22 h_v23 dropping h_v15 h_v16 h_v17 h_v19 he_v24 hinv3 e_v24 s3 v15 v16 v17 v19
  pat_same v22 v24 with h_v22 h_v24 using hinv4 else hinv4 hG in EoCases.__eo_prog_exists_elim.case_0
  pat_same v23 v12 with h_v23 h_v12 using hinv4 else hinv4 hG in EoCases.__eo_prog_exists_elim.case_0
  pat_unapply h_v20 as ⟨v26, v27, x_v26, x_v27, h_v26, h_v27, hn_v26, hn_v27⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_exists_elim.case_0
  step as ⟨e_v28, he_v28⟩
  store_step with CtorSpec.eo_not.construct s4 e_v28 (by rw [he_v28]; exact empty_args) hinv4 h64 as ⟨v28, s5, hinv5, h_v28⟩ growing hG carrying h_v9 h_v12 h_v26 h_v27 dropping h_v20 h_v22 h_v23 h_v24 he_v28 hinv4 e_v28 s4 v20 v22 v23 v24
  pat_same v26 v28 with h_v26 h_v28 using hinv5 else hinv5 hG in EoCases.__eo_prog_exists_elim.case_0
  pat_same v27 v9 with h_v27 h_v9 using hinv5 else hinv5 hG in EoCases.__eo_prog_exists_elim.case_0
  step as ⟨e_v29, he_v29⟩
  store_step with CtorSpec.eo__3d.construct s5 e_v29 (by rw [he_v29]; exact empty_args) hinv5 h64 as ⟨v29, s6, hinv6, h_v29⟩ growing hG carrying h_v9 h_v12 dropping h_v26 h_v27 h_v28 he_v29 hinv5 e_v29 s5 v26 v27 v28
  step as ⟨e_v30, he_v30⟩
  store_step with CtorSpec.eo_exists.construct s6 e_v30 (by rw [he_v30]; exact empty_args) hinv6 h64 as ⟨v30, s7, hinv7, h_v30⟩ growing hG carrying h_v9 h_v12 h_v29 dropping he_v30 hinv6 e_v30 s6
  store_step with Store.apply_rep s7 v30 v12 _ _ hinv7 h64 h_v30 h_v12 (by ns_tac) (by ns_tac) as ⟨v31, s8, hinv8, h_v31⟩ growing hG carrying h_v9 h_v12 h_v29 dropping h_v30 hinv7 s7 v30
  store_step with Store.apply_rep s8 v31 v9 _ _ hinv8 h64 h_v31 h_v9 (by ns_tac) (by ns_tac) as ⟨v32, s9, hinv9, h_v32⟩ growing hG carrying h_v9 h_v12 h_v29 dropping h_v31 hinv8 s8 v31
  store_step with Store.apply_rep s9 v29 v32 _ _ hinv9 h64 h_v29 h_v32 (by ns_tac) (by ns_tac) as ⟨v33, s10, hinv10, h_v33⟩ growing hG carrying h_v9 h_v12 dropping h_v29 h_v32 hinv9 s9 v29 v32
  step as ⟨e_v34, he_v34⟩
  store_step with CtorSpec.eo_not.construct s10 e_v34 (by rw [he_v34]; exact empty_args) hinv10 h64 as ⟨v34, s11, hinv11, h_v34⟩ growing hG carrying h_v9 h_v12 h_v33 dropping he_v34 hinv10 e_v34 s10
  step as ⟨e_v35, he_v35⟩
  store_step with CtorSpec.eo_forall.construct s11 e_v35 (by rw [he_v35]; exact empty_args) hinv11 h64 as ⟨v35, s12, hinv12, h_v35⟩ growing hG carrying h_v9 h_v12 h_v33 h_v34 dropping he_v35 hinv11 e_v35 s11
  store_step with Store.apply_rep s12 v35 v12 _ _ hinv12 h64 h_v35 h_v12 (by ns_tac) (by ns_tac) as ⟨v36, s13, hinv13, h_v36⟩ growing hG carrying h_v9 h_v33 h_v34 dropping h_v12 h_v35 hinv12 s12 v12 v35
  step as ⟨e_v37, he_v37⟩
  store_step with CtorSpec.eo_not.construct s13 e_v37 (by rw [he_v37]; exact empty_args) hinv13 h64 as ⟨v37, s14, hinv14, h_v37⟩ growing hG carrying h_v9 h_v33 h_v34 h_v36 dropping he_v37 hinv13 e_v37 s13
  store_step with Store.apply_rep s14 v37 v9 _ _ hinv14 h64 h_v37 h_v9 (by ns_tac) (by ns_tac) as ⟨v38, s15, hinv15, h_v38⟩ growing hG carrying h_v33 h_v34 h_v36 dropping h_v37 h_v9 hinv14 s14 v37 v9
  store_step with Store.apply_rep s15 v36 v38 _ _ hinv15 h64 h_v36 h_v38 (by ns_tac) (by ns_tac) as ⟨v39, s16, hinv16, h_v39⟩ growing hG carrying h_v33 h_v34 dropping h_v36 h_v38 hinv15 s15 v36 v38
  store_step with Store.apply_rep s16 v34 v39 _ _ hinv16 h64 h_v34 h_v39 (by ns_tac) (by ns_tac) as ⟨v40, s17, hinv17, h_v40⟩ growing hG carrying h_v33 dropping h_v34 h_v39 hinv16 s16 v34 v39
  store_step with Store.apply_rep s17 v33 v40 _ _ hinv17 h64 h_v33 h_v40 (by ns_tac) (by ns_tac) as ⟨v41, s18, hinv18, h_v41⟩ growing hG carrying dropping h_v33 h_v40 hinv17 s17 v33 v40
  case_done hinv18 hG with h_v41 in EoCases.__eo_prog_exists_elim.case_0 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5 hn_v8 hn_v9 hn_v11 hn_v12 hn_v15 hn_v16 hn_v19 hn_v20 hn_v22 hn_v23 hn_v26 hn_v27

/-- logos's `__eo_prog_exists_elim` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fexists_2delim.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_exists_elim x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_exists_elim.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_exists_elim
  unfold EoCases.__eo_prog_exists_elim.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fexists_2delim_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fexists_2delim s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_exists_elim x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fexists_2delim.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fexists_2delim
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fexists_2delim_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_exists_elim.case_0

theorem eo__24eo_5fprog_5fexists_2delim_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fexists_2delim.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fexists_2delim
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fexists_2delim s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_exists_elim x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fexists_2delim_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fexists_5fstring_5flength_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fexists_5fstring_5flength s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_exists_string_length.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_exists_string_length.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fexists_5fstring_5flength
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_prog_exists_string_length.case_0
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_Seq.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a1 h_a2 h_v1 h_v2 dropping h_a0 he_v3 e_v3
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_prog_exists_string_length.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_neg_u32_spec s1 1#u32 (-1) (by scalar_tac) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a1 h_a2 h_v2 dropping h_v1 h_v3 hinv1 s1 v1 v3
  step as ⟨e_v5, he_v5⟩
  store_step with Store.builtin_spec_gt s2 e_v5 (by rw [he_v5]; rfl) h_a1 h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a1 h_a2 h_v2 dropping h_v4 he_v5 hinv2 e_v5 s2 v4
  store_step with Store.literal_boolean_spec s3 true hinv3 h64 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a1 h_a2 h_v2 h_v5 dropping hinv3 s3
  have h_req_v19 := (show requires_1_eo__24eo_5fprog_5fexists_5fstring_5flength s4 v5 v6 a2 v2 a1 ⦃ r s' => s'.Inv ∧ s4.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold requires_1_eo__24eo_5fprog_5fexists_5fstring_5flength
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s4
    req_same v5 v6 with h_v5 h_v6 using hinv4 hG
    req_stuck h_v5 as hq_v5 using hinv4 hG
    try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
    store_step with Store.literal_int_neg_u32_spec s4 1#u32 (-1) (by scalar_tac) hinv4 h64 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_a1 h_a2 h_v2 dropping h_v5 h_v6 hinv4 s4 v5 v6
    step as ⟨e_v8, he_v8⟩
    store_step with Store.builtin_spec_gt s5 e_v8 (by rw [he_v8]; rfl) h_a2 h_v7 hinv5 h64 as ⟨v8, s6, hinv6, h_v8⟩ growing hG carrying h_a1 h_a2 h_v2 dropping h_v7 he_v8 hinv5 e_v8 s5 v7
    store_step with Store.literal_boolean_spec s6 true hinv6 h64 as ⟨v9, s7, hinv7, h_v9⟩ growing hG carrying h_a1 h_a2 h_v2 h_v8 dropping hinv6 s6
    have h_req_v18 := (show requires_0_eo__24eo_5fprog_5fexists_5fstring_5flength s7 v8 v9 v2 a1 a2 ⦃ r s' => s'.Inv ∧ s7.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
      unfold requires_0_eo__24eo_5fprog_5fexists_5fstring_5flength
      have hrem := (hG.rem hrem)
      have hG := Store.Grows.refl s7
      req_same v8 v9 with h_v8 h_v9 using hinv7 hG
      req_stuck h_v8 as hq_v8 using hinv7 hG
      step as ⟨e_v10, he_v10⟩
      store_step with CtorSpec.eo__3d.construct s7 e_v10 (by rw [he_v10]; exact empty_args) hinv7 h64 as ⟨v10, s8, hinv8, h_v10⟩ growing hG carrying h_a1 h_a2 h_v2 dropping h_v8 h_v9 he_v10 hinv7 e_v10 s7 v8 v9
      step as ⟨e_v11, he_v11⟩
      store_step with CtorSpec.eo_str_2elen.construct s8 e_v11 (by rw [he_v11]; exact empty_args) hinv8 h64 as ⟨v11, s9, hinv9, h_v11⟩ growing hG carrying h_a1 h_a2 h_v2 h_v10 dropping he_v11 hinv8 e_v11 s8
      step as ⟨e_v12, he_v12⟩
      store_step with CtorSpec.eo_Seq.construct s9 e_v12 (by rw [he_v12]; exact empty_args) hinv9 h64 as ⟨v12, s10, hinv10, h_v12⟩ growing hG carrying h_a1 h_a2 h_v2 h_v10 h_v11 dropping he_v12 hinv9 e_v12 s9
      store_step with Store.apply_rep s10 v12 v2 _ _ hinv10 h64 h_v12 h_v2 (by ns_tac) (by ns_tac) as ⟨v13, s11, hinv11, h_v13⟩ growing hG carrying h_a1 h_a2 h_v10 h_v11 dropping h_v12 h_v2 hinv10 s10 v12 v2
      step as ⟨e_v14, he_v14⟩
      store_step with CtorSpec.eo__40witness_5fstring_5flength.construct s11 e_v14 (by rw [he_v14]; rfl) h_v13 h_a1 h_a2 hinv11 h64 as ⟨v14, s12, hinv12, h_v14⟩ growing hG carrying h_a1 h_v10 h_v11 dropping h_a2 h_v13 he_v14 hinv11 e_v14 s11 v13
      store_step with Store.apply_rep s12 v11 v14 _ _ hinv12 h64 h_v11 h_v14 (by ns_tac) (by ns_tac) as ⟨v15, s13, hinv13, h_v15⟩ growing hG carrying h_a1 h_v10 dropping h_v11 h_v14 hinv12 s12 v11 v14
      store_step with Store.apply_rep s13 v10 v15 _ _ hinv13 h64 h_v10 h_v15 (by ns_tac) (by ns_tac) as ⟨v16, s14, hinv14, h_v16⟩ growing hG carrying h_a1 dropping h_v10 h_v15 hinv13 s13 v10 v15
      store_step with Store.apply_rep s14 v16 a1 _ _ hinv14 h64 h_v16 h_a1 (by ns_tac) (by ns_tac) as ⟨v17, s15, hinv15, h_v17⟩ growing hG carrying dropping h_a1 h_v16 hinv14 s14 v16
      req_done hinv15 hG with h_v17 using hq_v8)
    store_step with h_req_v18 as ⟨v18, s16, hinv16, h_v18⟩ growing hG carrying dropping h_a1 h_a2 h_req_v18 h_v2 h_v8 h_v9 hinv7 s7 v2 v8 v9
    req_done hinv16 hG with h_v18 using hq_v5)
  store_step with h_req_v19 as ⟨v19, s17, hinv17, h_v19⟩ growing hG carrying dropping h_a1 h_req_v19 h_v2 h_v5 h_v6 hinv4 s4 v2 v5 v6
  case_done hinv17 hG with h_v19 in EoCases.__eo_prog_exists_string_length.case_0 using hn_a0 hn_a1 hn_a2 hn_v1 hn_v2

/-- logos's `__eo_prog_exists_string_length` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fexists_5fstring_5flength.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __eo_prog_exists_string_length x_a0 x_a1 x_a2 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_exists_string_length.case_0 x_a0 x_a1 x_a2] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_exists_string_length
  unfold EoCases.__eo_prog_exists_string_length.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fexists_5fstring_5flength_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24eo_5fprog_5fexists_5fstring_5flength s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_exists_string_length x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fexists_5fstring_5flength.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24eo_5fprog_5fexists_5fstring_5flength
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fexists_5fstring_5flength_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1 hn_a2
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hc0 in EoCases.__eo_prog_exists_string_length.case_0

theorem eo__24eo_5fprog_5fexists_5fstring_5flength_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fexists_5fstring_5flength.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24eo_5fprog_5fexists_5fstring_5flength
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fexists_5fstring_5flength s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__eo_prog_exists_string_length x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fexists_5fstring_5flength_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5ffactoring_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24eo_5fprog_5ffactoring s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_factoring.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_factoring.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5ffactoring
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_factoring.case_0
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo_or.construct s e_v2 (by rw [he_v2]; exact empty_args) hinv h64 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying h_v1 dropping h_a0 he_v2 e_v2
  step as ⟨e_v3, he_v3⟩
  store_step with Store.builtin_spec_list_setof n ih.eo__24eo_5fis_5flist_5fnil s1 e_v3 (by rw [he_v3]; rfl) h_v2 h_v1 hinv1 h64 (hG.rem hrem) op_not_left_eo_or as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying dropping h_v1 h_v2 he_v3 hinv1 e_v3 s1 v1 v2
  store_step with ih.eo__24from_5fclause s2 v3 _ hinv2 h64 (hG.rem hrem) h_v3 as ⟨v4, s3, hinv3, h_v4⟩ growing hG carrying dropping h_v3 hinv2 s2 v3
  case_done hinv3 hG with h_v4 in EoCases.__eo_prog_factoring.case_0 using

/-- logos's `__eo_prog_factoring` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5ffactoring.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_factoring x_a0 =
      (firstSome [EoCases.__eo_prog_factoring.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_factoring
  unfold EoCases.__eo_prog_factoring.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5ffactoring_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5ffactoring s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_factoring x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5ffactoring.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5ffactoring
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fprog_5ffactoring_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using
  body_stuck hinv1 hG using hc0 in EoCases.__eo_prog_factoring.case_0

theorem eo__24eo_5fprog_5ffactoring_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5ffactoring.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5ffactoring
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5ffactoring s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_factoring x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5ffactoring_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

end pathos_compiled_checker
