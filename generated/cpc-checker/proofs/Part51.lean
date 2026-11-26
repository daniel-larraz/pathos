module
public import $PROOFS$.Head
public import $CHECKER$
public import $CALC$.Logos
import all $CALC$.Logos
public import $CALC$.SmtTranslate
import all $CALC$.SmtTranslate
public import $CALC$.SmtModel
import all $CALC$.SmtModel
public import $CASES$
import all $CASES$
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

set_option maxHeartbeats 6000000 in
theorem case_0_eo__24eo_5fprog_5fconcat_5fcsplit_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fconcat_5fcsplit s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_concat_csplit.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_concat_csplit.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fconcat_5fcsplit more_13_eo__24eo_5fprog_5fconcat_5fcsplit
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a1 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_concat_csplit.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_concat_csplit.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_concat_csplit.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_concat_csplit.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a2 as ⟨v10, x_v10, h_v10⟩ else hinv1 hG in EoCases.__eo_prog_concat_csplit.case_0
  pat_unapply h_v10 as ⟨v12, v13, x_v12, x_v13, h_v12, h_v13, hn_v12, hn_v13⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_concat_csplit.case_0
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo_not.construct s1 e_v14 (by rw [he_v14]; exact empty_args) hinv1 h64 as ⟨v14, s2, hinv2, h_v14⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13
  pat_same v12 v14 with h_v12 h_v14 using hinv2 else hinv2 hG in EoCases.__eo_prog_concat_csplit.case_0
  pat_unapply h_v13 as ⟨v16, v17, x_v16, x_v17, h_v16, h_v17, hn_v16, hn_v17⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_concat_csplit.case_0
  pat_unapply h_v16 as ⟨v19, v20, x_v19, x_v20, h_v19, h_v20, hn_v19, hn_v20⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_concat_csplit.case_0
  step as ⟨e_v21, he_v21⟩
  store_step with CtorSpec.eo__3d.construct s2 e_v21 (by rw [he_v21]; exact empty_args) hinv2 h64 as ⟨v21, s3, hinv3, h_v21⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20
  pat_same v19 v21 with h_v19 h_v21 using hinv3 else hinv3 hG in EoCases.__eo_prog_concat_csplit.case_0
  pat_unapply h_v20 as ⟨v23, v24, x_v23, x_v24, h_v23, h_v24, hn_v23, hn_v24⟩ using hinv3 else hinv3 hG in EoCases.__eo_prog_concat_csplit.case_0
  step as ⟨e_v25, he_v25⟩
  store_step with CtorSpec.eo_str_2elen.construct s3 e_v25 (by rw [he_v25]; exact empty_args) hinv3 h64 as ⟨v25, s4, hinv4, h_v25⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24
  pat_same v23 v25 with h_v23 h_v25 using hinv4 else hinv4 hG in EoCases.__eo_prog_concat_csplit.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s4 0#u32 (0) (by scalar_tac) hinv4 h64 as ⟨v26, s5, hinv5, h_v26⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25
  pat_same v17 v26 with h_v17 h_v26 using hinv5 else hinv5 hG in EoCases.__eo_prog_concat_csplit.case_0
  step as ⟨e_v27, he_v27⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s5 e_v27 (by rw [he_v27]; exact empty_args) hinv5 h64 as ⟨v27, s6, hinv6, h_v27⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26
  have h_ite_v34 := (show if_0_eo__24eo_5fprog_5fconcat_5fcsplit s6 a0 v7 ⦃ r s' => s'.Inv ∧ s6.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_0_eo__24eo_5fprog_5fconcat_5fcsplit
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s6
    rcases Store.boolean_value_term h_a0 with ⟨hx_28, hbv_28⟩ | ⟨hx_28, hbv_28⟩ | ⟨hx_28, hbv_28⟩
    · ite_branch hbv_28
      step as ⟨e_v28, he_v28⟩
      store_step with CtorSpec.eo_str_2e_2b_2b.construct s6 e_v28 (by rw [he_v28]; exact empty_args) hinv6 h64 as ⟨v28, s7, hinv7, h_v28⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27
      step as ⟨e_v29, he_v29⟩
      store_step with CtorSpec.eo_str_2e_2b_2b.construct s7 e_v29 (by rw [he_v29]; exact empty_args) hinv7 h64 as ⟨v29, s8, hinv8, h_v29⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28
      step as ⟨e_v30, he_v30⟩
      store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s8 e_v30 (by rw [he_v30]; rfl) h_v29 h_v7 hinv8 h64 (hG.rem hrem) (by not_left_tac) (by nil_self_tac) as ⟨v30, s9, hinv9, h_v30⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29
      step as ⟨e_v31, he_v31⟩
      store_step with Store.builtin_spec_list_rev n ih.eo__24eo_5fis_5flist_5fnil s9 e_v31 (by rw [he_v31]; rfl) h_v28 h_v30 hinv9 h64 (hG.rem hrem) (by not_left_tac) as ⟨v31, s10, hinv10, h_v31⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30
      ite_done hinv10 hG with (eo_ite_true_rep _ hx_28 h_v31)
    · ite_branch hbv_28
      step as ⟨e_v32, he_v32⟩
      store_step with CtorSpec.eo_str_2e_2b_2b.construct s6 e_v32 (by rw [he_v32]; exact empty_args) hinv6 h64 as ⟨v32, s7, hinv7, h_v32⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27
      step as ⟨e_v33, he_v33⟩
      store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s7 e_v33 (by rw [he_v33]; rfl) h_v32 h_v7 hinv7 h64 (hG.rem hrem) (by not_left_tac) (by nil_self_tac) as ⟨v33, s8, hinv8, h_v33⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v32
      ite_done hinv8 hG with (eo_ite_false_rep _ hx_28 h_v33)
    · ite_branch hbv_28
      ite_stuck hinv6 hG with hx_28)
  store_step with h_ite_v34 as ⟨v34, s7, hinv7, h_v34⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s7 0#u32 (0) (by scalar_tac) hinv7 h64 as ⟨v35, s8, hinv8, h_v35⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34
  step as ⟨e_v36, he_v36⟩
  store_step with Store.builtin_spec_list_nth n ih.eo__24eo_5fis_5flist_5fnil s8 e_v36 (by rw [he_v36]; rfl) h_v27 h_v34 h_v35 hinv8 h64 (hG.rem hrem) (by not_left_tac) as ⟨v36, s9, hinv9, h_v36⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35
  have h_req_v143 := (show requires_12_eo__24eo_5fprog_5fconcat_5fcsplit s9 v36 v24 a0 v4 ⦃ r s' => s'.Inv ∧ s9.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold requires_12_eo__24eo_5fprog_5fconcat_5fcsplit
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s9
    req_same v36 v24 with h_v36 h_v24 using hinv9 hG
    req_stuck h_v36 as hq_v36 using hinv9 hG
    step as ⟨e_v37, he_v37⟩
    store_step with CtorSpec.eo_str_2e_2b_2b.construct s9 e_v37 (by rw [he_v37]; exact empty_args) hinv9 h64 as ⟨v37, s10, hinv10, h_v37⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36
    have h_ite_v44 := (show if_1_eo__24eo_5fprog_5fconcat_5fcsplit s10 a0 v4 ⦃ r s' => s'.Inv ∧ s10.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
      unfold if_1_eo__24eo_5fprog_5fconcat_5fcsplit
      have hrem := (hG.rem hrem)
      have hG := Store.Grows.refl s10
      rcases Store.boolean_value_term h_a0 with ⟨hx_38, hbv_38⟩ | ⟨hx_38, hbv_38⟩ | ⟨hx_38, hbv_38⟩
      · ite_branch hbv_38
        step as ⟨e_v38, he_v38⟩
        store_step with CtorSpec.eo_str_2e_2b_2b.construct s10 e_v38 (by rw [he_v38]; exact empty_args) hinv10 h64 as ⟨v38, s11, hinv11, h_v38⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37
        step as ⟨e_v39, he_v39⟩
        store_step with CtorSpec.eo_str_2e_2b_2b.construct s11 e_v39 (by rw [he_v39]; exact empty_args) hinv11 h64 as ⟨v39, s12, hinv12, h_v39⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v38
        step as ⟨e_v40, he_v40⟩
        store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s12 e_v40 (by rw [he_v40]; rfl) h_v39 h_v4 hinv12 h64 (hG.rem hrem) (by not_left_tac) (by nil_self_tac) as ⟨v40, s13, hinv13, h_v40⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39
        step as ⟨e_v41, he_v41⟩
        store_step with Store.builtin_spec_list_rev n ih.eo__24eo_5fis_5flist_5fnil s13 e_v41 (by rw [he_v41]; rfl) h_v38 h_v40 hinv13 h64 (hG.rem hrem) (by not_left_tac) as ⟨v41, s14, hinv14, h_v41⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40
        ite_done hinv14 hG with (eo_ite_true_rep _ hx_38 h_v41)
      · ite_branch hbv_38
        step as ⟨e_v42, he_v42⟩
        store_step with CtorSpec.eo_str_2e_2b_2b.construct s10 e_v42 (by rw [he_v42]; exact empty_args) hinv10 h64 as ⟨v42, s11, hinv11, h_v42⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37
        step as ⟨e_v43, he_v43⟩
        store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s11 e_v43 (by rw [he_v43]; rfl) h_v42 h_v4 hinv11 h64 (hG.rem hrem) (by not_left_tac) (by nil_self_tac) as ⟨v43, s12, hinv12, h_v43⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v42
        ite_done hinv12 hG with (eo_ite_false_rep _ hx_38 h_v43)
      · ite_branch hbv_38
        ite_stuck hinv10 hG with hx_38)
    store_step with h_ite_v44 as ⟨v44, s11, hinv11, h_v44⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37
    try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
    store_step with Store.literal_int_u32_spec s11 0#u32 (0) (by scalar_tac) hinv11 h64 as ⟨v45, s12, hinv12, h_v45⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44
    step as ⟨e_v46, he_v46⟩
    store_step with Store.builtin_spec_list_nth n ih.eo__24eo_5fis_5flist_5fnil s12 e_v46 (by rw [he_v46]; rfl) h_v37 h_v44 h_v45 hinv12 h64 (hG.rem hrem) (by not_left_tac) as ⟨v46, s13, hinv13, h_v46⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45
    step as ⟨e_v47, he_v47⟩
    store_step with Store.builtin_spec_len s13 e_v47 (by rw [he_v47]; rfl) h_v46 hinv13 h64 as ⟨v47, s14, hinv14, h_v47⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46
    try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
    store_step with Store.literal_int_u32_spec s14 1#u32 (1) (by scalar_tac) hinv14 h64 as ⟨v48, s15, hinv15, h_v48⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47
    step as ⟨e_v49, he_v49⟩
    store_step with Store.builtin_spec_is_eq s15 e_v49 (by rw [he_v49]; rfl) h_v47 h_v48 hinv15 h64 as ⟨v49, s16, hinv16, h_v49⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47 h_v48
    store_step with Store.literal_boolean_spec s16 true hinv16 h64 as ⟨v50, s17, hinv17, h_v50⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49
    have h_req_v142 := (show requires_11_eo__24eo_5fprog_5fconcat_5fcsplit s17 v49 v50 v24 a0 v4 ⦃ r s' => s'.Inv ∧ s17.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
      unfold requires_11_eo__24eo_5fprog_5fconcat_5fcsplit
      have hrem := (hG.rem hrem)
      have hG := Store.Grows.refl s17
      req_same v49 v50 with h_v49 h_v50 using hinv17 hG
      req_stuck h_v49 as hq_v49 using hinv17 hG
      step as ⟨e_v51, he_v51⟩
      store_step with CtorSpec.eo__3d.construct s17 e_v51 (by rw [he_v51]; exact empty_args) hinv17 h64 as ⟨v51, s18, hinv18, h_v51⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50
      store_step with Store.apply_rep s18 v51 v24 _ _ hinv18 h64 h_v51 h_v24 (by ns_tac) (by ns_tac) as ⟨v52, s19, hinv19, h_v52⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51
      have h_ite_v140 := (show if_10_eo__24eo_5fprog_5fconcat_5fcsplit s19 a0 v24 a0 v4 ⦃ r s' => s'.Inv ∧ s19.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_10_eo__24eo_5fprog_5fconcat_5fcsplit more_5_eo__24eo_5fprog_5fconcat_5fcsplit more_6_eo__24eo_5fprog_5fconcat_5fcsplit more_7_eo__24eo_5fprog_5fconcat_5fcsplit more_8_eo__24eo_5fprog_5fconcat_5fcsplit more_9_eo__24eo_5fprog_5fconcat_5fcsplit
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s19
        rcases Store.boolean_value_term h_a0 with ⟨hx_53, hbv_53⟩ | ⟨hx_53, hbv_53⟩ | ⟨hx_53, hbv_53⟩
        · ite_branch hbv_53
          step as ⟨e_v53, he_v53⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s19 e_v53 (by rw [he_v53]; exact empty_args) hinv19 h64 as ⟨v53, s20, hinv20, h_v53⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52
          step as ⟨e_v54, he_v54⟩
          store_step with CtorSpec.eo__40purify.construct s20 e_v54 (by rw [he_v54]; exact empty_args) hinv20 h64 as ⟨v54, s21, hinv21, h_v54⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53
          step as ⟨e_v55, he_v55⟩
          store_step with CtorSpec.eo_str_2esubstr.construct s21 e_v55 (by rw [he_v55]; exact empty_args) hinv21 h64 as ⟨v55, s22, hinv22, h_v55⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54
          store_step with Store.apply_rep s22 v55 v24 _ _ hinv22 h64 h_v55 h_v24 (by ns_tac) (by ns_tac) as ⟨v56, s23, hinv23, h_v56⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s23 0#u32 (0) (by scalar_tac) hinv23 h64 as ⟨v57, s24, hinv24, h_v57⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56
          store_step with Store.apply_rep s24 v56 v57 _ _ hinv24 h64 h_v56 h_v57 (by ns_tac) (by ns_tac) as ⟨v58, s25, hinv25, h_v58⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57
          step as ⟨e_v59, he_v59⟩
          store_step with CtorSpec.eo__2d.construct s25 e_v59 (by rw [he_v59]; exact empty_args) hinv25 h64 as ⟨v59, s26, hinv26, h_v59⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58
          step as ⟨e_v60, he_v60⟩
          store_step with CtorSpec.eo_str_2elen.construct s26 e_v60 (by rw [he_v60]; exact empty_args) hinv26 h64 as ⟨v60, s27, hinv27, h_v60⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59
          store_step with Store.apply_rep s27 v60 v24 _ _ hinv27 h64 h_v60 h_v24 (by ns_tac) (by ns_tac) as ⟨v61, s28, hinv28, h_v61⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60
          store_step with Store.apply_rep s28 v59 v61 _ _ hinv28 h64 h_v59 h_v61 (by ns_tac) (by ns_tac) as ⟨v62, s29, hinv29, h_v62⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s29 1#u32 (1) (by scalar_tac) hinv29 h64 as ⟨v63, s30, hinv30, h_v63⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62
          store_step with Store.apply_rep s30 v62 v63 _ _ hinv30 h64 h_v62 h_v63 (by ns_tac) (by ns_tac) as ⟨v64, s31, hinv31, h_v64⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63
          store_step with Store.apply_rep s31 v58 v64 _ _ hinv31 h64 h_v58 h_v64 (by ns_tac) (by ns_tac) as ⟨v65, s32, hinv32, h_v65⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64
          store_step with Store.apply_rep s32 v54 v65 _ _ hinv32 h64 h_v54 h_v65 (by ns_tac) (by ns_tac) as ⟨v66, s33, hinv33, h_v66⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65
          store_step with Store.apply_rep s33 v53 v66 _ _ hinv33 h64 h_v53 h_v66 (by ns_tac) (by ns_tac) as ⟨v67, s34, hinv34, h_v67⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66
          step as ⟨e_v68, he_v68⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s34 e_v68 (by rw [he_v68]; exact empty_args) hinv34 h64 as ⟨v68, s35, hinv35, h_v68⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67
          step as ⟨e_v69, he_v69⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s35 e_v69 (by rw [he_v69]; exact empty_args) hinv35 h64 as ⟨v69, s36, hinv36, h_v69⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68
          have h_ite_v76 := (show if_2_eo__24eo_5fprog_5fconcat_5fcsplit s36 a0 v4 ⦃ r s' => s'.Inv ∧ s36.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
            unfold if_2_eo__24eo_5fprog_5fconcat_5fcsplit
            have hrem := (hG.rem hrem)
            have hG := Store.Grows.refl s36
            rcases Store.boolean_value_term h_a0 with ⟨hx_70, hbv_70⟩ | ⟨hx_70, hbv_70⟩ | ⟨hx_70, hbv_70⟩
            · ite_branch hbv_70
              step as ⟨e_v70, he_v70⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s36 e_v70 (by rw [he_v70]; exact empty_args) hinv36 h64 as ⟨v70, s37, hinv37, h_v70⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69
              step as ⟨e_v71, he_v71⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s37 e_v71 (by rw [he_v71]; exact empty_args) hinv37 h64 as ⟨v71, s38, hinv38, h_v71⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70
              step as ⟨e_v72, he_v72⟩
              store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s38 e_v72 (by rw [he_v72]; rfl) h_v71 h_v4 hinv38 h64 (hG.rem hrem) (by not_left_tac) (by nil_self_tac) as ⟨v72, s39, hinv39, h_v72⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70 h_v71
              step as ⟨e_v73, he_v73⟩
              store_step with Store.builtin_spec_list_rev n ih.eo__24eo_5fis_5flist_5fnil s39 e_v73 (by rw [he_v73]; rfl) h_v70 h_v72 hinv39 h64 (hG.rem hrem) (by not_left_tac) as ⟨v73, s40, hinv40, h_v73⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70 h_v71 h_v72
              ite_done hinv40 hG with (eo_ite_true_rep _ hx_70 h_v73)
            · ite_branch hbv_70
              step as ⟨e_v74, he_v74⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s36 e_v74 (by rw [he_v74]; exact empty_args) hinv36 h64 as ⟨v74, s37, hinv37, h_v74⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69
              step as ⟨e_v75, he_v75⟩
              store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s37 e_v75 (by rw [he_v75]; rfl) h_v74 h_v4 hinv37 h64 (hG.rem hrem) (by not_left_tac) (by nil_self_tac) as ⟨v75, s38, hinv38, h_v75⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v74
              ite_done hinv38 hG with (eo_ite_false_rep _ hx_70 h_v75)
            · ite_branch hbv_70
              ite_stuck hinv36 hG with hx_70)
          store_step with h_ite_v76 as ⟨v76, s37, hinv37, h_v76⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s37 0#u32 (0) (by scalar_tac) hinv37 h64 as ⟨v77, s38, hinv38, h_v77⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v76
          step as ⟨e_v78, he_v78⟩
          store_step with Store.builtin_spec_list_nth n ih.eo__24eo_5fis_5flist_5fnil s38 e_v78 (by rw [he_v78]; rfl) h_v69 h_v76 h_v77 hinv38 h64 (hG.rem hrem) (by not_left_tac) as ⟨v78, s39, hinv39, h_v78⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v76 h_v77
          store_step with Store.apply_mk_rep s39 v68 v78 _ _ hinv39 h64 h_v68 h_v78 as ⟨v79, s40, hinv40, h_v79⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v76 h_v77 h_v78
          step as ⟨e_v80, he_v80⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s40 e_v80 (by rw [he_v80]; exact empty_args) hinv40 h64 as ⟨v80, s41, hinv41, h_v80⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v76 h_v77 h_v78 h_v79
          step as ⟨e_v81, he_v81⟩
          store_step with CtorSpec.eo__40purify.construct s41 e_v81 (by rw [he_v81]; exact empty_args) hinv41 h64 as ⟨v81, s42, hinv42, h_v81⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v76 h_v77 h_v78 h_v79 h_v80
          step as ⟨e_v82, he_v82⟩
          store_step with CtorSpec.eo_str_2esubstr.construct s42 e_v82 (by rw [he_v82]; exact empty_args) hinv42 h64 as ⟨v82, s43, hinv43, h_v82⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v76 h_v77 h_v78 h_v79 h_v80 h_v81
          store_step with Store.apply_rep s43 v82 v24 _ _ hinv43 h64 h_v82 h_v24 (by ns_tac) (by ns_tac) as ⟨v83, s44, hinv44, h_v83⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v76 h_v77 h_v78 h_v79 h_v80 h_v81 h_v82
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s44 0#u32 (0) (by scalar_tac) hinv44 h64 as ⟨v84, s45, hinv45, h_v84⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v76 h_v77 h_v78 h_v79 h_v80 h_v81 h_v82 h_v83
          store_step with Store.apply_rep s45 v83 v84 _ _ hinv45 h64 h_v83 h_v84 (by ns_tac) (by ns_tac) as ⟨v85, s46, hinv46, h_v85⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v76 h_v77 h_v78 h_v79 h_v80 h_v81 h_v82 h_v83 h_v84
          step as ⟨e_v86, he_v86⟩
          store_step with CtorSpec.eo__2d.construct s46 e_v86 (by rw [he_v86]; exact empty_args) hinv46 h64 as ⟨v86, s47, hinv47, h_v86⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v76 h_v77 h_v78 h_v79 h_v80 h_v81 h_v82 h_v83 h_v84 h_v85
          step as ⟨e_v87, he_v87⟩
          store_step with CtorSpec.eo_str_2elen.construct s47 e_v87 (by rw [he_v87]; exact empty_args) hinv47 h64 as ⟨v87, s48, hinv48, h_v87⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v76 h_v77 h_v78 h_v79 h_v80 h_v81 h_v82 h_v83 h_v84 h_v85 h_v86
          store_step with Store.apply_rep s48 v87 v24 _ _ hinv48 h64 h_v87 h_v24 (by ns_tac) (by ns_tac) as ⟨v88, s49, hinv49, h_v88⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v76 h_v77 h_v78 h_v79 h_v80 h_v81 h_v82 h_v83 h_v84 h_v85 h_v86 h_v87
          store_step with Store.apply_rep s49 v86 v88 _ _ hinv49 h64 h_v86 h_v88 (by ns_tac) (by ns_tac) as ⟨v89, s50, hinv50, h_v89⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v76 h_v77 h_v78 h_v79 h_v80 h_v81 h_v82 h_v83 h_v84 h_v85 h_v86 h_v87 h_v88
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s50 1#u32 (1) (by scalar_tac) hinv50 h64 as ⟨v90, s51, hinv51, h_v90⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v76 h_v77 h_v78 h_v79 h_v80 h_v81 h_v82 h_v83 h_v84 h_v85 h_v86 h_v87 h_v88 h_v89
          store_step with Store.apply_rep s51 v89 v90 _ _ hinv51 h64 h_v89 h_v90 (by ns_tac) (by ns_tac) as ⟨v91, s52, hinv52, h_v91⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v76 h_v77 h_v78 h_v79 h_v80 h_v81 h_v82 h_v83 h_v84 h_v85 h_v86 h_v87 h_v88 h_v89 h_v90
          store_step with Store.apply_rep s52 v85 v91 _ _ hinv52 h64 h_v85 h_v91 (by ns_tac) (by ns_tac) as ⟨v92, s53, hinv53, h_v92⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v76 h_v77 h_v78 h_v79 h_v80 h_v81 h_v82 h_v83 h_v84 h_v85 h_v86 h_v87 h_v88 h_v89 h_v90 h_v91
          store_step with Store.apply_rep s53 v81 v92 _ _ hinv53 h64 h_v81 h_v92 (by ns_tac) (by ns_tac) as ⟨v93, s54, hinv54, h_v93⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v76 h_v77 h_v78 h_v79 h_v80 h_v81 h_v82 h_v83 h_v84 h_v85 h_v86 h_v87 h_v88 h_v89 h_v90 h_v91 h_v92
          store_step with ih.eo__24eo_5ftypeof s54 v93 _ hinv54 h64 (hG.rem hrem) h_v93 as ⟨v94, s55, hinv55, h_v94⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v76 h_v77 h_v78 h_v79 h_v80 h_v81 h_v82 h_v83 h_v84 h_v85 h_v86 h_v87 h_v88 h_v89 h_v90 h_v91 h_v92 h_v93
          store_step with ih.eo__24eo_5fnil s55 v80 v94 _ _ hinv55 h64 (hG.rem hrem) h_v80 h_v94 as ⟨v95, s56, hinv56, h_v95⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v76 h_v77 h_v78 h_v79 h_v80 h_v81 h_v82 h_v83 h_v84 h_v85 h_v86 h_v87 h_v88 h_v89 h_v90 h_v91 h_v92 h_v93 h_v94
          store_step with Store.apply_mk_rep s56 v79 v95 _ _ hinv56 h64 h_v79 h_v95 as ⟨v96, s57, hinv57, h_v96⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v76 h_v77 h_v78 h_v79 h_v80 h_v81 h_v82 h_v83 h_v84 h_v85 h_v86 h_v87 h_v88 h_v89 h_v90 h_v91 h_v92 h_v93 h_v94 h_v95
          store_step with Store.apply_mk_rep s57 v67 v96 _ _ hinv57 h64 h_v67 h_v96 as ⟨v97, s58, hinv58, h_v97⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v76 h_v77 h_v78 h_v79 h_v80 h_v81 h_v82 h_v83 h_v84 h_v85 h_v86 h_v87 h_v88 h_v89 h_v90 h_v91 h_v92 h_v93 h_v94 h_v95 h_v96
          ite_done hinv58 hG with (eo_ite_true_rep _ hx_53 h_v97)
        · ite_branch hbv_53
          step as ⟨e_v98, he_v98⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s19 e_v98 (by rw [he_v98]; exact empty_args) hinv19 h64 as ⟨v98, s20, hinv20, h_v98⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52
          step as ⟨e_v99, he_v99⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s20 e_v99 (by rw [he_v99]; exact empty_args) hinv20 h64 as ⟨v99, s21, hinv21, h_v99⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v98
          have h_ite_v106 := (show if_3_eo__24eo_5fprog_5fconcat_5fcsplit s21 a0 v4 ⦃ r s' => s'.Inv ∧ s21.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
            unfold if_3_eo__24eo_5fprog_5fconcat_5fcsplit
            have hrem := (hG.rem hrem)
            have hG := Store.Grows.refl s21
            rcases Store.boolean_value_term h_a0 with ⟨hx_100, hbv_100⟩ | ⟨hx_100, hbv_100⟩ | ⟨hx_100, hbv_100⟩
            · ite_branch hbv_100
              step as ⟨e_v100, he_v100⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s21 e_v100 (by rw [he_v100]; exact empty_args) hinv21 h64 as ⟨v100, s22, hinv22, h_v100⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v98 h_v99
              step as ⟨e_v101, he_v101⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s22 e_v101 (by rw [he_v101]; exact empty_args) hinv22 h64 as ⟨v101, s23, hinv23, h_v101⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v98 h_v99 h_v100
              step as ⟨e_v102, he_v102⟩
              store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s23 e_v102 (by rw [he_v102]; rfl) h_v101 h_v4 hinv23 h64 (hG.rem hrem) (by not_left_tac) (by nil_self_tac) as ⟨v102, s24, hinv24, h_v102⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v98 h_v99 h_v100 h_v101
              step as ⟨e_v103, he_v103⟩
              store_step with Store.builtin_spec_list_rev n ih.eo__24eo_5fis_5flist_5fnil s24 e_v103 (by rw [he_v103]; rfl) h_v100 h_v102 hinv24 h64 (hG.rem hrem) (by not_left_tac) as ⟨v103, s25, hinv25, h_v103⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v98 h_v99 h_v100 h_v101 h_v102
              ite_done hinv25 hG with (eo_ite_true_rep _ hx_100 h_v103)
            · ite_branch hbv_100
              step as ⟨e_v104, he_v104⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s21 e_v104 (by rw [he_v104]; exact empty_args) hinv21 h64 as ⟨v104, s22, hinv22, h_v104⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v98 h_v99
              step as ⟨e_v105, he_v105⟩
              store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s22 e_v105 (by rw [he_v105]; rfl) h_v104 h_v4 hinv22 h64 (hG.rem hrem) (by not_left_tac) (by nil_self_tac) as ⟨v105, s23, hinv23, h_v105⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v98 h_v99 h_v104
              ite_done hinv23 hG with (eo_ite_false_rep _ hx_100 h_v105)
            · ite_branch hbv_100
              ite_stuck hinv21 hG with hx_100)
          store_step with h_ite_v106 as ⟨v106, s22, hinv22, h_v106⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v98 h_v99
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s22 0#u32 (0) (by scalar_tac) hinv22 h64 as ⟨v107, s23, hinv23, h_v107⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v98 h_v99 h_v106
          step as ⟨e_v108, he_v108⟩
          store_step with Store.builtin_spec_list_nth n ih.eo__24eo_5fis_5flist_5fnil s23 e_v108 (by rw [he_v108]; rfl) h_v99 h_v106 h_v107 hinv23 h64 (hG.rem hrem) (by not_left_tac) as ⟨v108, s24, hinv24, h_v108⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v98 h_v99 h_v106 h_v107
          store_step with Store.apply_mk_rep s24 v98 v108 _ _ hinv24 h64 h_v98 h_v108 as ⟨v109, s25, hinv25, h_v109⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v98 h_v99 h_v106 h_v107 h_v108
          step as ⟨e_v110, he_v110⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s25 e_v110 (by rw [he_v110]; exact empty_args) hinv25 h64 as ⟨v110, s26, hinv26, h_v110⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v98 h_v99 h_v106 h_v107 h_v108 h_v109
          step as ⟨e_v111, he_v111⟩
          store_step with CtorSpec.eo__40purify.construct s26 e_v111 (by rw [he_v111]; exact empty_args) hinv26 h64 as ⟨v111, s27, hinv27, h_v111⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v98 h_v99 h_v106 h_v107 h_v108 h_v109 h_v110
          step as ⟨e_v112, he_v112⟩
          store_step with CtorSpec.eo_str_2esubstr.construct s27 e_v112 (by rw [he_v112]; exact empty_args) hinv27 h64 as ⟨v112, s28, hinv28, h_v112⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v98 h_v99 h_v106 h_v107 h_v108 h_v109 h_v110 h_v111
          store_step with Store.apply_rep s28 v112 v24 _ _ hinv28 h64 h_v112 h_v24 (by ns_tac) (by ns_tac) as ⟨v113, s29, hinv29, h_v113⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v98 h_v99 h_v106 h_v107 h_v108 h_v109 h_v110 h_v111 h_v112
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s29 1#u32 (1) (by scalar_tac) hinv29 h64 as ⟨v114, s30, hinv30, h_v114⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v98 h_v99 h_v106 h_v107 h_v108 h_v109 h_v110 h_v111 h_v112 h_v113
          store_step with Store.apply_rep s30 v113 v114 _ _ hinv30 h64 h_v113 h_v114 (by ns_tac) (by ns_tac) as ⟨v115, s31, hinv31, h_v115⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v98 h_v99 h_v106 h_v107 h_v108 h_v109 h_v110 h_v111 h_v112 h_v113 h_v114
          step as ⟨e_v116, he_v116⟩
          store_step with CtorSpec.eo__2d.construct s31 e_v116 (by rw [he_v116]; exact empty_args) hinv31 h64 as ⟨v116, s32, hinv32, h_v116⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v98 h_v99 h_v106 h_v107 h_v108 h_v109 h_v110 h_v111 h_v112 h_v113 h_v114 h_v115
          step as ⟨e_v117, he_v117⟩
          store_step with CtorSpec.eo_str_2elen.construct s32 e_v117 (by rw [he_v117]; exact empty_args) hinv32 h64 as ⟨v117, s33, hinv33, h_v117⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v98 h_v99 h_v106 h_v107 h_v108 h_v109 h_v110 h_v111 h_v112 h_v113 h_v114 h_v115 h_v116
          store_step with Store.apply_rep s33 v117 v24 _ _ hinv33 h64 h_v117 h_v24 (by ns_tac) (by ns_tac) as ⟨v118, s34, hinv34, h_v118⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v98 h_v99 h_v106 h_v107 h_v108 h_v109 h_v110 h_v111 h_v112 h_v113 h_v114 h_v115 h_v116 h_v117
          store_step with Store.apply_rep s34 v116 v118 _ _ hinv34 h64 h_v116 h_v118 (by ns_tac) (by ns_tac) as ⟨v119, s35, hinv35, h_v119⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v98 h_v99 h_v106 h_v107 h_v108 h_v109 h_v110 h_v111 h_v112 h_v113 h_v114 h_v115 h_v116 h_v117 h_v118
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s35 1#u32 (1) (by scalar_tac) hinv35 h64 as ⟨v120, s36, hinv36, h_v120⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v98 h_v99 h_v106 h_v107 h_v108 h_v109 h_v110 h_v111 h_v112 h_v113 h_v114 h_v115 h_v116 h_v117 h_v118 h_v119
          store_step with Store.apply_rep s36 v119 v120 _ _ hinv36 h64 h_v119 h_v120 (by ns_tac) (by ns_tac) as ⟨v121, s37, hinv37, h_v121⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v98 h_v99 h_v106 h_v107 h_v108 h_v109 h_v110 h_v111 h_v112 h_v113 h_v114 h_v115 h_v116 h_v117 h_v118 h_v119 h_v120
          store_step with Store.apply_rep s37 v115 v121 _ _ hinv37 h64 h_v115 h_v121 (by ns_tac) (by ns_tac) as ⟨v122, s38, hinv38, h_v122⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v98 h_v99 h_v106 h_v107 h_v108 h_v109 h_v110 h_v111 h_v112 h_v113 h_v114 h_v115 h_v116 h_v117 h_v118 h_v119 h_v120 h_v121
          store_step with Store.apply_rep s38 v111 v122 _ _ hinv38 h64 h_v111 h_v122 (by ns_tac) (by ns_tac) as ⟨v123, s39, hinv39, h_v123⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v98 h_v99 h_v106 h_v107 h_v108 h_v109 h_v110 h_v111 h_v112 h_v113 h_v114 h_v115 h_v116 h_v117 h_v118 h_v119 h_v120 h_v121 h_v122
          store_step with Store.apply_rep s39 v110 v123 _ _ hinv39 h64 h_v110 h_v123 (by ns_tac) (by ns_tac) as ⟨v124, s40, hinv40, h_v124⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v98 h_v99 h_v106 h_v107 h_v108 h_v109 h_v110 h_v111 h_v112 h_v113 h_v114 h_v115 h_v116 h_v117 h_v118 h_v119 h_v120 h_v121 h_v122 h_v123
          step as ⟨e_v125, he_v125⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s40 e_v125 (by rw [he_v125]; exact empty_args) hinv40 h64 as ⟨v125, s41, hinv41, h_v125⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v98 h_v99 h_v106 h_v107 h_v108 h_v109 h_v110 h_v111 h_v112 h_v113 h_v114 h_v115 h_v116 h_v117 h_v118 h_v119 h_v120 h_v121 h_v122 h_v123 h_v124
          step as ⟨e_v126, he_v126⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s41 e_v126 (by rw [he_v126]; exact empty_args) hinv41 h64 as ⟨v126, s42, hinv42, h_v126⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v98 h_v99 h_v106 h_v107 h_v108 h_v109 h_v110 h_v111 h_v112 h_v113 h_v114 h_v115 h_v116 h_v117 h_v118 h_v119 h_v120 h_v121 h_v122 h_v123 h_v124 h_v125
          have h_ite_v133 := (show if_4_eo__24eo_5fprog_5fconcat_5fcsplit s42 a0 v4 ⦃ r s' => s'.Inv ∧ s42.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
            unfold if_4_eo__24eo_5fprog_5fconcat_5fcsplit
            have hrem := (hG.rem hrem)
            have hG := Store.Grows.refl s42
            rcases Store.boolean_value_term h_a0 with ⟨hx_127, hbv_127⟩ | ⟨hx_127, hbv_127⟩ | ⟨hx_127, hbv_127⟩
            · ite_branch hbv_127
              step as ⟨e_v127, he_v127⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s42 e_v127 (by rw [he_v127]; exact empty_args) hinv42 h64 as ⟨v127, s43, hinv43, h_v127⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v98 h_v99 h_v106 h_v107 h_v108 h_v109 h_v110 h_v111 h_v112 h_v113 h_v114 h_v115 h_v116 h_v117 h_v118 h_v119 h_v120 h_v121 h_v122 h_v123 h_v124 h_v125 h_v126
              step as ⟨e_v128, he_v128⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s43 e_v128 (by rw [he_v128]; exact empty_args) hinv43 h64 as ⟨v128, s44, hinv44, h_v128⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v98 h_v99 h_v106 h_v107 h_v108 h_v109 h_v110 h_v111 h_v112 h_v113 h_v114 h_v115 h_v116 h_v117 h_v118 h_v119 h_v120 h_v121 h_v122 h_v123 h_v124 h_v125 h_v126 h_v127
              step as ⟨e_v129, he_v129⟩
              store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s44 e_v129 (by rw [he_v129]; rfl) h_v128 h_v4 hinv44 h64 (hG.rem hrem) (by not_left_tac) (by nil_self_tac) as ⟨v129, s45, hinv45, h_v129⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v98 h_v99 h_v106 h_v107 h_v108 h_v109 h_v110 h_v111 h_v112 h_v113 h_v114 h_v115 h_v116 h_v117 h_v118 h_v119 h_v120 h_v121 h_v122 h_v123 h_v124 h_v125 h_v126 h_v127 h_v128
              step as ⟨e_v130, he_v130⟩
              store_step with Store.builtin_spec_list_rev n ih.eo__24eo_5fis_5flist_5fnil s45 e_v130 (by rw [he_v130]; rfl) h_v127 h_v129 hinv45 h64 (hG.rem hrem) (by not_left_tac) as ⟨v130, s46, hinv46, h_v130⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v98 h_v99 h_v106 h_v107 h_v108 h_v109 h_v110 h_v111 h_v112 h_v113 h_v114 h_v115 h_v116 h_v117 h_v118 h_v119 h_v120 h_v121 h_v122 h_v123 h_v124 h_v125 h_v126 h_v127 h_v128 h_v129
              ite_done hinv46 hG with (eo_ite_true_rep _ hx_127 h_v130)
            · ite_branch hbv_127
              step as ⟨e_v131, he_v131⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s42 e_v131 (by rw [he_v131]; exact empty_args) hinv42 h64 as ⟨v131, s43, hinv43, h_v131⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v98 h_v99 h_v106 h_v107 h_v108 h_v109 h_v110 h_v111 h_v112 h_v113 h_v114 h_v115 h_v116 h_v117 h_v118 h_v119 h_v120 h_v121 h_v122 h_v123 h_v124 h_v125 h_v126
              step as ⟨e_v132, he_v132⟩
              store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s43 e_v132 (by rw [he_v132]; rfl) h_v131 h_v4 hinv43 h64 (hG.rem hrem) (by not_left_tac) (by nil_self_tac) as ⟨v132, s44, hinv44, h_v132⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v98 h_v99 h_v106 h_v107 h_v108 h_v109 h_v110 h_v111 h_v112 h_v113 h_v114 h_v115 h_v116 h_v117 h_v118 h_v119 h_v120 h_v121 h_v122 h_v123 h_v124 h_v125 h_v126 h_v131
              ite_done hinv44 hG with (eo_ite_false_rep _ hx_127 h_v132)
            · ite_branch hbv_127
              ite_stuck hinv42 hG with hx_127)
          store_step with h_ite_v133 as ⟨v133, s43, hinv43, h_v133⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v98 h_v99 h_v106 h_v107 h_v108 h_v109 h_v110 h_v111 h_v112 h_v113 h_v114 h_v115 h_v116 h_v117 h_v118 h_v119 h_v120 h_v121 h_v122 h_v123 h_v124 h_v125 h_v126
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s43 0#u32 (0) (by scalar_tac) hinv43 h64 as ⟨v134, s44, hinv44, h_v134⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v98 h_v99 h_v106 h_v107 h_v108 h_v109 h_v110 h_v111 h_v112 h_v113 h_v114 h_v115 h_v116 h_v117 h_v118 h_v119 h_v120 h_v121 h_v122 h_v123 h_v124 h_v125 h_v126 h_v133
          step as ⟨e_v135, he_v135⟩
          store_step with Store.builtin_spec_list_nth n ih.eo__24eo_5fis_5flist_5fnil s44 e_v135 (by rw [he_v135]; rfl) h_v126 h_v133 h_v134 hinv44 h64 (hG.rem hrem) (by not_left_tac) as ⟨v135, s45, hinv45, h_v135⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v98 h_v99 h_v106 h_v107 h_v108 h_v109 h_v110 h_v111 h_v112 h_v113 h_v114 h_v115 h_v116 h_v117 h_v118 h_v119 h_v120 h_v121 h_v122 h_v123 h_v124 h_v125 h_v126 h_v133 h_v134
          store_step with ih.eo__24eo_5ftypeof s45 v135 _ hinv45 h64 (hG.rem hrem) h_v135 as ⟨v136, s46, hinv46, h_v136⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v98 h_v99 h_v106 h_v107 h_v108 h_v109 h_v110 h_v111 h_v112 h_v113 h_v114 h_v115 h_v116 h_v117 h_v118 h_v119 h_v120 h_v121 h_v122 h_v123 h_v124 h_v125 h_v126 h_v133 h_v134 h_v135
          store_step with ih.eo__24eo_5fnil s46 v125 v136 _ _ hinv46 h64 (hG.rem hrem) h_v125 h_v136 as ⟨v137, s47, hinv47, h_v137⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v98 h_v99 h_v106 h_v107 h_v108 h_v109 h_v110 h_v111 h_v112 h_v113 h_v114 h_v115 h_v116 h_v117 h_v118 h_v119 h_v120 h_v121 h_v122 h_v123 h_v124 h_v125 h_v126 h_v133 h_v134 h_v135 h_v136
          store_step with Store.apply_mk_rep s47 v124 v137 _ _ hinv47 h64 h_v124 h_v137 as ⟨v138, s48, hinv48, h_v138⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v98 h_v99 h_v106 h_v107 h_v108 h_v109 h_v110 h_v111 h_v112 h_v113 h_v114 h_v115 h_v116 h_v117 h_v118 h_v119 h_v120 h_v121 h_v122 h_v123 h_v124 h_v125 h_v126 h_v133 h_v134 h_v135 h_v136 h_v137
          store_step with Store.apply_mk_rep s48 v109 v138 _ _ hinv48 h64 h_v109 h_v138 as ⟨v139, s49, hinv49, h_v139⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v98 h_v99 h_v106 h_v107 h_v108 h_v109 h_v110 h_v111 h_v112 h_v113 h_v114 h_v115 h_v116 h_v117 h_v118 h_v119 h_v120 h_v121 h_v122 h_v123 h_v124 h_v125 h_v126 h_v133 h_v134 h_v135 h_v136 h_v137 h_v138
          ite_done hinv49 hG with (eo_ite_false_rep _ hx_53 h_v139)
        · ite_branch hbv_53
          ite_stuck hinv19 hG with hx_53)
      store_step with h_ite_v140 as ⟨v140, s20, hinv20, h_v140⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52
      store_step with Store.apply_mk_rep s20 v52 v140 _ _ hinv20 h64 h_v52 h_v140 as ⟨v141, s21, hinv21, h_v141⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v140
      req_done hinv21 hG with h_v141 using hq_v49)
    store_step with h_req_v142 as ⟨v142, s22, hinv22, h_v142⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36 h_v37 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50
    req_done hinv22 hG with h_v142 using hq_v36)
  store_step with h_req_v143 as ⟨v143, s23, hinv23, h_v143⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v23 h_v24 h_v25 h_v26 h_v27 h_v34 h_v35 h_v36
  case_done hinv23 hG with h_v143 in EoCases.__eo_prog_concat_csplit.case_0 using hn_a0 hn_v3 hn_v4 hn_v6 hn_v7 hn_v12 hn_v13 hn_v16 hn_v17 hn_v19 hn_v20 hn_v23 hn_v24

set_option maxHeartbeats 6000000 in
/-- logos's `__eo_prog_concat_csplit` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fconcat_5fcsplit.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __eo_prog_concat_csplit x_a0 x_a1 x_a2 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_concat_csplit.case_0 x_a0 x_a1 x_a2] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_concat_csplit
  unfold EoCases.__eo_prog_concat_csplit.case_0
  logos_eq

set_option maxHeartbeats 6000000 in
theorem body_eo__24eo_5fprog_5fconcat_5fcsplit_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24eo_5fprog_5fconcat_5fcsplit s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_concat_csplit x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fconcat_5fcsplit.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24eo_5fprog_5fconcat_5fcsplit
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fconcat_5fcsplit_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_concat_csplit.case_0

set_option maxHeartbeats 6000000 in
theorem eo__24eo_5fprog_5fconcat_5fcsplit_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fconcat_5fcsplit.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24eo_5fprog_5fconcat_5fcsplit
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fconcat_5fcsplit s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__eo_prog_concat_csplit x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fconcat_5fcsplit_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

end pathos_compiled_checker
