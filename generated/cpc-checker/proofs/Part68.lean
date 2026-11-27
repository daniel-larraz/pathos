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

set_option maxHeartbeats 5000000 in
theorem case_0_eo__24eo_5fprog_5fconcat_5feq_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fconcat_5feq s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_concat_eq.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_concat_eq.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fconcat_5feq
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a1 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_concat_eq.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_concat_eq.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_concat_eq.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_v4 h_v6 h_v7 dropping h_a1 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_concat_eq.case_0
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__3d.construct s1 e_v9 (by rw [he_v9]; exact empty_args) hinv1 h64 as ⟨v9, s2, hinv2, h_v9⟩ growing hG carrying h_a0 h_v4 h_v7 dropping h_v6 h_v8 he_v9 hinv1 e_v9 s1 v6 v8
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s2 e_v10 (by rw [he_v10]; exact empty_args) hinv2 h64 as ⟨v10, s3, hinv3, h_v10⟩ growing hG carrying h_a0 h_v4 h_v7 h_v9 dropping he_v10 hinv2 e_v10 s2
  have h_ite_v45 := (show if_4_eo__24eo_5fprog_5fconcat_5feq s3 a0 a0 v7 v4 ⦃ r s' => s'.Inv ∧ s3.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_4_eo__24eo_5fprog_5fconcat_5feq
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s3
    rcases Store.boolean_value_term h_a0 with ⟨hx_11, hbv_11⟩ | ⟨hx_11, hbv_11⟩ | ⟨hx_11, hbv_11⟩
    · ite_branch hbv_11
      step as ⟨e_v11, he_v11⟩
      store_step with CtorSpec.eo_str_2e_2b_2b.construct s3 e_v11 (by rw [he_v11]; exact empty_args) hinv3 h64 as ⟨v11, s4, hinv4, h_v11⟩ growing hG carrying h_a0 h_v4 h_v7 h_v9 h_v10 dropping he_v11 e_v11
      have h_ite_v18 := (show if_0_eo__24eo_5fprog_5fconcat_5feq s4 a0 v7 ⦃ r s' => s'.Inv ∧ s4.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_0_eo__24eo_5fprog_5fconcat_5feq
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s4
        rcases Store.boolean_value_term h_a0 with ⟨hx_12, hbv_12⟩ | ⟨hx_12, hbv_12⟩ | ⟨hx_12, hbv_12⟩
        · ite_branch hbv_12
          step as ⟨e_v12, he_v12⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s4 e_v12 (by rw [he_v12]; exact empty_args) hinv4 h64 as ⟨v12, s5, hinv5, h_v12⟩ growing hG carrying h_a0 h_v4 h_v7 h_v9 h_v10 h_v11 dropping he_v12 e_v12
          step as ⟨e_v13, he_v13⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s5 e_v13 (by rw [he_v13]; exact empty_args) hinv5 h64 as ⟨v13, s6, hinv6, h_v13⟩ growing hG carrying h_a0 h_v4 h_v7 h_v9 h_v10 h_v11 h_v12 dropping he_v13 e_v13
          step as ⟨e_v14, he_v14⟩
          store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s6 e_v14 (by rw [he_v14]; rfl) h_v13 h_v7 hinv6 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v14, s7, hinv7, h_v14⟩ growing hG carrying h_a0 h_v4 h_v7 h_v9 h_v10 h_v11 h_v12 dropping h_v13 he_v14 e_v14 v13
          step as ⟨e_v15, he_v15⟩
          store_step with Store.builtin_spec_list_rev n ih.eo__24eo_5fis_5flist_5fnil s7 e_v15 (by rw [he_v15]; rfl) h_v12 h_v14 hinv7 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v15, s8, hinv8, h_v15⟩ growing hG carrying h_a0 h_v4 h_v7 h_v9 h_v10 h_v11 dropping h_v12 h_v14 he_v15 e_v15 v12 v14
          ite_done hinv8 hG with (eo_ite_true_rep _ hx_12 h_v15)
        · ite_branch hbv_12
          step as ⟨e_v16, he_v16⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s4 e_v16 (by rw [he_v16]; exact empty_args) hinv4 h64 as ⟨v16, s5, hinv5, h_v16⟩ growing hG carrying h_a0 h_v4 h_v7 h_v9 h_v10 h_v11 dropping he_v16 e_v16
          step as ⟨e_v17, he_v17⟩
          store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s5 e_v17 (by rw [he_v17]; rfl) h_v16 h_v7 hinv5 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v17, s6, hinv6, h_v17⟩ growing hG carrying h_a0 h_v4 h_v7 h_v9 h_v10 h_v11 dropping h_v16 he_v17 e_v17 v16
          ite_done hinv6 hG with (eo_ite_false_rep _ hx_12 h_v17)
        · ite_branch hbv_12
          ite_stuck hinv4 hG with hx_12)
      store_step with h_ite_v18 as ⟨v18, s5, hinv5, h_v18⟩ growing hG carrying h_a0 h_v4 h_v7 h_v9 h_v10 h_v11 dropping h_ite_v18
      have h_ite_v25 := (show if_1_eo__24eo_5fprog_5fconcat_5feq s5 a0 v4 ⦃ r s' => s'.Inv ∧ s5.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_1_eo__24eo_5fprog_5fconcat_5feq
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s5
        rcases Store.boolean_value_term h_a0 with ⟨hx_19, hbv_19⟩ | ⟨hx_19, hbv_19⟩ | ⟨hx_19, hbv_19⟩
        · ite_branch hbv_19
          step as ⟨e_v19, he_v19⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s5 e_v19 (by rw [he_v19]; exact empty_args) hinv5 h64 as ⟨v19, s6, hinv6, h_v19⟩ growing hG carrying h_a0 h_v4 h_v7 h_v9 h_v10 h_v11 h_v18 dropping he_v19 e_v19
          step as ⟨e_v20, he_v20⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s6 e_v20 (by rw [he_v20]; exact empty_args) hinv6 h64 as ⟨v20, s7, hinv7, h_v20⟩ growing hG carrying h_a0 h_v4 h_v7 h_v9 h_v10 h_v11 h_v18 h_v19 dropping he_v20 e_v20
          step as ⟨e_v21, he_v21⟩
          store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s7 e_v21 (by rw [he_v21]; rfl) h_v20 h_v4 hinv7 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v21, s8, hinv8, h_v21⟩ growing hG carrying h_a0 h_v4 h_v7 h_v9 h_v10 h_v11 h_v18 h_v19 dropping h_v20 he_v21 e_v21 v20
          step as ⟨e_v22, he_v22⟩
          store_step with Store.builtin_spec_list_rev n ih.eo__24eo_5fis_5flist_5fnil s8 e_v22 (by rw [he_v22]; rfl) h_v19 h_v21 hinv8 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v22, s9, hinv9, h_v22⟩ growing hG carrying h_a0 h_v4 h_v7 h_v9 h_v10 h_v11 h_v18 dropping h_v19 h_v21 he_v22 e_v22 v19 v21
          ite_done hinv9 hG with (eo_ite_true_rep _ hx_19 h_v22)
        · ite_branch hbv_19
          step as ⟨e_v23, he_v23⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s5 e_v23 (by rw [he_v23]; exact empty_args) hinv5 h64 as ⟨v23, s6, hinv6, h_v23⟩ growing hG carrying h_a0 h_v4 h_v7 h_v9 h_v10 h_v11 h_v18 dropping he_v23 e_v23
          step as ⟨e_v24, he_v24⟩
          store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s6 e_v24 (by rw [he_v24]; rfl) h_v23 h_v4 hinv6 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v24, s7, hinv7, h_v24⟩ growing hG carrying h_a0 h_v4 h_v7 h_v9 h_v10 h_v11 h_v18 dropping h_v23 he_v24 e_v24 v23
          ite_done hinv7 hG with (eo_ite_false_rep _ hx_19 h_v24)
        · ite_branch hbv_19
          ite_stuck hinv5 hG with hx_19)
      store_step with h_ite_v25 as ⟨v25, s6, hinv6, h_v25⟩ growing hG carrying h_a0 h_v4 h_v7 h_v9 h_v10 h_v11 h_v18 dropping h_ite_v25
      store_step with ih.eo__24str_5fstrip_5fprefix s6 v18 v25 _ _ hinv6 h64 (hG.rem hrem) h_v18 h_v25 as ⟨v26, s7, hinv7, h_v26⟩ growing hG carrying h_a0 h_v4 h_v7 h_v9 h_v10 h_v11 dropping h_v18 h_v25 v18 v25
      store_step with ih.eo__24pair_5ffirst s7 v26 _ hinv7 h64 (hG.rem hrem) h_v26 as ⟨v27, s8, hinv8, h_v27⟩ growing hG carrying h_a0 h_v4 h_v7 h_v9 h_v10 h_v11 dropping h_v26 v26
      step as ⟨e_v28, he_v28⟩
      store_step with Store.builtin_spec_list_rev n ih.eo__24eo_5fis_5flist_5fnil s8 e_v28 (by rw [he_v28]; rfl) h_v11 h_v27 hinv8 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v28, s9, hinv9, h_v28⟩ growing hG carrying h_a0 h_v4 h_v7 h_v9 h_v10 dropping h_v11 h_v27 he_v28 e_v28 v11 v27
      ite_done hinv9 hG with (eo_ite_true_rep _ hx_11 h_v28)
    · ite_branch hbv_11
      have h_ite_v35 := (show if_2_eo__24eo_5fprog_5fconcat_5feq s3 a0 v7 ⦃ r s' => s'.Inv ∧ s3.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_2_eo__24eo_5fprog_5fconcat_5feq
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s3
        rcases Store.boolean_value_term h_a0 with ⟨hx_29, hbv_29⟩ | ⟨hx_29, hbv_29⟩ | ⟨hx_29, hbv_29⟩
        · ite_branch hbv_29
          step as ⟨e_v29, he_v29⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s3 e_v29 (by rw [he_v29]; exact empty_args) hinv3 h64 as ⟨v29, s4, hinv4, h_v29⟩ growing hG carrying h_a0 h_v4 h_v7 h_v9 h_v10 dropping he_v29 e_v29
          step as ⟨e_v30, he_v30⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s4 e_v30 (by rw [he_v30]; exact empty_args) hinv4 h64 as ⟨v30, s5, hinv5, h_v30⟩ growing hG carrying h_a0 h_v4 h_v7 h_v9 h_v10 h_v29 dropping he_v30 e_v30
          step as ⟨e_v31, he_v31⟩
          store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s5 e_v31 (by rw [he_v31]; rfl) h_v30 h_v7 hinv5 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v31, s6, hinv6, h_v31⟩ growing hG carrying h_a0 h_v4 h_v7 h_v9 h_v10 h_v29 dropping h_v30 he_v31 e_v31 v30
          step as ⟨e_v32, he_v32⟩
          store_step with Store.builtin_spec_list_rev n ih.eo__24eo_5fis_5flist_5fnil s6 e_v32 (by rw [he_v32]; rfl) h_v29 h_v31 hinv6 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v32, s7, hinv7, h_v32⟩ growing hG carrying h_a0 h_v4 h_v7 h_v9 h_v10 dropping h_v29 h_v31 he_v32 e_v32 v29 v31
          ite_done hinv7 hG with (eo_ite_true_rep _ hx_29 h_v32)
        · ite_branch hbv_29
          step as ⟨e_v33, he_v33⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s3 e_v33 (by rw [he_v33]; exact empty_args) hinv3 h64 as ⟨v33, s4, hinv4, h_v33⟩ growing hG carrying h_a0 h_v4 h_v7 h_v9 h_v10 dropping he_v33 e_v33
          step as ⟨e_v34, he_v34⟩
          store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s4 e_v34 (by rw [he_v34]; rfl) h_v33 h_v7 hinv4 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v34, s5, hinv5, h_v34⟩ growing hG carrying h_a0 h_v4 h_v7 h_v9 h_v10 dropping h_v33 he_v34 e_v34 v33
          ite_done hinv5 hG with (eo_ite_false_rep _ hx_29 h_v34)
        · ite_branch hbv_29
          ite_stuck hinv3 hG with hx_29)
      store_step with h_ite_v35 as ⟨v35, s4, hinv4, h_v35⟩ growing hG carrying h_a0 h_v4 h_v7 h_v9 h_v10 dropping h_ite_v35
      have h_ite_v42 := (show if_3_eo__24eo_5fprog_5fconcat_5feq s4 a0 v4 ⦃ r s' => s'.Inv ∧ s4.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_3_eo__24eo_5fprog_5fconcat_5feq
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s4
        rcases Store.boolean_value_term h_a0 with ⟨hx_36, hbv_36⟩ | ⟨hx_36, hbv_36⟩ | ⟨hx_36, hbv_36⟩
        · ite_branch hbv_36
          step as ⟨e_v36, he_v36⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s4 e_v36 (by rw [he_v36]; exact empty_args) hinv4 h64 as ⟨v36, s5, hinv5, h_v36⟩ growing hG carrying h_a0 h_v4 h_v7 h_v9 h_v10 h_v35 dropping he_v36 e_v36
          step as ⟨e_v37, he_v37⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s5 e_v37 (by rw [he_v37]; exact empty_args) hinv5 h64 as ⟨v37, s6, hinv6, h_v37⟩ growing hG carrying h_a0 h_v4 h_v7 h_v9 h_v10 h_v35 h_v36 dropping he_v37 e_v37
          step as ⟨e_v38, he_v38⟩
          store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s6 e_v38 (by rw [he_v38]; rfl) h_v37 h_v4 hinv6 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v38, s7, hinv7, h_v38⟩ growing hG carrying h_a0 h_v4 h_v7 h_v9 h_v10 h_v35 h_v36 dropping h_v37 he_v38 e_v38 v37
          step as ⟨e_v39, he_v39⟩
          store_step with Store.builtin_spec_list_rev n ih.eo__24eo_5fis_5flist_5fnil s7 e_v39 (by rw [he_v39]; rfl) h_v36 h_v38 hinv7 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v39, s8, hinv8, h_v39⟩ growing hG carrying h_a0 h_v4 h_v7 h_v9 h_v10 h_v35 dropping h_v36 h_v38 he_v39 e_v39 v36 v38
          ite_done hinv8 hG with (eo_ite_true_rep _ hx_36 h_v39)
        · ite_branch hbv_36
          step as ⟨e_v40, he_v40⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s4 e_v40 (by rw [he_v40]; exact empty_args) hinv4 h64 as ⟨v40, s5, hinv5, h_v40⟩ growing hG carrying h_a0 h_v4 h_v7 h_v9 h_v10 h_v35 dropping he_v40 e_v40
          step as ⟨e_v41, he_v41⟩
          store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s5 e_v41 (by rw [he_v41]; rfl) h_v40 h_v4 hinv5 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v41, s6, hinv6, h_v41⟩ growing hG carrying h_a0 h_v4 h_v7 h_v9 h_v10 h_v35 dropping h_v40 he_v41 e_v41 v40
          ite_done hinv6 hG with (eo_ite_false_rep _ hx_36 h_v41)
        · ite_branch hbv_36
          ite_stuck hinv4 hG with hx_36)
      store_step with h_ite_v42 as ⟨v42, s5, hinv5, h_v42⟩ growing hG carrying h_a0 h_v4 h_v7 h_v9 h_v10 h_v35 dropping h_ite_v42
      store_step with ih.eo__24str_5fstrip_5fprefix s5 v35 v42 _ _ hinv5 h64 (hG.rem hrem) h_v35 h_v42 as ⟨v43, s6, hinv6, h_v43⟩ growing hG carrying h_a0 h_v4 h_v7 h_v9 h_v10 dropping h_v35 h_v42 v35 v42
      store_step with ih.eo__24pair_5ffirst s6 v43 _ hinv6 h64 (hG.rem hrem) h_v43 as ⟨v44, s7, hinv7, h_v44⟩ growing hG carrying h_a0 h_v4 h_v7 h_v9 h_v10 dropping h_v43 v43
      ite_done hinv7 hG with (eo_ite_false_rep _ hx_11 h_v44)
    · ite_branch hbv_11
      ite_stuck hinv3 hG with hx_11)
  store_step with h_ite_v45 as ⟨v45, s4, hinv4, h_v45⟩ growing hG carrying h_a0 h_v4 h_v7 h_v9 h_v10 dropping h_ite_v45 hinv3 s3
  step as ⟨e_v46, he_v46⟩
  store_step with Store.builtin_spec_list_singleton_elim n ih.eo__24eo_5fis_5flist_5fnil s4 e_v46 (by rw [he_v46]; rfl) h_v10 h_v45 hinv4 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_apply_eo_str_2e_2b_2b as ⟨v46, s5, hinv5, h_v46⟩ growing hG carrying h_a0 h_v4 h_v7 h_v9 dropping h_v10 h_v45 he_v46 hinv4 e_v46 s4 v10 v45
  store_step with Store.apply_mk_rep s5 v9 v46 _ _ hinv5 h64 h_v9 h_v46 as ⟨v47, s6, hinv6, h_v47⟩ growing hG carrying h_a0 h_v4 h_v7 dropping h_v46 h_v9 hinv5 s5 v46 v9
  step as ⟨e_v48, he_v48⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s6 e_v48 (by rw [he_v48]; exact empty_args) hinv6 h64 as ⟨v48, s7, hinv7, h_v48⟩ growing hG carrying h_a0 h_v4 h_v7 h_v47 dropping he_v48 hinv6 e_v48 s6
  have h_ite_v83 := (show if_9_eo__24eo_5fprog_5fconcat_5feq s7 a0 a0 v7 v4 ⦃ r s' => s'.Inv ∧ s7.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_9_eo__24eo_5fprog_5fconcat_5feq
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s7
    rcases Store.boolean_value_term h_a0 with ⟨hx_49, hbv_49⟩ | ⟨hx_49, hbv_49⟩ | ⟨hx_49, hbv_49⟩
    · ite_branch hbv_49
      step as ⟨e_v49, he_v49⟩
      store_step with CtorSpec.eo_str_2e_2b_2b.construct s7 e_v49 (by rw [he_v49]; exact empty_args) hinv7 h64 as ⟨v49, s8, hinv8, h_v49⟩ growing hG carrying h_a0 h_v4 h_v7 h_v47 h_v48 dropping he_v49 e_v49
      have h_ite_v56 := (show if_5_eo__24eo_5fprog_5fconcat_5feq s8 a0 v7 ⦃ r s' => s'.Inv ∧ s8.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_5_eo__24eo_5fprog_5fconcat_5feq
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s8
        rcases Store.boolean_value_term h_a0 with ⟨hx_50, hbv_50⟩ | ⟨hx_50, hbv_50⟩ | ⟨hx_50, hbv_50⟩
        · ite_branch hbv_50
          step as ⟨e_v50, he_v50⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s8 e_v50 (by rw [he_v50]; exact empty_args) hinv8 h64 as ⟨v50, s9, hinv9, h_v50⟩ growing hG carrying h_a0 h_v4 h_v7 h_v47 h_v48 h_v49 dropping he_v50 e_v50
          step as ⟨e_v51, he_v51⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s9 e_v51 (by rw [he_v51]; exact empty_args) hinv9 h64 as ⟨v51, s10, hinv10, h_v51⟩ growing hG carrying h_a0 h_v4 h_v7 h_v47 h_v48 h_v49 h_v50 dropping he_v51 e_v51
          step as ⟨e_v52, he_v52⟩
          store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s10 e_v52 (by rw [he_v52]; rfl) h_v51 h_v7 hinv10 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v52, s11, hinv11, h_v52⟩ growing hG carrying h_a0 h_v4 h_v7 h_v47 h_v48 h_v49 h_v50 dropping h_v51 he_v52 e_v52 v51
          step as ⟨e_v53, he_v53⟩
          store_step with Store.builtin_spec_list_rev n ih.eo__24eo_5fis_5flist_5fnil s11 e_v53 (by rw [he_v53]; rfl) h_v50 h_v52 hinv11 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v53, s12, hinv12, h_v53⟩ growing hG carrying h_a0 h_v4 h_v7 h_v47 h_v48 h_v49 dropping h_v50 h_v52 he_v53 e_v53 v50 v52
          ite_done hinv12 hG with (eo_ite_true_rep _ hx_50 h_v53)
        · ite_branch hbv_50
          step as ⟨e_v54, he_v54⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s8 e_v54 (by rw [he_v54]; exact empty_args) hinv8 h64 as ⟨v54, s9, hinv9, h_v54⟩ growing hG carrying h_a0 h_v4 h_v7 h_v47 h_v48 h_v49 dropping he_v54 e_v54
          step as ⟨e_v55, he_v55⟩
          store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s9 e_v55 (by rw [he_v55]; rfl) h_v54 h_v7 hinv9 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v55, s10, hinv10, h_v55⟩ growing hG carrying h_a0 h_v4 h_v7 h_v47 h_v48 h_v49 dropping h_v54 he_v55 e_v55 v54
          ite_done hinv10 hG with (eo_ite_false_rep _ hx_50 h_v55)
        · ite_branch hbv_50
          ite_stuck hinv8 hG with hx_50)
      store_step with h_ite_v56 as ⟨v56, s9, hinv9, h_v56⟩ growing hG carrying h_a0 h_v4 h_v7 h_v47 h_v48 h_v49 dropping h_ite_v56
      have h_ite_v63 := (show if_6_eo__24eo_5fprog_5fconcat_5feq s9 a0 v4 ⦃ r s' => s'.Inv ∧ s9.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_6_eo__24eo_5fprog_5fconcat_5feq
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s9
        rcases Store.boolean_value_term h_a0 with ⟨hx_57, hbv_57⟩ | ⟨hx_57, hbv_57⟩ | ⟨hx_57, hbv_57⟩
        · ite_branch hbv_57
          step as ⟨e_v57, he_v57⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s9 e_v57 (by rw [he_v57]; exact empty_args) hinv9 h64 as ⟨v57, s10, hinv10, h_v57⟩ growing hG carrying h_a0 h_v4 h_v7 h_v47 h_v48 h_v49 h_v56 dropping he_v57 e_v57
          step as ⟨e_v58, he_v58⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s10 e_v58 (by rw [he_v58]; exact empty_args) hinv10 h64 as ⟨v58, s11, hinv11, h_v58⟩ growing hG carrying h_a0 h_v4 h_v7 h_v47 h_v48 h_v49 h_v56 h_v57 dropping he_v58 e_v58
          step as ⟨e_v59, he_v59⟩
          store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s11 e_v59 (by rw [he_v59]; rfl) h_v58 h_v4 hinv11 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v59, s12, hinv12, h_v59⟩ growing hG carrying h_a0 h_v4 h_v7 h_v47 h_v48 h_v49 h_v56 h_v57 dropping h_v58 he_v59 e_v59 v58
          step as ⟨e_v60, he_v60⟩
          store_step with Store.builtin_spec_list_rev n ih.eo__24eo_5fis_5flist_5fnil s12 e_v60 (by rw [he_v60]; rfl) h_v57 h_v59 hinv12 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v60, s13, hinv13, h_v60⟩ growing hG carrying h_a0 h_v4 h_v7 h_v47 h_v48 h_v49 h_v56 dropping h_v57 h_v59 he_v60 e_v60 v57 v59
          ite_done hinv13 hG with (eo_ite_true_rep _ hx_57 h_v60)
        · ite_branch hbv_57
          step as ⟨e_v61, he_v61⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s9 e_v61 (by rw [he_v61]; exact empty_args) hinv9 h64 as ⟨v61, s10, hinv10, h_v61⟩ growing hG carrying h_a0 h_v4 h_v7 h_v47 h_v48 h_v49 h_v56 dropping he_v61 e_v61
          step as ⟨e_v62, he_v62⟩
          store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s10 e_v62 (by rw [he_v62]; rfl) h_v61 h_v4 hinv10 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v62, s11, hinv11, h_v62⟩ growing hG carrying h_a0 h_v4 h_v7 h_v47 h_v48 h_v49 h_v56 dropping h_v61 he_v62 e_v62 v61
          ite_done hinv11 hG with (eo_ite_false_rep _ hx_57 h_v62)
        · ite_branch hbv_57
          ite_stuck hinv9 hG with hx_57)
      store_step with h_ite_v63 as ⟨v63, s10, hinv10, h_v63⟩ growing hG carrying h_a0 h_v4 h_v7 h_v47 h_v48 h_v49 h_v56 dropping h_ite_v63
      store_step with ih.eo__24str_5fstrip_5fprefix s10 v56 v63 _ _ hinv10 h64 (hG.rem hrem) h_v56 h_v63 as ⟨v64, s11, hinv11, h_v64⟩ growing hG carrying h_a0 h_v4 h_v7 h_v47 h_v48 h_v49 dropping h_v56 h_v63 v56 v63
      store_step with ih.eo__24pair_5fsecond s11 v64 _ hinv11 h64 (hG.rem hrem) h_v64 as ⟨v65, s12, hinv12, h_v65⟩ growing hG carrying h_a0 h_v4 h_v7 h_v47 h_v48 h_v49 dropping h_v64 v64
      step as ⟨e_v66, he_v66⟩
      store_step with Store.builtin_spec_list_rev n ih.eo__24eo_5fis_5flist_5fnil s12 e_v66 (by rw [he_v66]; rfl) h_v49 h_v65 hinv12 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v66, s13, hinv13, h_v66⟩ growing hG carrying h_a0 h_v4 h_v7 h_v47 h_v48 dropping h_v49 h_v65 he_v66 e_v66 v49 v65
      ite_done hinv13 hG with (eo_ite_true_rep _ hx_49 h_v66)
    · ite_branch hbv_49
      have h_ite_v73 := (show if_7_eo__24eo_5fprog_5fconcat_5feq s7 a0 v7 ⦃ r s' => s'.Inv ∧ s7.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_7_eo__24eo_5fprog_5fconcat_5feq
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s7
        rcases Store.boolean_value_term h_a0 with ⟨hx_67, hbv_67⟩ | ⟨hx_67, hbv_67⟩ | ⟨hx_67, hbv_67⟩
        · ite_branch hbv_67
          step as ⟨e_v67, he_v67⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s7 e_v67 (by rw [he_v67]; exact empty_args) hinv7 h64 as ⟨v67, s8, hinv8, h_v67⟩ growing hG carrying h_a0 h_v4 h_v7 h_v47 h_v48 dropping he_v67 e_v67
          step as ⟨e_v68, he_v68⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s8 e_v68 (by rw [he_v68]; exact empty_args) hinv8 h64 as ⟨v68, s9, hinv9, h_v68⟩ growing hG carrying h_a0 h_v4 h_v7 h_v47 h_v48 h_v67 dropping he_v68 e_v68
          step as ⟨e_v69, he_v69⟩
          store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s9 e_v69 (by rw [he_v69]; rfl) h_v68 h_v7 hinv9 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v69, s10, hinv10, h_v69⟩ growing hG carrying h_a0 h_v4 h_v7 h_v47 h_v48 h_v67 dropping h_v68 he_v69 e_v69 v68
          step as ⟨e_v70, he_v70⟩
          store_step with Store.builtin_spec_list_rev n ih.eo__24eo_5fis_5flist_5fnil s10 e_v70 (by rw [he_v70]; rfl) h_v67 h_v69 hinv10 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v70, s11, hinv11, h_v70⟩ growing hG carrying h_a0 h_v4 h_v7 h_v47 h_v48 dropping h_v67 h_v69 he_v70 e_v70 v67 v69
          ite_done hinv11 hG with (eo_ite_true_rep _ hx_67 h_v70)
        · ite_branch hbv_67
          step as ⟨e_v71, he_v71⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s7 e_v71 (by rw [he_v71]; exact empty_args) hinv7 h64 as ⟨v71, s8, hinv8, h_v71⟩ growing hG carrying h_a0 h_v4 h_v7 h_v47 h_v48 dropping he_v71 e_v71
          step as ⟨e_v72, he_v72⟩
          store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s8 e_v72 (by rw [he_v72]; rfl) h_v71 h_v7 hinv8 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v72, s9, hinv9, h_v72⟩ growing hG carrying h_a0 h_v4 h_v47 h_v48 dropping h_v7 h_v71 he_v72 e_v72 v7 v71
          ite_done hinv9 hG with (eo_ite_false_rep _ hx_67 h_v72)
        · ite_branch hbv_67
          ite_stuck hinv7 hG with hx_67)
      store_step with h_ite_v73 as ⟨v73, s8, hinv8, h_v73⟩ growing hG carrying h_a0 h_v4 h_v47 h_v48 dropping h_ite_v73 h_v7 v7
      have h_ite_v80 := (show if_8_eo__24eo_5fprog_5fconcat_5feq s8 a0 v4 ⦃ r s' => s'.Inv ∧ s8.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_8_eo__24eo_5fprog_5fconcat_5feq
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s8
        rcases Store.boolean_value_term h_a0 with ⟨hx_74, hbv_74⟩ | ⟨hx_74, hbv_74⟩ | ⟨hx_74, hbv_74⟩
        · ite_branch hbv_74
          step as ⟨e_v74, he_v74⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s8 e_v74 (by rw [he_v74]; exact empty_args) hinv8 h64 as ⟨v74, s9, hinv9, h_v74⟩ growing hG carrying h_v4 h_v47 h_v48 h_v73 dropping h_a0 he_v74 e_v74
          step as ⟨e_v75, he_v75⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s9 e_v75 (by rw [he_v75]; exact empty_args) hinv9 h64 as ⟨v75, s10, hinv10, h_v75⟩ growing hG carrying h_v4 h_v47 h_v48 h_v73 h_v74 dropping he_v75 e_v75
          step as ⟨e_v76, he_v76⟩
          store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s10 e_v76 (by rw [he_v76]; rfl) h_v75 h_v4 hinv10 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v76, s11, hinv11, h_v76⟩ growing hG carrying h_v4 h_v47 h_v48 h_v73 h_v74 dropping h_v75 he_v76 e_v76 v75
          step as ⟨e_v77, he_v77⟩
          store_step with Store.builtin_spec_list_rev n ih.eo__24eo_5fis_5flist_5fnil s11 e_v77 (by rw [he_v77]; rfl) h_v74 h_v76 hinv11 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v77, s12, hinv12, h_v77⟩ growing hG carrying h_v4 h_v47 h_v48 h_v73 dropping h_v74 h_v76 he_v77 e_v77 v74 v76
          ite_done hinv12 hG with (eo_ite_true_rep _ hx_74 h_v77)
        · ite_branch hbv_74
          step as ⟨e_v78, he_v78⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s8 e_v78 (by rw [he_v78]; exact empty_args) hinv8 h64 as ⟨v78, s9, hinv9, h_v78⟩ growing hG carrying h_v4 h_v47 h_v48 h_v73 dropping h_a0 he_v78 e_v78
          step as ⟨e_v79, he_v79⟩
          store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s9 e_v79 (by rw [he_v79]; rfl) h_v78 h_v4 hinv9 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v79, s10, hinv10, h_v79⟩ growing hG carrying h_v47 h_v48 h_v73 dropping h_v4 h_v78 he_v79 e_v79 v4 v78
          ite_done hinv10 hG with (eo_ite_false_rep _ hx_74 h_v79)
        · ite_branch hbv_74
          ite_stuck hinv8 hG with hx_74)
      store_step with h_ite_v80 as ⟨v80, s9, hinv9, h_v80⟩ growing hG carrying h_v47 h_v48 h_v73 dropping h_a0 h_ite_v80 h_v4 v4
      store_step with ih.eo__24str_5fstrip_5fprefix s9 v73 v80 _ _ hinv9 h64 (hG.rem hrem) h_v73 h_v80 as ⟨v81, s10, hinv10, h_v81⟩ growing hG carrying h_v47 h_v48 dropping h_v73 h_v80 v73 v80
      store_step with ih.eo__24pair_5fsecond s10 v81 _ hinv10 h64 (hG.rem hrem) h_v81 as ⟨v82, s11, hinv11, h_v82⟩ growing hG carrying h_v47 h_v48 dropping h_v81 v81
      ite_done hinv11 hG with (eo_ite_false_rep _ hx_49 h_v82)
    · ite_branch hbv_49
      ite_stuck hinv7 hG with hx_49)
  store_step with h_ite_v83 as ⟨v83, s8, hinv8, h_v83⟩ growing hG carrying h_v47 h_v48 dropping h_ite_v83 h_v4 h_v7 hinv7 s7 v4 v7
  step as ⟨e_v84, he_v84⟩
  store_step with Store.builtin_spec_list_singleton_elim n ih.eo__24eo_5fis_5flist_5fnil s8 e_v84 (by rw [he_v84]; rfl) h_v48 h_v83 hinv8 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_apply_eo_str_2e_2b_2b as ⟨v84, s9, hinv9, h_v84⟩ growing hG carrying h_v47 dropping h_v48 h_v83 he_v84 hinv8 e_v84 s8 v48 v83
  store_step with Store.apply_mk_rep s9 v47 v84 _ _ hinv9 h64 h_v47 h_v84 as ⟨v85, s10, hinv10, h_v85⟩ growing hG carrying dropping h_v47 h_v84 hinv9 s9 v47 v84
  case_done hinv10 hG with h_v85 in EoCases.__eo_prog_concat_eq.case_0 using hn_a0 hn_v3 hn_v4 hn_v6 hn_v7

set_option maxHeartbeats 5000000 in
/-- logos's `__eo_prog_concat_eq` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fconcat_5feq.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_concat_eq x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_concat_eq.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_concat_eq
  unfold EoCases.__eo_prog_concat_eq.case_0
  logos_eq

set_option maxHeartbeats 5000000 in
theorem body_eo__24eo_5fprog_5fconcat_5feq_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5fconcat_5feq s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_concat_eq x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fconcat_5feq.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5fconcat_5feq
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fconcat_5feq_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_concat_eq.case_0

set_option maxHeartbeats 5000000 in
theorem eo__24eo_5fprog_5fconcat_5feq_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fconcat_5feq.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5fconcat_5feq
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fconcat_5feq s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_concat_eq x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fconcat_5feq_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

end pathos_compiled_checker
