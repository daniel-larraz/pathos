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

set_option maxHeartbeats 4000000 in
theorem case_0_eo__24chain_5fm_5fresolve_5frec_5fstep_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    case_0_eo__24chain_5fm_5fresolve_5frec_5fstep s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__chain_m_resolve_rec_step.case_0 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__chain_m_resolve_rec_step.case_0 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24chain_5fm_5fresolve_5frec_5fstep
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__chain_m_resolve_rec_step.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__chain_m_resolve_rec_step.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__40_40pair.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__chain_m_resolve_rec_step.case_0
  have h_ite_v9 := (show if_0_eo__24chain_5fm_5fresolve_5frec_5fstep s1 a2 a3 ⦃ r s' => s'.Inv ∧ s1.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_0_eo__24chain_5fm_5fresolve_5frec_5fstep
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s1
    rcases Store.boolean_value_term h_a2 with ⟨hx_7, hbv_7⟩ | ⟨hx_7, hbv_7⟩ | ⟨hx_7, hbv_7⟩
    · ite_branch hbv_7
      step as ⟨e_v7, he_v7⟩
      store_step with CtorSpec.eo_not.construct s1 e_v7 (by rw [he_v7]; exact empty_args) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v2 h_v4 h_v5 h_v6
      store_step with Store.apply_rep s2 v7 a3 _ _ hinv2 h64 h_v7 h_a3 (by ns_tac) (by ns_tac) as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
      ite_done hinv3 hG with (eo_ite_true_rep _ hx_7 h_v8)
    · ite_branch hbv_7
      ite_done hinv1 hG with (eo_ite_false_rep _ hx_7 h_a3)
    · ite_branch hbv_7
      ite_stuck hinv1 hG with hx_7)
  store_step with h_ite_v9 as ⟨v9, s2, hinv2, h_v9⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v2 h_v4 h_v5 h_v6
  step as ⟨e_v10, he_v10⟩
  store_step with Store.builtin_spec_eq s2 e_v10 (by rw [he_v10]; rfl) h_v9 h_a1 hinv2 h64 as ⟨v10, s3, hinv3, h_v10⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v2 h_v4 h_v5 h_v6 h_v9
  have h_ite_v39 := (show if_5_eo__24chain_5fm_5fresolve_5frec_5fstep s3 v10 v5 a2 a3 v2 a1 ⦃ r s' => s'.Inv ∧ s3.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_5_eo__24chain_5fm_5fresolve_5frec_5fstep more_4_eo__24chain_5fm_5fresolve_5frec_5fstep
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s3
    rcases Store.boolean_value_term h_v10 with ⟨hx_11, hbv_11⟩ | ⟨hx_11, hbv_11⟩ | ⟨hx_11, hbv_11⟩
    · ite_branch hbv_11
      step as ⟨e_v11, he_v11⟩
      store_step with CtorSpec.eo__40_40pair.construct s3 e_v11 (by rw [he_v11]; exact empty_args) hinv3 h64 as ⟨v11, s4, hinv4, h_v11⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v2 h_v4 h_v5 h_v6 h_v9 h_v10
      store_step with Store.apply_rep s4 v11 v5 _ _ hinv4 h64 h_v11 h_v5 (by ns_tac) (by ns_tac) as ⟨v12, s5, hinv5, h_v12⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v2 h_v4 h_v5 h_v6 h_v9 h_v10 h_v11
      step as ⟨e_v13, he_v13⟩
      store_step with CtorSpec.eo_or.construct s5 e_v13 (by rw [he_v13]; exact empty_args) hinv5 h64 as ⟨v13, s6, hinv6, h_v13⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v2 h_v4 h_v5 h_v6 h_v9 h_v10 h_v11 h_v12
      have h_ite_v16 := (show if_1_eo__24chain_5fm_5fresolve_5frec_5fstep s6 a2 a3 ⦃ r s' => s'.Inv ∧ s6.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_1_eo__24chain_5fm_5fresolve_5frec_5fstep
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s6
        rcases Store.boolean_value_term h_a2 with ⟨hx_14, hbv_14⟩ | ⟨hx_14, hbv_14⟩ | ⟨hx_14, hbv_14⟩
        · ite_branch hbv_14
          ite_done hinv6 hG with (eo_ite_true_rep _ hx_14 h_a3)
        · ite_branch hbv_14
          step as ⟨e_v14, he_v14⟩
          store_step with CtorSpec.eo_not.construct s6 e_v14 (by rw [he_v14]; exact empty_args) hinv6 h64 as ⟨v14, s7, hinv7, h_v14⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v2 h_v4 h_v5 h_v6 h_v9 h_v10 h_v11 h_v12 h_v13
          store_step with Store.apply_rep s7 v14 a3 _ _ hinv7 h64 h_v14 h_a3 (by ns_tac) (by ns_tac) as ⟨v15, s8, hinv8, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v2 h_v4 h_v5 h_v6 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14
          ite_done hinv8 hG with (eo_ite_false_rep _ hx_14 h_v15)
        · ite_branch hbv_14
          ite_stuck hinv6 hG with hx_14)
      store_step with h_ite_v16 as ⟨v16, s7, hinv7, h_v16⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v2 h_v4 h_v5 h_v6 h_v9 h_v10 h_v11 h_v12 h_v13
      store_step with Store.apply_mk_rep s7 v13 v16 _ _ hinv7 h64 h_v13 h_v16 as ⟨v17, s8, hinv8, h_v17⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v2 h_v4 h_v5 h_v6 h_v9 h_v10 h_v11 h_v12 h_v13 h_v16
      store_step with Store.apply_mk_rep s8 v17 v2 _ _ hinv8 h64 h_v17 h_v2 as ⟨v18, s9, hinv9, h_v18⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v2 h_v4 h_v5 h_v6 h_v9 h_v10 h_v11 h_v12 h_v13 h_v16 h_v17
      store_step with Store.apply_mk_rep s9 v12 v18 _ _ hinv9 h64 h_v12 h_v18 as ⟨v19, s10, hinv10, h_v19⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v2 h_v4 h_v5 h_v6 h_v9 h_v10 h_v11 h_v12 h_v13 h_v16 h_v17 h_v18
      ite_done hinv10 hG with (eo_ite_true_rep _ hx_11 h_v19)
    · ite_branch hbv_11
      step as ⟨e_v20, he_v20⟩
      store_step with CtorSpec.eo__40_40pair.construct s3 e_v20 (by rw [he_v20]; exact empty_args) hinv3 h64 as ⟨v20, s4, hinv4, h_v20⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v2 h_v4 h_v5 h_v6 h_v9 h_v10
      step as ⟨e_v21, he_v21⟩
      store_step with CtorSpec.eo_or.construct s4 e_v21 (by rw [he_v21]; exact empty_args) hinv4 h64 as ⟨v21, s5, hinv5, h_v21⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v2 h_v4 h_v5 h_v6 h_v9 h_v10 h_v20
      step as ⟨e_v22, he_v22⟩
      store_step with CtorSpec.eo_or.construct s5 e_v22 (by rw [he_v22]; exact empty_args) hinv5 h64 as ⟨v22, s6, hinv6, h_v22⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v2 h_v4 h_v5 h_v6 h_v9 h_v10 h_v20 h_v21
      step as ⟨e_v23, he_v23⟩
      store_step with CtorSpec.eo_or.construct s6 e_v23 (by rw [he_v23]; exact empty_args) hinv6 h64 as ⟨v23, s7, hinv7, h_v23⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v2 h_v4 h_v5 h_v6 h_v9 h_v10 h_v20 h_v21 h_v22
      have h_ite_v26 := (show if_2_eo__24chain_5fm_5fresolve_5frec_5fstep s7 a2 a3 ⦃ r s' => s'.Inv ∧ s7.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_2_eo__24chain_5fm_5fresolve_5frec_5fstep
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s7
        rcases Store.boolean_value_term h_a2 with ⟨hx_24, hbv_24⟩ | ⟨hx_24, hbv_24⟩ | ⟨hx_24, hbv_24⟩
        · ite_branch hbv_24
          step as ⟨e_v24, he_v24⟩
          store_step with CtorSpec.eo_not.construct s7 e_v24 (by rw [he_v24]; exact empty_args) hinv7 h64 as ⟨v24, s8, hinv8, h_v24⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v2 h_v4 h_v5 h_v6 h_v9 h_v10 h_v20 h_v21 h_v22 h_v23
          store_step with Store.apply_rep s8 v24 a3 _ _ hinv8 h64 h_v24 h_a3 (by ns_tac) (by ns_tac) as ⟨v25, s9, hinv9, h_v25⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v2 h_v4 h_v5 h_v6 h_v9 h_v10 h_v20 h_v21 h_v22 h_v23 h_v24
          ite_done hinv9 hG with (eo_ite_true_rep _ hx_24 h_v25)
        · ite_branch hbv_24
          ite_done hinv7 hG with (eo_ite_false_rep _ hx_24 h_a3)
        · ite_branch hbv_24
          ite_stuck hinv7 hG with hx_24)
      store_step with h_ite_v26 as ⟨v26, s8, hinv8, h_v26⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v2 h_v4 h_v5 h_v6 h_v9 h_v10 h_v20 h_v21 h_v22 h_v23
      store_step with Store.apply_mk_rep s8 v23 v26 _ _ hinv8 h64 h_v23 h_v26 as ⟨v27, s9, hinv9, h_v27⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v2 h_v4 h_v5 h_v6 h_v9 h_v10 h_v20 h_v21 h_v22 h_v23 h_v26
      store_step with Store.apply_mk_rep s9 v27 v2 _ _ hinv9 h64 h_v27 h_v2 as ⟨v28, s10, hinv10, h_v28⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v2 h_v4 h_v5 h_v6 h_v9 h_v10 h_v20 h_v21 h_v22 h_v23 h_v26 h_v27
      step as ⟨e_v29, he_v29⟩
      store_step with Store.builtin_spec_list_diff n ih.eo__24eo_5fis_5flist_5fnil s10 e_v29 (by rw [he_v29]; rfl) h_v22 h_a1 h_v28 hinv10 h64 (hG.rem hrem) (by not_left_tac) (by unique_nil_tac) as ⟨v29, s11, hinv11, h_v29⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v2 h_v4 h_v5 h_v6 h_v9 h_v10 h_v20 h_v21 h_v22 h_v23 h_v26 h_v27 h_v28
      step as ⟨e_v30, he_v30⟩
      store_step with Store.builtin_spec_list_concat n ih.eo__24eo_5fis_5flist_5fnil s11 e_v30 (by rw [he_v30]; rfl) h_v21 h_v29 h_v5 hinv11 h64 (hG.rem hrem) (by not_left_tac) (by unique_nil_tac) as ⟨v30, s12, hinv12, h_v30⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v2 h_v4 h_v5 h_v6 h_v9 h_v10 h_v20 h_v21 h_v22 h_v23 h_v26 h_v27 h_v28 h_v29
      store_step with Store.apply_mk_rep s12 v20 v30 _ _ hinv12 h64 h_v20 h_v30 as ⟨v31, s13, hinv13, h_v31⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v2 h_v4 h_v5 h_v6 h_v9 h_v10 h_v20 h_v21 h_v22 h_v23 h_v26 h_v27 h_v28 h_v29 h_v30
      step as ⟨e_v32, he_v32⟩
      store_step with CtorSpec.eo_or.construct s13 e_v32 (by rw [he_v32]; exact empty_args) hinv13 h64 as ⟨v32, s14, hinv14, h_v32⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v2 h_v4 h_v5 h_v6 h_v9 h_v10 h_v20 h_v21 h_v22 h_v23 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31
      have h_ite_v35 := (show if_3_eo__24chain_5fm_5fresolve_5frec_5fstep s14 a2 a3 ⦃ r s' => s'.Inv ∧ s14.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_3_eo__24chain_5fm_5fresolve_5frec_5fstep
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s14
        rcases Store.boolean_value_term h_a2 with ⟨hx_33, hbv_33⟩ | ⟨hx_33, hbv_33⟩ | ⟨hx_33, hbv_33⟩
        · ite_branch hbv_33
          ite_done hinv14 hG with (eo_ite_true_rep _ hx_33 h_a3)
        · ite_branch hbv_33
          step as ⟨e_v33, he_v33⟩
          store_step with CtorSpec.eo_not.construct s14 e_v33 (by rw [he_v33]; exact empty_args) hinv14 h64 as ⟨v33, s15, hinv15, h_v33⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v2 h_v4 h_v5 h_v6 h_v9 h_v10 h_v20 h_v21 h_v22 h_v23 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32
          store_step with Store.apply_rep s15 v33 a3 _ _ hinv15 h64 h_v33 h_a3 (by ns_tac) (by ns_tac) as ⟨v34, s16, hinv16, h_v34⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v2 h_v4 h_v5 h_v6 h_v9 h_v10 h_v20 h_v21 h_v22 h_v23 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33
          ite_done hinv16 hG with (eo_ite_false_rep _ hx_33 h_v34)
        · ite_branch hbv_33
          ite_stuck hinv14 hG with hx_33)
      store_step with h_ite_v35 as ⟨v35, s15, hinv15, h_v35⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v2 h_v4 h_v5 h_v6 h_v9 h_v10 h_v20 h_v21 h_v22 h_v23 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32
      store_step with Store.apply_mk_rep s15 v32 v35 _ _ hinv15 h64 h_v32 h_v35 as ⟨v36, s16, hinv16, h_v36⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v2 h_v4 h_v5 h_v6 h_v9 h_v10 h_v20 h_v21 h_v22 h_v23 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v35
      store_step with Store.apply_mk_rep s16 v36 v2 _ _ hinv16 h64 h_v36 h_v2 as ⟨v37, s17, hinv17, h_v37⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v2 h_v4 h_v5 h_v6 h_v9 h_v10 h_v20 h_v21 h_v22 h_v23 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v35 h_v36
      store_step with Store.apply_mk_rep s17 v31 v37 _ _ hinv17 h64 h_v31 h_v37 as ⟨v38, s18, hinv18, h_v38⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v2 h_v4 h_v5 h_v6 h_v9 h_v10 h_v20 h_v21 h_v22 h_v23 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v35 h_v36 h_v37
      ite_done hinv18 hG with (eo_ite_false_rep _ hx_11 h_v38)
    · ite_branch hbv_11
      ite_stuck hinv3 hG with hx_11)
  store_step with h_ite_v39 as ⟨v39, s4, hinv4, h_v39⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v2 h_v4 h_v5 h_v6 h_v9 h_v10
  case_done hinv4 hG with h_v39 in EoCases.__chain_m_resolve_rec_step.case_0 using hn_a0 hn_a1 hn_a2 hn_a3 hn_v1 hn_v2 hn_v4 hn_v5

set_option maxHeartbeats 4000000 in
/-- logos's `__chain_m_resolve_rec_step` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24chain_5fm_5fresolve_5frec_5fstep.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) :
    __chain_m_resolve_rec_step x_a0 x_a1 x_a2 x_a3 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__chain_m_resolve_rec_step.case_0 x_a0 x_a1 x_a2 x_a3] HasStuck.stuck) := by
  conv => lhs; unfold __chain_m_resolve_rec_step
  unfold EoCases.__chain_m_resolve_rec_step.case_0
  logos_eq

set_option maxHeartbeats 4000000 in
theorem body_eo__24chain_5fm_5fresolve_5frec_5fstep_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) :
    body_eo__24chain_5fm_5fresolve_5frec_5fstep s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__chain_m_resolve_rec_step x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24chain_5fm_5fresolve_5frec_5fstep.rust_eq x_a0 x_a1 x_a2 x_a3 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3)]
  unfold body_eo__24chain_5fm_5fresolve_5frec_5fstep
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  stuck_check h_a3 : x_a3 as hn_a3 else hinv hG
  case_step with case_0_eo__24chain_5fm_5fresolve_5frec_5fstep_spec n ih s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2 hn_a3
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 using hn_a0 hn_a1 hn_a2 hn_a3
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hn_a3 hc0 in EoCases.__chain_m_resolve_rec_step.case_0

set_option maxHeartbeats 4000000 in
theorem eo__24chain_5fm_5fresolve_5frec_5fstep_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24chain_5fm_5fresolve_5frec_5fstep.Spec n := by
  intro s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3
  unfold eo__24chain_5fm_5fresolve_5frec_5fstep
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24chain_5fm_5fresolve_5frec_5fstep s1 a0 a1 a2 a3) (fun s' t => Represents.rep s' t (__chain_m_resolve_rec_step x_a0 x_a1 x_a2 x_a3))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24chain_5fm_5fresolve_5frec_5fstep_spec m (ih m hm) s1 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

end pathos_compiled_checker
