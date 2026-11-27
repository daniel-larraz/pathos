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
theorem case_0_eo__24substitute_5fsimul_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) (hn_a4 : x_a4 ≠ Eo.Term.Stuck) :
    case_0_eo__24substitute_5fsimul_5frec s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__substitute_simul_rec.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__substitute_simul_rec.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24substitute_5fsimul_5frec
  have hG := Store.Grows.refl s
  pat_unapply h_a1 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__substitute_simul_rec.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__substitute_simul_rec.case_0
  pat_unapply h_v5 as ⟨v7, v8, x_v7, x_v8, h_v7, h_v8, hn_v7, hn_v8⟩ using hinv else hinv hG in EoCases.__substitute_simul_rec.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv else hinv hG in EoCases.__substitute_simul_rec.case_0
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s e_v12 (by rw [he_v12]; exact empty_args) hinv h64 as ⟨v12, s1, hinv1, h_v12⟩ growing hG carrying h_a0 h_a2 h_a3 h_a4 h_v2 h_v4 h_v8 h_v10 h_v11 dropping h_a1 h_v1 h_v5 h_v7 he_v12 e_v12 v1 v5 v7
  pat_same v10 v12 with h_v10 h_v12 using hinv1 else hinv1 hG in EoCases.__substitute_simul_rec.case_0
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s1 e_v13 (by rw [he_v13]; exact empty_args) hinv1 h64 as ⟨v13, s2, hinv2, h_v13⟩ growing hG carrying h_a0 h_a2 h_a3 h_a4 h_v2 h_v4 h_v8 h_v11 dropping h_v10 h_v12 he_v13 hinv1 e_v13 s1 v10 v12
  store_step with Store.apply_rep s2 v13 v11 _ _ hinv2 h64 h_v13 h_v11 (by ns_tac) (by ns_tac) as ⟨v14, s3, hinv3, h_v14⟩ growing hG carrying h_a0 h_a2 h_a3 h_a4 h_v2 h_v4 h_v8 h_v11 dropping h_v13 hinv2 s2 v13
  store_step with Store.apply_rep s3 v14 v8 _ _ hinv3 h64 h_v14 h_v8 (by ns_tac) (by ns_tac) as ⟨v15, s4, hinv4, h_v15⟩ growing hG carrying h_a0 h_a2 h_a3 h_a4 h_v2 h_v4 h_v8 h_v11 dropping h_v14 hinv3 s3 v14
  step as ⟨e_v16, he_v16⟩
  store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s4 e_v16 (by rw [he_v16]; exact empty_args) hinv4 h64 as ⟨v16, s5, hinv5, h_v16⟩ growing hG carrying h_a0 h_a2 h_a3 h_a4 h_v2 h_v4 h_v8 h_v11 h_v15 dropping he_v16 hinv4 e_v16 s4
  store_step with ih.eo__24contains_5fatomic_5fterm_5flist_5ffree_5frec s5 a3 v15 v16 _ _ _ hinv5 h64 (hG.rem hrem) h_a3 h_v15 h_v16 as ⟨v17, s6, hinv6, h_v17⟩ growing hG carrying h_a0 h_a2 h_a3 h_a4 h_v2 h_v4 h_v8 h_v11 dropping h_v15 h_v16 hinv5 s5 v15 v16
  store_step with Store.literal_boolean_spec s6 false hinv6 h64 as ⟨v18, s7, hinv7, h_v18⟩ growing hG carrying h_a0 h_a2 h_a3 h_a4 h_v2 h_v4 h_v8 h_v11 h_v17 dropping hinv6 s6
  have h_req_v38 := (show requires_1_eo__24substitute_5fsimul_5frec s7 v17 v18 a0 v11 v8 a2 a3 a4 v4 v2 ⦃ r s' => s'.Inv ∧ s7.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold requires_1_eo__24substitute_5fsimul_5frec
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s7
    req_same v17 v18 with h_v17 h_v18 using hinv7 hG
    req_stuck h_v17 as hq_v17 using hinv7 hG
    have h_ite_v37 := (show if_0_eo__24substitute_5fsimul_5frec s7 a0 v11 v8 a0 a2 a3 a4 v4 v2 ⦃ r s' => s'.Inv ∧ s7.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
      unfold if_0_eo__24substitute_5fsimul_5frec
      have hrem := (hG.rem hrem)
      have hG := Store.Grows.refl s7
      rcases Store.boolean_value_term h_a0 with ⟨hx_19, hbv_19⟩ | ⟨hx_19, hbv_19⟩ | ⟨hx_19, hbv_19⟩
      · ite_branch hbv_19
        step as ⟨e_v19, he_v19⟩
        store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s7 e_v19 (by rw [he_v19]; exact empty_args) hinv7 h64 as ⟨v19, s8, hinv8, h_v19⟩ growing hG carrying h_a0 h_a2 h_a3 h_a4 h_v2 h_v4 h_v8 h_v11 dropping h_v17 h_v18 he_v19 e_v19 v17 v18
        store_step with Store.apply_rep s8 v19 v11 _ _ hinv8 h64 h_v19 h_v11 (by ns_tac) (by ns_tac) as ⟨v20, s9, hinv9, h_v20⟩ growing hG carrying h_a0 h_a2 h_a3 h_a4 h_v2 h_v4 h_v8 h_v11 dropping h_v19 v19
        store_step with Store.apply_rep s9 v20 v8 _ _ hinv9 h64 h_v20 h_v8 (by ns_tac) (by ns_tac) as ⟨v21, s10, hinv10, h_v21⟩ growing hG carrying h_a0 h_a2 h_a3 h_a4 h_v2 h_v4 h_v8 h_v11 dropping h_v20 v20
        store_step with ih.eo__24substitute_5fsimul_5frec s10 a0 v21 a2 a3 a4 _ _ _ _ _ hinv10 h64 (hG.rem hrem) h_a0 h_v21 h_a2 h_a3 h_a4 as ⟨v22, s11, hinv11, h_v22⟩ growing hG carrying h_a0 h_a2 h_a3 h_a4 h_v2 h_v4 h_v8 h_v11 dropping h_v21 v21
        store_step with Store.apply_mk_rep s11 v4 v22 _ _ hinv11 h64 h_v4 h_v22 as ⟨v23, s12, hinv12, h_v23⟩ growing hG carrying h_a0 h_a2 h_a3 h_a4 h_v2 h_v4 h_v8 h_v11 dropping h_v22 v22
        store_step with ih.eo__24substitute_5fsimul_5frec s12 a0 v2 a2 a3 a4 _ _ _ _ _ hinv12 h64 (hG.rem hrem) h_a0 h_v2 h_a2 h_a3 h_a4 as ⟨v24, s13, hinv13, h_v24⟩ growing hG carrying h_a0 h_a2 h_a3 h_a4 h_v2 h_v4 h_v8 h_v11 h_v23 dropping
        store_step with Store.apply_mk_rep s13 v23 v24 _ _ hinv13 h64 h_v23 h_v24 as ⟨v25, s14, hinv14, h_v25⟩ growing hG carrying h_a0 h_a2 h_a3 h_a4 h_v2 h_v4 h_v8 h_v11 dropping h_v23 h_v24 v23 v24
        ite_done hinv14 hG with (eo_ite_true_rep _ hx_19 h_v25)
      · ite_branch hbv_19
        step as ⟨e_v26, he_v26⟩
        store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s7 e_v26 (by rw [he_v26]; exact empty_args) hinv7 h64 as ⟨v26, s8, hinv8, h_v26⟩ growing hG carrying h_a0 h_a2 h_a3 h_a4 h_v2 h_v4 h_v8 h_v11 dropping h_v17 h_v18 he_v26 e_v26 v17 v18
        store_step with Store.apply_rep s8 v26 v11 _ _ hinv8 h64 h_v26 h_v11 (by ns_tac) (by ns_tac) as ⟨v27, s9, hinv9, h_v27⟩ growing hG carrying h_a0 h_a2 h_a3 h_a4 h_v2 h_v4 h_v8 h_v11 dropping h_v26 v26
        store_step with Store.apply_rep s9 v27 v8 _ _ hinv9 h64 h_v27 h_v8 (by ns_tac) (by ns_tac) as ⟨v28, s10, hinv10, h_v28⟩ growing hG carrying h_a0 h_a2 h_a3 h_a4 h_v2 h_v4 h_v8 h_v11 dropping h_v27 v27
        store_step with Store.apply_rep s10 v4 v28 _ _ hinv10 h64 h_v4 h_v28 (by ns_tac) (by ns_tac) as ⟨v29, s11, hinv11, h_v29⟩ growing hG carrying h_a0 h_a2 h_a3 h_a4 h_v2 h_v8 h_v11 dropping h_v28 h_v4 hinv10 s10 v28 v4
        step as ⟨e_v30, he_v30⟩
        store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s11 e_v30 (by rw [he_v30]; exact empty_args) hinv11 h64 as ⟨v30, s12, hinv12, h_v30⟩ growing hG carrying h_a0 h_a2 h_a3 h_a4 h_v2 h_v8 h_v11 h_v29 dropping he_v30 hinv11 e_v30 s11
        step as ⟨e_v31, he_v31⟩
        store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s12 e_v31 (by rw [he_v31]; exact empty_args) hinv12 h64 as ⟨v31, s13, hinv13, h_v31⟩ growing hG carrying h_a0 h_a2 h_a3 h_a4 h_v2 h_v8 h_v11 h_v29 h_v30 dropping he_v31 hinv12 e_v31 s12
        store_step with Store.apply_rep s13 v31 v11 _ _ hinv13 h64 h_v31 h_v11 (by ns_tac) (by ns_tac) as ⟨v32, s14, hinv14, h_v32⟩ growing hG carrying h_a0 h_a2 h_a3 h_a4 h_v2 h_v8 h_v29 h_v30 dropping h_v11 h_v31 hinv13 s13 v11 v31
        store_step with Store.apply_rep s14 v32 v8 _ _ hinv14 h64 h_v32 h_v8 (by ns_tac) (by ns_tac) as ⟨v33, s15, hinv15, h_v33⟩ growing hG carrying h_a0 h_a2 h_a3 h_a4 h_v2 h_v29 h_v30 dropping h_v32 h_v8 hinv14 s14 v32 v8
        step as ⟨e_v34, he_v34⟩
        store_step with Store.builtin_spec_list_concat n ih.eo__24eo_5fis_5flist_5fnil s15 e_v34 (by rw [he_v34]; rfl) h_v30 h_v33 h_a4 hinv15 h64 (hG.rem hrem) (by not_left_tac) (by unique_nil_tac) as ⟨v34, s16, hinv16, h_v34⟩ growing hG carrying h_a0 h_a2 h_a3 h_v2 h_v29 dropping h_a4 h_v30 h_v33 he_v34 hinv15 e_v34 s15 v30 v33
        store_step with ih.eo__24substitute_5fsimul_5frec s16 a0 v2 a2 a3 v34 _ _ _ _ _ hinv16 h64 (hG.rem hrem) h_a0 h_v2 h_a2 h_a3 h_v34 as ⟨v35, s17, hinv17, h_v35⟩ growing hG carrying h_v29 dropping h_a0 h_a2 h_a3 h_v2 h_v34 hinv16 s16 v2 v34
        store_step with Store.apply_mk_rep s17 v29 v35 _ _ hinv17 h64 h_v29 h_v35 as ⟨v36, s18, hinv18, h_v36⟩ growing hG carrying dropping h_v29 h_v35 hinv17 s17 v29 v35
        ite_done hinv18 hG with (eo_ite_false_rep _ hx_19 h_v36)
      · ite_branch hbv_19
        ite_stuck hinv7 hG with hx_19)
    store_step with h_ite_v37 as ⟨v37, s8, hinv8, h_v37⟩ growing hG carrying dropping h_a3 h_ite_v37 h_v11 h_v17 h_v18 h_v2 h_v4 h_v8 hinv7 s7 v11 v17 v18 v2 v4 v8
    req_done hinv8 hG with h_v37 using hq_v17)
  store_step with h_req_v38 as ⟨v38, s9, hinv9, h_v38⟩ growing hG carrying dropping h_a3 h_req_v38 h_v11 h_v17 h_v18 h_v2 h_v4 h_v8 hinv7 s7 v11 v17 v18 v2 v4 v8
  case_done hinv9 hG with h_v38 in EoCases.__substitute_simul_rec.case_0 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_v1 hn_v2 hn_v4 hn_v5 hn_v7 hn_v8 hn_v10 hn_v11

set_option maxHeartbeats 20000000 in
theorem case_1_eo__24substitute_5fsimul_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) (hn_a4 : x_a4 ≠ Eo.Term.Stuck) :
    case_1_eo__24substitute_5fsimul_5frec s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__substitute_simul_rec.case_1 x_a0 x_a1 x_a2 x_a3 x_a4 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__substitute_simul_rec.case_1 x_a0 x_a1 x_a2 x_a3 x_a4 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24substitute_5fsimul_5frec
  have hG := Store.Grows.refl s
  pat_unapply h_a1 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__substitute_simul_rec.case_1
  store_step with ih.eo__24substitute_5fsimul_5frec s a0 v1 a2 a3 a4 _ _ _ _ _ hinv h64 hrem h_a0 h_v1 h_a2 h_a3 h_a4 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_a2 h_a3 h_a4 h_v2 dropping h_a1 h_v1 v1
  store_step with ih.eo__24substitute_5fsimul_5frec s1 a0 v2 a2 a3 a4 _ _ _ _ _ hinv1 h64 (hG.rem hrem) h_a0 h_v2 h_a2 h_a3 h_a4 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v3 dropping h_a0 h_a2 h_a3 h_a4 h_v2 hinv1 s1 v2
  store_step with Store.apply_mk_rep s2 v3 v4 _ _ hinv2 h64 h_v3 h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying dropping h_v3 h_v4 hinv2 s2 v3 v4
  case_done hinv3 hG with h_v5 in EoCases.__substitute_simul_rec.case_1 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_v1 hn_v2

set_option maxHeartbeats 20000000 in
theorem case_2_eo__24substitute_5fsimul_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) (hn_a4 : x_a4 ≠ Eo.Term.Stuck) :
    case_2_eo__24substitute_5fsimul_5frec s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__substitute_simul_rec.case_2 x_a0 x_a1 x_a2 x_a3 x_a4 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__substitute_simul_rec.case_2 x_a0 x_a1 x_a2 x_a3 x_a4 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24substitute_5fsimul_5frec
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fVar.destruct h_a1 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__substitute_simul_rec.case_2
  obtain ⟨hn_v1, hn_v2⟩ := CtorSpec.eo__24emb_5fVar.fields_ne_stuck hinv h_a1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a2 h_a3 h_a4 h_v1 h_v2 dropping h_a1 he_v3 e_v3
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s1 e_v4 (by rw [he_v4]; rfl) h_v1 h_v2 hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a2 h_a3 h_a4 h_v1 h_v2 h_v3 dropping he_v4 hinv1 e_v4 s1
  step as ⟨e_v5, he_v5⟩
  store_step with Store.builtin_spec_list_find n ih.eo__24eo_5fis_5flist_5fnil s2 e_v5 (by rw [he_v5]; rfl) h_v3 h_a4 h_v4 hinv2 h64 (hG.rem hrem) (by not_left_tac) as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a2 h_a3 h_v1 h_v2 dropping h_a4 h_v3 h_v4 he_v5 hinv2 e_v5 s2 v3 v4
  step as ⟨e_v6, he_v6⟩
  store_step with Store.builtin_spec_is_neg s3 e_v6 (by rw [he_v6]; rfl) h_v5 hinv3 h64 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a2 h_a3 h_v1 h_v2 dropping h_v5 he_v6 hinv3 e_v6 s3 v5
  have h_ite_v19 := (show if_4_eo__24substitute_5fsimul_5frec s4 v6 v1 v2 a2 a3 ⦃ r s' => s'.Inv ∧ s4.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_4_eo__24substitute_5fsimul_5frec
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s4
    rcases Store.boolean_value_term h_v6 with ⟨hx_7, hbv_7⟩ | ⟨hx_7, hbv_7⟩ | ⟨hx_7, hbv_7⟩
    · ite_branch hbv_7
      step as ⟨e_v7, he_v7⟩
      store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s4 e_v7 (by rw [he_v7]; exact empty_args) hinv4 h64 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_a2 h_a3 h_v1 h_v2 dropping h_v6 he_v7 e_v7 v6
      step as ⟨e_v8, he_v8⟩
      store_step with CtorSpec.eo__24emb_5fVar.construct s5 e_v8 (by rw [he_v8]; rfl) h_v1 h_v2 hinv5 h64 as ⟨v8, s6, hinv6, h_v8⟩ growing hG carrying h_a2 h_a3 h_v1 h_v2 h_v7 dropping he_v8 e_v8
      step as ⟨e_v9, he_v9⟩
      store_step with Store.builtin_spec_list_find n ih.eo__24eo_5fis_5flist_5fnil s6 e_v9 (by rw [he_v9]; rfl) h_v7 h_a2 h_v8 hinv6 h64 (hG.rem hrem) (by not_left_tac) as ⟨v9, s7, hinv7, h_v9⟩ growing hG carrying h_a2 h_a3 h_v1 h_v2 dropping h_v7 h_v8 he_v9 hinv6 e_v9 s6 v7 v8
      step as ⟨e_v10, he_v10⟩
      store_step with Store.builtin_spec_is_neg s7 e_v10 (by rw [he_v10]; rfl) h_v9 hinv7 h64 as ⟨v10, s8, hinv8, h_v10⟩ growing hG carrying h_a2 h_a3 h_v1 h_v2 dropping h_v9 he_v10 hinv7 e_v10 s7 v9
      have h_ite_v17 := (show if_3_eo__24substitute_5fsimul_5frec s8 v10 v1 v2 a2 a3 ⦃ r s' => s'.Inv ∧ s8.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_3_eo__24substitute_5fsimul_5frec
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s8
        rcases Store.boolean_value_term h_v10 with ⟨hx_11, hbv_11⟩ | ⟨hx_11, hbv_11⟩ | ⟨hx_11, hbv_11⟩
        · ite_branch hbv_11
          step as ⟨e_v11, he_v11⟩
          store_step with CtorSpec.eo__24emb_5fVar.construct s8 e_v11 (by rw [he_v11]; rfl) h_v1 h_v2 hinv8 h64 as ⟨v11, s9, hinv9, h_v11⟩ growing hG carrying h_a2 h_a3 h_v1 h_v2 dropping h_v10 he_v11 e_v11 v10
          ite_done hinv9 hG with (eo_ite_true_rep _ hx_11 h_v11)
        · ite_branch hbv_11
          step as ⟨e_v12, he_v12⟩
          store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s8 e_v12 (by rw [he_v12]; exact empty_args) hinv8 h64 as ⟨v12, s9, hinv9, h_v12⟩ growing hG carrying h_a2 h_a3 h_v1 h_v2 dropping h_v10 he_v12 e_v12 v10
          step as ⟨e_v13, he_v13⟩
          store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s9 e_v13 (by rw [he_v13]; exact empty_args) hinv9 h64 as ⟨v13, s10, hinv10, h_v13⟩ growing hG carrying h_a2 h_a3 h_v1 h_v2 h_v12 dropping he_v13 e_v13
          step as ⟨e_v14, he_v14⟩
          store_step with CtorSpec.eo__24emb_5fVar.construct s10 e_v14 (by rw [he_v14]; rfl) h_v1 h_v2 hinv10 h64 as ⟨v14, s11, hinv11, h_v14⟩ growing hG carrying h_a2 h_a3 h_v1 h_v2 h_v12 h_v13 dropping he_v14 hinv10 e_v14 s10
          step as ⟨e_v15, he_v15⟩
          store_step with Store.builtin_spec_list_find n ih.eo__24eo_5fis_5flist_5fnil s11 e_v15 (by rw [he_v15]; rfl) h_v13 h_a2 h_v14 hinv11 h64 (hG.rem hrem) (by not_left_tac) as ⟨v15, s12, hinv12, h_v15⟩ growing hG carrying h_a3 h_v1 h_v2 h_v12 dropping h_a2 h_v13 h_v14 he_v15 hinv11 e_v15 s11 v13 v14
          store_step with ih.eo__24assoc_5fnil_5fnth s12 v12 a3 v15 _ _ _ hinv12 h64 (hG.rem hrem) h_v12 h_a3 h_v15 as ⟨v16, s13, hinv13, h_v16⟩ growing hG carrying h_v1 h_v2 dropping h_a3 h_v12 h_v15 hinv12 s12 v12 v15
          ite_done hinv13 hG with (eo_ite_false_rep _ hx_11 h_v16)
        · ite_branch hbv_11
          ite_stuck hinv8 hG with hx_11)
      store_step with h_ite_v17 as ⟨v17, s9, hinv9, h_v17⟩ growing hG carrying h_v1 h_v2 dropping h_a2 h_ite_v17 h_v10 hinv8 s8 v10
      ite_done hinv9 hG with (eo_ite_true_rep _ hx_7 h_v17)
    · ite_branch hbv_7
      step as ⟨e_v18, he_v18⟩
      store_step with CtorSpec.eo__24emb_5fVar.construct s4 e_v18 (by rw [he_v18]; rfl) h_v1 h_v2 hinv4 h64 as ⟨v18, s5, hinv5, h_v18⟩ growing hG carrying dropping h_v1 h_v2 h_v6 he_v18 e_v18 v1 v2 v6
      ite_done hinv5 hG with (eo_ite_false_rep _ hx_7 h_v18)
    · ite_branch hbv_7
      ite_stuck hinv4 hG with hx_7)
  store_step with h_ite_v19 as ⟨v19, s5, hinv5, h_v19⟩ growing hG carrying dropping h_ite_v19 h_v1 h_v2 h_v6 hinv4 s4 v1 v2 v6
  case_done hinv5 hG with h_v19 in EoCases.__substitute_simul_rec.case_2 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_v1 hn_v2

set_option maxHeartbeats 20000000 in
theorem case_3_eo__24substitute_5fsimul_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) (hn_a4 : x_a4 ≠ Eo.Term.Stuck) :
    case_3_eo__24substitute_5fsimul_5frec s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__substitute_simul_rec.case_3 x_a0 x_a1 x_a2 x_a3 x_a4 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__substitute_simul_rec.case_3 x_a0 x_a1 x_a2 x_a3 x_a4 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_3_eo__24substitute_5fsimul_5frec
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a1 dropping he_v0 e_v0
  store_step with ih.eo__24is_5fclosed_5frec s1 a1 v0 _ _ hinv1 h64 (hG.rem hrem) h_a1 h_v0 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a1 dropping h_v0 hinv1 s1 v0
  store_step with Store.literal_boolean_spec s2 true hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a1 h_v1 dropping hinv2 s2
  have h_req_v3 := (show requires_5_eo__24substitute_5fsimul_5frec s3 v1 v2 a1 ⦃ r s' => s'.Inv ∧ s3.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold requires_5_eo__24substitute_5fsimul_5frec
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s3
    req_same v1 v2 with h_v1 h_v2 using hinv3 hG
    req_stuck h_v1 as hq_v1 using hinv3 hG
    req_done hinv3 hG with h_a1 using hq_v1)
  store_step with h_req_v3 as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying dropping h_a1 h_req_v3 h_v1 h_v2 hinv3 s3 v1 v2
  case_done hinv4 hG with h_v3 in EoCases.__substitute_simul_rec.case_3 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4

set_option maxHeartbeats 20000000 in
/-- logos's `__substitute_simul_rec` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24substitute_5fsimul_5frec.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) (hw_a4 : Valid.valid x_a4) :
    __substitute_simul_rec x_a0 x_a1 x_a2 x_a3 x_a4 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else if x_a4 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__substitute_simul_rec.case_0 x_a0 x_a1 x_a2 x_a3 x_a4, EoCases.__substitute_simul_rec.case_1 x_a0 x_a1 x_a2 x_a3 x_a4, EoCases.__substitute_simul_rec.case_2 x_a0 x_a1 x_a2 x_a3 x_a4, EoCases.__substitute_simul_rec.case_3 x_a0 x_a1 x_a2 x_a3 x_a4] HasStuck.stuck) := by
  conv => lhs; unfold __substitute_simul_rec
  unfold EoCases.__substitute_simul_rec.case_0 EoCases.__substitute_simul_rec.case_1 EoCases.__substitute_simul_rec.case_2 EoCases.__substitute_simul_rec.case_3
  logos_eq

set_option maxHeartbeats 20000000 in
theorem body_eo__24substitute_5fsimul_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) :
    body_eo__24substitute_5fsimul_5frec s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__substitute_simul_rec x_a0 x_a1 x_a2 x_a3 x_a4)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24substitute_5fsimul_5frec.rust_eq x_a0 x_a1 x_a2 x_a3 x_a4 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3) (by valid_tac hinv h_a4)]
  unfold body_eo__24substitute_5fsimul_5frec
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  stuck_check h_a3 : x_a3 as hn_a3 else hinv hG
  stuck_check h_a4 : x_a4 as hn_a4 else hinv hG
  case_step with case_0_eo__24substitute_5fsimul_5frec_spec n ih s a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 hn_a0 hn_a1 hn_a2 hn_a3 hn_a4
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4
  case_step with case_1_eo__24substitute_5fsimul_5frec_spec n ih s1 a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 h_a3 h_a4 hn_a0 hn_a1 hn_a2 hn_a3 hn_a4
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hc0
  case_step with case_2_eo__24substitute_5fsimul_5frec_spec n ih s2 a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv2 h64 (hG.rem hrem) h_a0 h_a1 h_a2 h_a3 h_a4 hn_a0 hn_a1 hn_a2 hn_a3 hn_a4
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hc0 hc1
  case_step with case_3_eo__24substitute_5fsimul_5frec_spec n ih s3 a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv3 h64 (hG.rem hrem) h_a0 h_a1 h_a2 h_a3 h_a4 hn_a0 hn_a1 hn_a2 hn_a3 hn_a4
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hc0 hc1 hc2
  body_stuck hinv4 hG using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hc0 hc1 hc2 hc3 in EoCases.__substitute_simul_rec.case_0 EoCases.__substitute_simul_rec.case_1 EoCases.__substitute_simul_rec.case_2 EoCases.__substitute_simul_rec.case_3

set_option maxHeartbeats 20000000 in
theorem eo__24substitute_5fsimul_5frec_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24substitute_5fsimul_5frec.Spec n := by
  intro s a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4
  unfold eo__24substitute_5fsimul_5frec
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 1095#u32 _ [a0, a1, a2, a3, a4] rfl
    (fun s1 => body_eo__24substitute_5fsimul_5frec s1 a0 a1 a2 a3 a4) (fun s' t => Represents.rep s' t (__substitute_simul_rec x_a0 x_a1 x_a2 x_a3 x_a4))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, b2, b3, b4, y0, y1, y2, y3, y4, hargs, hb0, hb1, hb2, hb3, hb4, hr⟩ := ProgramSem.of_1095 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      obtain rfl := Rep.functional hb2 (Represents.congr h_a2 hn)
      obtain rfl := Rep.functional hb3 (Represents.congr h_a3 hn)
      obtain rfl := Rep.functional hb4 (Represents.congr h_a4 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_1095 ⟨a0, a1, a2, a3, a4, x_a0, x_a1, x_a2, x_a3, x_a4, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, Rep.mono hpre h_a2, Rep.mono hpre h_a3, Rep.mono hpre h_a4, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24substitute_5fsimul_5frec_spec m (ih m hm) s1 a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn) (by congr_one h_a4 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

end pathos_compiled_checker
