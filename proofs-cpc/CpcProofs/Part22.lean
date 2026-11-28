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

theorem case_0_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_destruct_lit Store.destruct_boolean_spec s a0 h_a0 hinv h64 as ⟨v1, x_v1, h_v1⟩ storing ⟨s1, hinv1⟩ growing hG carrying in EoCases.__eo_to_smt.case_0
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eBoolean.construct s1 e_v2 (by rw [he_v2]; rfl) h_v1 hinv1 h64 as ⟨v2, s2, hinv2, h_v2⟩ growing hG carrying dropping h_a0 h_v1 he_v2 hinv1 e_v2 s1 v1
  case_done hinv2 hG with h_v2 in EoCases.__eo_to_smt.case_0 using

theorem case_1_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_1_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_1 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_1 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_destruct_lit Store.destruct_numeral_spec s a0 h_a0 hinv h64 as ⟨v1, x_v1, h_v1⟩ storing ⟨s1, hinv1⟩ growing hG carrying in EoCases.__eo_to_smt.case_1
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eNumeral.construct s1 e_v2 (by rw [he_v2]; rfl) h_v1 hinv1 h64 as ⟨v2, s2, hinv2, h_v2⟩ growing hG carrying dropping h_a0 h_v1 he_v2 hinv1 e_v2 s1 v1
  case_done hinv2 hG with h_v2 in EoCases.__eo_to_smt.case_1 using

theorem case_2_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_2_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_2 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_2 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_destruct_lit Store.destruct_rational_spec s a0 h_a0 hinv h64 as ⟨v1, x_v1, h_v1⟩ storing ⟨s1, hinv1⟩ growing hG carrying in EoCases.__eo_to_smt.case_2
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eRational.construct s1 e_v2 (by rw [he_v2]; rfl) h_v1 hinv1 h64 as ⟨v2, s2, hinv2, h_v2⟩ growing hG carrying dropping h_a0 h_v1 he_v2 hinv1 e_v2 s1 v1
  case_done hinv2 hG with h_v2 in EoCases.__eo_to_smt.case_2 using

theorem case_3_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_3_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_3 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_3 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_3_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_destruct_lit Store.destruct_string_spec s a0 h_a0 hinv h64 as ⟨v1, x_v1, h_v1⟩ storing ⟨s1, hinv1⟩ growing hG carrying in EoCases.__eo_to_smt.case_3
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eString.construct s1 e_v2 (by rw [he_v2]; rfl) h_v1 hinv1 h64 as ⟨v2, s2, hinv2, h_v2⟩ growing hG carrying dropping h_a0 h_v1 he_v2 hinv1 e_v2 s1 v1
  case_done hinv2 hG with h_v2 in EoCases.__eo_to_smt.case_3 using

theorem case_4_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_4_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_4 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_4 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_4_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_destruct_lit2 Store.destruct_binary_spec s a0 h_a0 hinv h64 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ storing ⟨s1, hinv1⟩ growing hG carrying in EoCases.__eo_to_smt.case_4
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eBinary.construct s1 e_v3 (by rw [he_v3]; rfl) h_v1 h_v2 hinv1 h64 as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying dropping h_a0 h_v1 h_v2 he_v3 hinv1 e_v3 s1 v1 v2
  case_done hinv2 hG with h_v3 in EoCases.__eo_to_smt.case_4 using

theorem case_5_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_5_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_5 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_5 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_5_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fVar.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__eo_to_smt.case_5
  obtain ⟨hn_v1, hn_v2⟩ := CtorSpec.eo__24emb_5fVar.fields_ne_stuck hinv h_a0
  pat_destruct_lit Store.destruct_string_spec s v1 h_v1 hinv h64 as ⟨v4, x_v4, h_v4⟩ storing ⟨s1, hinv1⟩ growing hG carrying h_v2 in EoCases.__eo_to_smt.case_5
  store_step with ih.eo__24eo_5fto_5fsmt_5ftype s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v5, s2, hinv2, h_v5⟩ growing hG carrying h_v4 dropping h_a0 h_v1 h_v2 hinv1 s1 v1 v2
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eVar.construct s2 e_v6 (by rw [he_v6]; rfl) h_v4 h_v5 hinv2 h64 as ⟨v6, s3, hinv3, h_v6⟩ growing hG carrying dropping h_v4 h_v5 he_v6 hinv2 e_v6 s2 v4 v5
  case_done hinv3 hG with h_v6 in EoCases.__eo_to_smt.case_5 using hn_v1 hn_v2

theorem case_6_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_6_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_6 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_6 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_6_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fDtCons.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ ⟨v3, x_v3, h_v3⟩ else hinv hG in EoCases.__eo_to_smt.case_6
  store_step with ih.eo__24eo_5fto_5fsmt_5freserved_5fdatatype_5fname s v1 _ hinv h64 hrem h_v1 as ⟨v4, s1, hinv1, h_v4⟩ growing hG carrying h_v1 h_v2 h_v3 dropping h_a0
  have h_ite_v8 := (show if_0_eo__24eo_5fto_5fsmt s1 v4 v2 v1 v3 ⦃ r s' => s'.Inv ∧ s1.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_0_eo__24eo_5fto_5fsmt
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s1
    rcases Store.boolean_value_native h_v4 with ⟨hx_5, hbv_5⟩ | ⟨hx_5, hbv_5⟩
    · ite_branch hbv_5
      step as ⟨e_v5, he_v5⟩
      store_step with CtorSpec.eo__24emb_5fsm_2eNone.construct s1 e_v5 (by rw [he_v5]; exact empty_args) hinv1 h64 as ⟨v5, s2, hinv2, h_v5⟩ growing hG carrying h_v1 h_v2 h_v3 dropping h_v4 he_v5 e_v5 v4
      ite_done hinv2 hG with (native_ite_true_rep _ hx_5 h_v5)
    · ite_branch hbv_5
      store_step with ih.eo__24eo_5fto_5fsmt_5fdatatype_5fdecl s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v6, s2, hinv2, h_v6⟩ growing hG carrying h_v1 h_v3 dropping h_v2 h_v4 hinv1 s1 v2 v4
      step as ⟨e_v7, he_v7⟩
      store_step with CtorSpec.eo__24emb_5fsm_2eDtCons.construct s2 e_v7 (by rw [he_v7]; rfl) h_v1 h_v6 h_v3 hinv2 h64 as ⟨v7, s3, hinv3, h_v7⟩ growing hG carrying dropping h_v1 h_v3 h_v6 he_v7 e_v7 v1 v3 v6
      ite_done hinv3 hG with (native_ite_false_rep _ hx_5 h_v7))
  store_step with h_ite_v8 as ⟨v8, s2, hinv2, h_v8⟩ growing hG carrying dropping h_ite_v8 h_v1 h_v2 h_v3 h_v4 hinv1 s1 v1 v2 v3 v4
  case_done hinv2 hG with h_v8 in EoCases.__eo_to_smt.case_6 using

theorem case_7_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_7_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_7 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_7 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_7_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fDtSel.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ ⟨v3, x_v3, h_v3⟩ ⟨v4, x_v4, h_v4⟩ else hinv hG in EoCases.__eo_to_smt.case_7
  store_step with ih.eo__24eo_5fto_5fsmt_5freserved_5fdatatype_5fname s v1 _ hinv h64 hrem h_v1 as ⟨v5, s1, hinv1, h_v5⟩ growing hG carrying h_v1 h_v2 h_v3 h_v4 dropping h_a0
  have h_ite_v9 := (show if_1_eo__24eo_5fto_5fsmt s1 v5 v2 v1 v3 v4 ⦃ r s' => s'.Inv ∧ s1.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_1_eo__24eo_5fto_5fsmt
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s1
    rcases Store.boolean_value_native h_v5 with ⟨hx_6, hbv_6⟩ | ⟨hx_6, hbv_6⟩
    · ite_branch hbv_6
      step as ⟨e_v6, he_v6⟩
      store_step with CtorSpec.eo__24emb_5fsm_2eNone.construct s1 e_v6 (by rw [he_v6]; exact empty_args) hinv1 h64 as ⟨v6, s2, hinv2, h_v6⟩ growing hG carrying h_v1 h_v2 h_v3 h_v4 dropping h_v5 he_v6 e_v6 v5
      ite_done hinv2 hG with (native_ite_true_rep _ hx_6 h_v6)
    · ite_branch hbv_6
      store_step with ih.eo__24eo_5fto_5fsmt_5fdatatype_5fdecl s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v1 h_v3 h_v4 dropping h_v2 h_v5 hinv1 s1 v2 v5
      step as ⟨e_v8, he_v8⟩
      store_step with CtorSpec.eo__24emb_5fsm_2eDtSel.construct s2 e_v8 (by rw [he_v8]; rfl) h_v1 h_v7 h_v3 h_v4 hinv2 h64 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying dropping h_v1 h_v3 h_v4 h_v7 he_v8 e_v8 v1 v3 v4 v7
      ite_done hinv3 hG with (native_ite_false_rep _ hx_6 h_v8))
  store_step with h_ite_v9 as ⟨v9, s2, hinv2, h_v9⟩ growing hG carrying dropping h_ite_v9 h_v1 h_v2 h_v3 h_v4 h_v5 hinv1 s1 v1 v2 v3 v4 v5
  case_done hinv2 hG with h_v9 in EoCases.__eo_to_smt.case_7 using

theorem case_8_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_8_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_8 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_8 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_8_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fUConst.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__eo_to_smt.case_8
  step as ⟨e_v3, he_v3⟩
  store_step with Store.native_spec_uconst_id s e_v3 (by rw [he_v3]; rfl) h_v1 hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v2 dropping h_a0 h_v1 he_v3 e_v3 v1
  rw [← Bridge.native_uconst_id] at h_v3
  store_step with ih.eo__24eo_5fto_5fsmt_5ftype s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v3 dropping h_v2 hinv1 s1 v2
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eUConst.construct s2 e_v5 (by rw [he_v5]; rfl) h_v3 h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying dropping h_v3 h_v4 he_v5 hinv2 e_v5 s2 v3 v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_to_smt.case_8 using

theorem case_9_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_9_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_9 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_9 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_9_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_9
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_9
  pat_unapply h_v4 as ⟨v7, v8, x_v7, x_v8, h_v7, h_v8, hn_v7, hn_v8⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_9
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_ite.construct s e_v9 (by rw [he_v9]; exact empty_args) hinv h64 as ⟨v9, s1, hinv1, h_v9⟩ growing hG carrying h_v2 h_v5 h_v7 h_v8 dropping h_a0 h_v1 h_v4 he_v9 e_v9 v1 v4
  pat_same v7 v9 with h_v7 h_v9 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_9
  store_step with ih.eo__24eo_5fto_5fsmt s1 v8 _ hinv1 h64 (hG.rem hrem) h_v8 as ⟨v10, s2, hinv2, h_v10⟩ growing hG carrying h_v2 h_v5 dropping h_v7 h_v8 h_v9 hinv1 s1 v7 v8 v9
  store_step with ih.eo__24eo_5fto_5fsmt s2 v5 _ hinv2 h64 (hG.rem hrem) h_v5 as ⟨v11, s3, hinv3, h_v11⟩ growing hG carrying h_v2 h_v10 dropping h_v5 hinv2 s2 v5
  store_step with ih.eo__24eo_5fto_5fsmt s3 v2 _ hinv3 h64 (hG.rem hrem) h_v2 as ⟨v12, s4, hinv4, h_v12⟩ growing hG carrying h_v10 h_v11 dropping h_v2 hinv3 s3 v2
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eite.construct s4 e_v13 (by rw [he_v13]; rfl) h_v10 h_v11 h_v12 hinv4 h64 as ⟨v13, s5, hinv5, h_v13⟩ growing hG carrying dropping h_v10 h_v11 h_v12 he_v13 hinv4 e_v13 s4 v10 v11 v12
  case_done hinv5 hG with h_v13 in EoCases.__eo_to_smt.case_9 using hn_v1 hn_v2 hn_v4 hn_v5 hn_v7 hn_v8

theorem case_10_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_10_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_10 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_10 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_10_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_10
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_not.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v1 h_v2 dropping h_a0 he_v3 e_v3
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_10
  store_step with ih.eo__24eo_5fto_5fsmt s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying dropping h_v1 h_v2 h_v3 hinv1 s1 v1 v2 v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5fsm_2enot.construct s2 e_v5 (by rw [he_v5]; rfl) h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying dropping h_v4 he_v5 hinv2 e_v5 s2 v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_to_smt.case_10 using hn_v1 hn_v2

theorem case_11_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_11_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_11 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_11 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_11_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_11
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_11
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_or.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_11
  store_step with ih.eo__24eo_5fto_5fsmt s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 dropping h_v4 h_v5 h_v6 hinv1 s1 v4 v5 v6
  store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v7 dropping h_v2 hinv2 s2 v2
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eor.construct s3 e_v9 (by rw [he_v9]; rfl) h_v7 h_v8 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying dropping h_v7 h_v8 he_v9 hinv3 e_v9 s3 v7 v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_to_smt.case_11 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_12_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_12_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_12 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_12 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_12_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_12
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_12
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_and.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_12
  store_step with ih.eo__24eo_5fto_5fsmt s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 dropping h_v4 h_v5 h_v6 hinv1 s1 v4 v5 v6
  store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v7 dropping h_v2 hinv2 s2 v2
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eand.construct s3 e_v9 (by rw [he_v9]; rfl) h_v7 h_v8 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying dropping h_v7 h_v8 he_v9 hinv3 e_v9 s3 v7 v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_to_smt.case_12 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_13_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_13_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_13 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_13 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_13_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_13
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_13
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__3d_3e.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_13
  store_step with ih.eo__24eo_5fto_5fsmt s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 dropping h_v4 h_v5 h_v6 hinv1 s1 v4 v5 v6
  store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v7 dropping h_v2 hinv2 s2 v2
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fsm_2e_3d_3e.construct s3 e_v9 (by rw [he_v9]; rfl) h_v7 h_v8 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying dropping h_v7 h_v8 he_v9 hinv3 e_v9 s3 v7 v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_to_smt.case_13 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_14_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_14_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_14 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_14 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_14_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_14
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_14
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_xor.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_14
  store_step with ih.eo__24eo_5fto_5fsmt s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 dropping h_v4 h_v5 h_v6 hinv1 s1 v4 v5 v6
  store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v7 dropping h_v2 hinv2 s2 v2
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fsm_2exor.construct s3 e_v9 (by rw [he_v9]; rfl) h_v7 h_v8 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying dropping h_v7 h_v8 he_v9 hinv3 e_v9 s3 v7 v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_to_smt.case_14 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_15_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_15_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_15 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_15 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_15_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_15
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_15
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__3d.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_15
  store_step with ih.eo__24eo_5fto_5fsmt s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 dropping h_v4 h_v5 h_v6 hinv1 s1 v4 v5 v6
  store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v7 dropping h_v2 hinv2 s2 v2
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fsm_2e_3d.construct s3 e_v9 (by rw [he_v9]; rfl) h_v7 h_v8 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying dropping h_v7 h_v8 he_v9 hinv3 e_v9 s3 v7 v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_to_smt.case_15 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_16_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_16_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_16 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_16 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_16_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_16
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_16
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_lambda.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_16
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo__24emb_5fsbd_2enil.construct s1 e_v7 (by rw [he_v7]; exact empty_args) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 h_v5 dropping h_v4 h_v6 he_v7 hinv1 e_v7 s1 v4 v6
  store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v5 h_v7 dropping h_v2 hinv2 s2 v2
  store_step with ih.eo__24eo_5fto_5fsmt_5flambda_5fcurry s3 v5 v8 _ _ hinv3 h64 (hG.rem hrem) h_v5 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_v7 dropping h_v5 h_v8 hinv3 s3 v5 v8
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo__24emb_5fsm_2ebind.construct s4 e_v10 (by rw [he_v10]; rfl) h_v7 h_v9 hinv4 h64 as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying dropping h_v7 h_v9 he_v10 hinv4 e_v10 s4 v7 v9
  case_done hinv5 hG with h_v10 in EoCases.__eo_to_smt.case_16 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_17_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_17_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_17 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_17 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_17_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_17
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_distinct.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v1 h_v2 dropping h_a0 he_v3 e_v3
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_17
  store_step with ih.eo__24eo_5fto_5fsmt_5ftyped_5flist_5felem_5ftype s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v2 dropping h_v1 h_v3 hinv1 s1 v1 v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s2 e_v5 (by rw [he_v5]; exact empty_args) hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_v2 h_v4 dropping he_v5 hinv2 e_v5 s2
  step as ⟨e_v6, he_v6⟩
  store_step with Store.native_spec_Teq s3 e_v6 (by rw [he_v6]; rfl) h_v4 h_v5 hinv3 h64 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_v2 dropping h_v4 h_v5 he_v6 hinv3 e_v6 s3 v4 v5
  have h_ite_v9 := (show if_2_eo__24eo_5fto_5fsmt s4 v6 v2 ⦃ r s' => s'.Inv ∧ s4.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_2_eo__24eo_5fto_5fsmt
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s4
    rcases Store.boolean_value_native h_v6 with ⟨hx_7, hbv_7⟩ | ⟨hx_7, hbv_7⟩
    · ite_branch hbv_7
      step as ⟨e_v7, he_v7⟩
      store_step with CtorSpec.eo__24emb_5fsm_2eNone.construct s4 e_v7 (by rw [he_v7]; exact empty_args) hinv4 h64 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_v2 dropping h_v6 he_v7 e_v7 v6
      ite_done hinv5 hG with (native_ite_true_rep _ hx_7 h_v7)
    · ite_branch hbv_7
      store_step with ih.eo__24eo_5fto_5fsmt_5fdistinct s4 v2 _ hinv4 h64 (hG.rem hrem) h_v2 as ⟨v8, s5, hinv5, h_v8⟩ growing hG carrying dropping h_v2 h_v6 hinv4 s4 v2 v6
      ite_done hinv5 hG with (native_ite_false_rep _ hx_7 h_v8))
  store_step with h_ite_v9 as ⟨v9, s5, hinv5, h_v9⟩ growing hG carrying dropping h_ite_v9 h_v2 h_v6 hinv4 s4 v2 v6
  case_done hinv5 hG with h_v9 in EoCases.__eo_to_smt.case_17 using hn_v1 hn_v2

theorem case_18_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_18_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_18 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_18 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_18_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_18
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__40purify.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v1 h_v2 dropping h_a0 he_v3 e_v3
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_18
  store_step with ih.eo__24eo_5fto_5fsmt s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying dropping h_v1 h_v2 h_v3 hinv1 s1 v1 v2 v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5fsm_2e_40purify.construct s2 e_v5 (by rw [he_v5]; rfl) h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying dropping h_v4 he_v5 hinv2 e_v5 s2 v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_to_smt.case_18 using hn_v1 hn_v2

theorem case_19_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_19_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_19 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_19 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_19_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_19
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_19
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__2b.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_19
  store_step with ih.eo__24eo_5fto_5fsmt s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 dropping h_v4 h_v5 h_v6 hinv1 s1 v4 v5 v6
  store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v7 dropping h_v2 hinv2 s2 v2
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fsm_2e_2b.construct s3 e_v9 (by rw [he_v9]; rfl) h_v7 h_v8 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying dropping h_v7 h_v8 he_v9 hinv3 e_v9 s3 v7 v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_to_smt.case_19 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_20_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_20_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_20 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_20 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_20_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_20
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_20
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__2d.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_20
  store_step with ih.eo__24eo_5fto_5fsmt s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 dropping h_v4 h_v5 h_v6 hinv1 s1 v4 v5 v6
  store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v7 dropping h_v2 hinv2 s2 v2
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fsm_2e_2d.construct s3 e_v9 (by rw [he_v9]; rfl) h_v7 h_v8 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying dropping h_v7 h_v8 he_v9 hinv3 e_v9 s3 v7 v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_to_smt.case_20 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_21_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_21_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_21 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_21 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_21_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_21
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_21
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__2a.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_21
  store_step with ih.eo__24eo_5fto_5fsmt s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 dropping h_v4 h_v5 h_v6 hinv1 s1 v4 v5 v6
  store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v7 dropping h_v2 hinv2 s2 v2
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fsm_2e_2a.construct s3 e_v9 (by rw [he_v9]; rfl) h_v7 h_v8 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying dropping h_v7 h_v8 he_v9 hinv3 e_v9 s3 v7 v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_to_smt.case_21 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_22_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_22_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_22 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_22 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_22_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_22
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_22
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__3c.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_22
  store_step with ih.eo__24eo_5fto_5fsmt s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 dropping h_v4 h_v5 h_v6 hinv1 s1 v4 v5 v6
  store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v7 dropping h_v2 hinv2 s2 v2
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fsm_2e_3c.construct s3 e_v9 (by rw [he_v9]; rfl) h_v7 h_v8 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying dropping h_v7 h_v8 he_v9 hinv3 e_v9 s3 v7 v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_to_smt.case_22 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_23_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_23_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_23 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_23 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_23_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_23
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_23
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__3c_3d.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_23
  store_step with ih.eo__24eo_5fto_5fsmt s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 dropping h_v4 h_v5 h_v6 hinv1 s1 v4 v5 v6
  store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v7 dropping h_v2 hinv2 s2 v2
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fsm_2e_3c_3d.construct s3 e_v9 (by rw [he_v9]; rfl) h_v7 h_v8 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying dropping h_v7 h_v8 he_v9 hinv3 e_v9 s3 v7 v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_to_smt.case_23 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_24_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_24_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_24 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_24 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_24_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_24
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_24
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__3e.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_24
  store_step with ih.eo__24eo_5fto_5fsmt s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 dropping h_v4 h_v5 h_v6 hinv1 s1 v4 v5 v6
  store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v7 dropping h_v2 hinv2 s2 v2
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fsm_2e_3e.construct s3 e_v9 (by rw [he_v9]; rfl) h_v7 h_v8 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying dropping h_v7 h_v8 he_v9 hinv3 e_v9 s3 v7 v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_to_smt.case_24 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_25_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_25_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_25 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_25 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_25_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_25
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_25
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__3e_3d.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_25
  store_step with ih.eo__24eo_5fto_5fsmt s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 dropping h_v4 h_v5 h_v6 hinv1 s1 v4 v5 v6
  store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v7 dropping h_v2 hinv2 s2 v2
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fsm_2e_3e_3d.construct s3 e_v9 (by rw [he_v9]; rfl) h_v7 h_v8 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying dropping h_v7 h_v8 he_v9 hinv3 e_v9 s3 v7 v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_to_smt.case_25 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_26_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_26_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_26 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_26 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_26_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_26
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_to_5freal.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v1 h_v2 dropping h_a0 he_v3 e_v3
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_26
  store_step with ih.eo__24eo_5fto_5fsmt s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying dropping h_v1 h_v2 h_v3 hinv1 s1 v1 v2 v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eto_5freal.construct s2 e_v5 (by rw [he_v5]; rfl) h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying dropping h_v4 he_v5 hinv2 e_v5 s2 v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_to_smt.case_26 using hn_v1 hn_v2

theorem case_27_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_27_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_27 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_27 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_27_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_27
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_to_5fint.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v1 h_v2 dropping h_a0 he_v3 e_v3
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_27
  store_step with ih.eo__24eo_5fto_5fsmt s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying dropping h_v1 h_v2 h_v3 hinv1 s1 v1 v2 v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eto_5fint.construct s2 e_v5 (by rw [he_v5]; rfl) h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying dropping h_v4 he_v5 hinv2 e_v5 s2 v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_to_smt.case_27 using hn_v1 hn_v2

theorem case_28_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_28_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_28 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_28 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_28_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_28
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_is_5fint.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v1 h_v2 dropping h_a0 he_v3 e_v3
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_28
  store_step with ih.eo__24eo_5fto_5fsmt s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying dropping h_v1 h_v2 h_v3 hinv1 s1 v1 v2 v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eis_5fint.construct s2 e_v5 (by rw [he_v5]; rfl) h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying dropping h_v4 he_v5 hinv2 e_v5 s2 v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_to_smt.case_28 using hn_v1 hn_v2

theorem case_29_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_29_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_29 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_29 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_29_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_29
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_abs.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v1 h_v2 dropping h_a0 he_v3 e_v3
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_29
  store_step with ih.eo__24eo_5fto_5fsmt s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying dropping h_v1 h_v2 h_v3 hinv1 s1 v1 v2 v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eabs.construct s2 e_v5 (by rw [he_v5]; rfl) h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying dropping h_v4 he_v5 hinv2 e_v5 s2 v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_to_smt.case_29 using hn_v1 hn_v2

theorem case_30_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_30_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_30 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_30 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_30_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_30
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__24eoo_5f_2d_2e2.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v1 h_v2 dropping h_a0 he_v3 e_v3
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_30
  store_step with ih.eo__24eo_5fto_5fsmt s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying dropping h_v1 h_v2 h_v3 hinv1 s1 v1 v2 v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5fsm_2euneg.construct s2 e_v5 (by rw [he_v5]; rfl) h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying dropping h_v4 he_v5 hinv2 e_v5 s2 v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_to_smt.case_30 using hn_v1 hn_v2

theorem case_31_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_31_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_31 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_31 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_31_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_31
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_31
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_div.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_31
  store_step with ih.eo__24eo_5fto_5fsmt s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 dropping h_v4 h_v5 h_v6 hinv1 s1 v4 v5 v6
  store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v7 dropping h_v2 hinv2 s2 v2
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fsm_2ediv.construct s3 e_v9 (by rw [he_v9]; rfl) h_v7 h_v8 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying dropping h_v7 h_v8 he_v9 hinv3 e_v9 s3 v7 v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_to_smt.case_31 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_32_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_32_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_32 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_32 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_32_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_32
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_32
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_mod.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_32
  store_step with ih.eo__24eo_5fto_5fsmt s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 dropping h_v4 h_v5 h_v6 hinv1 s1 v4 v5 v6
  store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v7 dropping h_v2 hinv2 s2 v2
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fsm_2emod.construct s3 e_v9 (by rw [he_v9]; rfl) h_v7 h_v8 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying dropping h_v7 h_v8 he_v9 hinv3 e_v9 s3 v7 v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_to_smt.case_32 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_33_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_33_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_33 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_33 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_33_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_33
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_33
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_divisible.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_33
  store_step with ih.eo__24eo_5fto_5fsmt s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 dropping h_v4 h_v5 h_v6 hinv1 s1 v4 v5 v6
  store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v7 dropping h_v2 hinv2 s2 v2
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fsm_2edivisible.construct s3 e_v9 (by rw [he_v9]; rfl) h_v7 h_v8 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying dropping h_v7 h_v8 he_v9 hinv3 e_v9 s3 v7 v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_to_smt.case_33 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_34_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_34_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_34 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_34 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_34_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_34
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_int_2epow2.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v1 h_v2 dropping h_a0 he_v3 e_v3
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_34
  store_step with ih.eo__24eo_5fto_5fsmt s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying dropping h_v1 h_v2 h_v3 hinv1 s1 v1 v2 v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eint_2epow2.construct s2 e_v5 (by rw [he_v5]; rfl) h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying dropping h_v4 he_v5 hinv2 e_v5 s2 v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_to_smt.case_34 using hn_v1 hn_v2

theorem case_35_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_35_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_35 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_35 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_35_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_35
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_int_2elog2.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v1 h_v2 dropping h_a0 he_v3 e_v3
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_35
  store_step with ih.eo__24eo_5fto_5fsmt s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying dropping h_v1 h_v2 h_v3 hinv1 s1 v1 v2 v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eint_2elog2.construct s2 e_v5 (by rw [he_v5]; rfl) h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying dropping h_v4 he_v5 hinv2 e_v5 s2 v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_to_smt.case_35 using hn_v1 hn_v2

theorem case_36_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_36_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_36 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_36 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_36_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_36
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_int_2eispow2.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v1 h_v2 dropping h_a0 he_v3 e_v3
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_36
  store_step with ih.eo__24eo_5fto_5fsmt s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v2 dropping h_v1 h_v3 hinv1 s1 v1 v3
  simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.raw_int_u32_spec s2 0#u32 (0) (by scalar_tac) hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_v2 h_v4 dropping hinv2 s2
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eNumeral.construct s3 e_v6 (by rw [he_v6]; rfl) h_v5 hinv3 h64 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_v2 h_v4 dropping h_v5 he_v6 hinv3 e_v6 s3 v5
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo__24emb_5fsm_2e_3e_3d.construct s4 e_v7 (by rw [he_v7]; rfl) h_v4 h_v6 hinv4 h64 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_v2 dropping h_v4 h_v6 he_v7 hinv4 e_v7 s4 v4 v6
  store_step with ih.eo__24eo_5fto_5fsmt s5 v2 _ hinv5 h64 (hG.rem hrem) h_v2 as ⟨v8, s6, hinv6, h_v8⟩ growing hG carrying h_v2 h_v7 dropping hinv5 s5
  store_step with ih.eo__24eo_5fto_5fsmt s6 v2 _ hinv6 h64 (hG.rem hrem) h_v2 as ⟨v9, s7, hinv7, h_v9⟩ growing hG carrying h_v7 h_v8 dropping h_v2 hinv6 s6 v2
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eint_2elog2.construct s7 e_v10 (by rw [he_v10]; rfl) h_v9 hinv7 h64 as ⟨v10, s8, hinv8, h_v10⟩ growing hG carrying h_v7 h_v8 dropping h_v9 he_v10 hinv7 e_v10 s7 v9
  step as ⟨e_v11, he_v11⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eint_2epow2.construct s8 e_v11 (by rw [he_v11]; rfl) h_v10 hinv8 h64 as ⟨v11, s9, hinv9, h_v11⟩ growing hG carrying h_v7 h_v8 dropping h_v10 he_v11 hinv8 e_v11 s8 v10
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo__24emb_5fsm_2e_3d.construct s9 e_v12 (by rw [he_v12]; rfl) h_v8 h_v11 hinv9 h64 as ⟨v12, s10, hinv10, h_v12⟩ growing hG carrying h_v7 dropping h_v11 h_v8 he_v12 hinv9 e_v12 s9 v11 v8
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eand.construct s10 e_v13 (by rw [he_v13]; rfl) h_v7 h_v12 hinv10 h64 as ⟨v13, s11, hinv11, h_v13⟩ growing hG carrying dropping h_v12 h_v7 he_v13 hinv10 e_v13 s10 v12 v7
  case_done hinv11 hG with h_v13 in EoCases.__eo_to_smt.case_36 using hn_v1 hn_v2

theorem case_37_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_37_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_37 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_37 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_37_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_37
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_37
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_div_5ftotal.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_37
  store_step with ih.eo__24eo_5fto_5fsmt s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 dropping h_v4 h_v5 h_v6 hinv1 s1 v4 v5 v6
  store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v7 dropping h_v2 hinv2 s2 v2
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fsm_2ediv_5ftotal.construct s3 e_v9 (by rw [he_v9]; rfl) h_v7 h_v8 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying dropping h_v7 h_v8 he_v9 hinv3 e_v9 s3 v7 v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_to_smt.case_37 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_38_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_38_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_38 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_38 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_38_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_38
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_38
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_mod_5ftotal.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_38
  store_step with ih.eo__24eo_5fto_5fsmt s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 dropping h_v4 h_v5 h_v6 hinv1 s1 v4 v5 v6
  store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v7 dropping h_v2 hinv2 s2 v2
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fsm_2emod_5ftotal.construct s3 e_v9 (by rw [he_v9]; rfl) h_v7 h_v8 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying dropping h_v7 h_v8 he_v9 hinv3 e_v9 s3 v7 v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_to_smt.case_38 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_39_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_39_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_39 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_39 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_39_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_39
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__40int_5fdiv_5fby_5fzero.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v1 h_v2 dropping h_a0 he_v3 e_v3
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_39
  store_step with ih.eo__24eo_5fto_5fsmt s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying dropping h_v1 h_v2 h_v3 hinv1 s1 v1 v2 v3
  simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.raw_int_u32_spec s2 0#u32 (0) (by scalar_tac) hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_v4 dropping hinv2 s2
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eNumeral.construct s3 e_v6 (by rw [he_v6]; rfl) h_v5 hinv3 h64 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_v4 dropping h_v5 he_v6 hinv3 e_v6 s3 v5
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo__24emb_5fsm_2ediv.construct s4 e_v7 (by rw [he_v7]; rfl) h_v4 h_v6 hinv4 h64 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying dropping h_v4 h_v6 he_v7 hinv4 e_v7 s4 v4 v6
  case_done hinv5 hG with h_v7 in EoCases.__eo_to_smt.case_39 using hn_v1 hn_v2

theorem case_40_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_40_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_40 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_40 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_40_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_40
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__40mod_5fby_5fzero.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v1 h_v2 dropping h_a0 he_v3 e_v3
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_40
  store_step with ih.eo__24eo_5fto_5fsmt s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying dropping h_v1 h_v2 h_v3 hinv1 s1 v1 v2 v3
  simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.raw_int_u32_spec s2 0#u32 (0) (by scalar_tac) hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_v4 dropping hinv2 s2
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eNumeral.construct s3 e_v6 (by rw [he_v6]; rfl) h_v5 hinv3 h64 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_v4 dropping h_v5 he_v6 hinv3 e_v6 s3 v5
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo__24emb_5fsm_2emod.construct s4 e_v7 (by rw [he_v7]; rfl) h_v4 h_v6 hinv4 h64 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying dropping h_v4 h_v6 he_v7 hinv4 e_v7 s4 v4 v6
  case_done hinv5 hG with h_v7 in EoCases.__eo_to_smt.case_40 using hn_v1 hn_v2

theorem case_41_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_41_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_41 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_41 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_41_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_41
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_41
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_select.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_41
  store_step with ih.eo__24eo_5fto_5fsmt s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 dropping h_v4 h_v5 h_v6 hinv1 s1 v4 v5 v6
  store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v7 dropping h_v2 hinv2 s2 v2
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eselect.construct s3 e_v9 (by rw [he_v9]; rfl) h_v7 h_v8 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying dropping h_v7 h_v8 he_v9 hinv3 e_v9 s3 v7 v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_to_smt.case_41 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_42_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_42_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_42 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_42 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_42_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_42
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_42
  pat_unapply h_v4 as ⟨v7, v8, x_v7, x_v8, h_v7, h_v8, hn_v7, hn_v8⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_42
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_store.construct s e_v9 (by rw [he_v9]; exact empty_args) hinv h64 as ⟨v9, s1, hinv1, h_v9⟩ growing hG carrying h_v2 h_v5 h_v7 h_v8 dropping h_a0 h_v1 h_v4 he_v9 e_v9 v1 v4
  pat_same v7 v9 with h_v7 h_v9 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_42
  store_step with ih.eo__24eo_5fto_5fsmt s1 v8 _ hinv1 h64 (hG.rem hrem) h_v8 as ⟨v10, s2, hinv2, h_v10⟩ growing hG carrying h_v2 h_v5 dropping h_v7 h_v8 h_v9 hinv1 s1 v7 v8 v9
  store_step with ih.eo__24eo_5fto_5fsmt s2 v5 _ hinv2 h64 (hG.rem hrem) h_v5 as ⟨v11, s3, hinv3, h_v11⟩ growing hG carrying h_v2 h_v10 dropping h_v5 hinv2 s2 v5
  store_step with ih.eo__24eo_5fto_5fsmt s3 v2 _ hinv3 h64 (hG.rem hrem) h_v2 as ⟨v12, s4, hinv4, h_v12⟩ growing hG carrying h_v10 h_v11 dropping h_v2 hinv3 s3 v2
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo__24emb_5fsm_2estore.construct s4 e_v13 (by rw [he_v13]; rfl) h_v10 h_v11 h_v12 hinv4 h64 as ⟨v13, s5, hinv5, h_v13⟩ growing hG carrying dropping h_v10 h_v11 h_v12 he_v13 hinv4 e_v13 s4 v10 v11 v12
  case_done hinv5 hG with h_v13 in EoCases.__eo_to_smt.case_42 using hn_v1 hn_v2 hn_v4 hn_v5 hn_v7 hn_v8

theorem case_43_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_43_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_43 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_43 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_43_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_43
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_43
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__40array_5fdeq_5fdiff.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_43
  store_step with ih.eo__24eo_5fto_5fsmt s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 h_v5 dropping h_v4 h_v6 hinv1 s1 v4 v6
  store_step with ih.eo__24eo_5fto_5fsmt s2 v5 _ hinv2 h64 (hG.rem hrem) h_v5 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v2 h_v7 dropping h_v5 hinv2 s2 v5
  store_step with ih.eo__24smtx_5ftypeof s3 v8 _ hinv3 h64 (hG.rem hrem) h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_v2 h_v7 dropping h_v8 hinv3 s3 v8
  store_step with ih.eo__24eo_5fto_5fsmt s4 v2 _ hinv4 h64 (hG.rem hrem) h_v2 as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_v2 h_v7 h_v9 dropping hinv4 s4
  store_step with ih.eo__24eo_5fto_5fsmt s5 v2 _ hinv5 h64 (hG.rem hrem) h_v2 as ⟨v11, s6, hinv6, h_v11⟩ growing hG carrying h_v7 h_v9 h_v10 dropping h_v2 hinv5 s5 v2
  store_step with ih.eo__24smtx_5ftypeof s6 v11 _ hinv6 h64 (hG.rem hrem) h_v11 as ⟨v12, s7, hinv7, h_v12⟩ growing hG carrying h_v7 h_v9 h_v10 dropping h_v11 hinv6 s6 v11
  store_step with ih.eo__24eo_5fto_5fsmt_5farray_5fdeq_5fdiff s7 v7 v9 v10 v12 _ _ _ _ hinv7 h64 (hG.rem hrem) h_v7 h_v9 h_v10 h_v12 as ⟨v13, s8, hinv8, h_v13⟩ growing hG carrying dropping h_v10 h_v12 h_v7 h_v9 hinv7 s7 v10 v12 v7 v9
  case_done hinv8 hG with h_v13 in EoCases.__eo_to_smt.case_43 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_44_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_44_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_44 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_44 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_44_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_44
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__40bvsize.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v1 h_v2 dropping h_a0 he_v3 e_v3
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_44
  simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.raw_int_u32_spec s1 0#u32 (0) (by scalar_tac) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v2 dropping h_v1 h_v3 hinv1 s1 v1 v3
  store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_v2 h_v4 dropping hinv2 s2
  store_step with ih.eo__24smtx_5ftypeof s3 v5 _ hinv3 h64 (hG.rem hrem) h_v5 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_v2 h_v4 dropping h_v5 hinv3 s3 v5
  store_step with ih.eo__24eo_5fto_5fsmt_5fbv_5fsize s4 v6 _ hinv4 h64 (hG.rem hrem) h_v6 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_v2 h_v4 dropping h_v6 hinv4 s4 v6
  step as ⟨e_v8, he_v8⟩
  store_step with Store.native_spec_zleq s5 e_v8 (by rw [he_v8]; rfl) h_v4 h_v7 hinv5 h64 as ⟨v8, s6, hinv6, h_v8⟩ growing hG carrying h_v2 dropping h_v4 h_v7 he_v8 hinv5 e_v8 s5 v4 v7
  rw [← Bridge.native_zleq] at h_v8
  have h_ite_v15 := (show if_4_eo__24eo_5fto_5fsmt s6 v8 v2 ⦃ r s' => s'.Inv ∧ s6.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_4_eo__24eo_5fto_5fsmt
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s6
    rcases Store.boolean_value_native h_v8 with ⟨hx_9, hbv_9⟩ | ⟨hx_9, hbv_9⟩
    · ite_branch hbv_9
      store_step with ih.eo__24eo_5fto_5fsmt s6 v2 _ hinv6 h64 (hG.rem hrem) h_v2 as ⟨v9, s7, hinv7, h_v9⟩ growing hG carrying dropping h_v2 h_v8 v2 v8
      store_step with ih.eo__24smtx_5ftypeof s7 v9 _ hinv7 h64 (hG.rem hrem) h_v9 as ⟨v10, s8, hinv8, h_v10⟩ growing hG carrying dropping h_v9 v9
      store_step with ih.eo__24eo_5fto_5fsmt_5fbv_5fsize s8 v10 _ hinv8 h64 (hG.rem hrem) h_v10 as ⟨v11, s9, hinv9, h_v11⟩ growing hG carrying dropping h_v10 hinv8 s8 v10
      step as ⟨e_v12, he_v12⟩
      store_step with CtorSpec.eo__24emb_5fsm_2eNumeral.construct s9 e_v12 (by rw [he_v12]; rfl) h_v11 hinv9 h64 as ⟨v12, s10, hinv10, h_v12⟩ growing hG carrying dropping h_v11 he_v12 hinv9 e_v12 s9 v11
      step as ⟨e_v13, he_v13⟩
      store_step with CtorSpec.eo__24emb_5fsm_2e_40purify.construct s10 e_v13 (by rw [he_v13]; rfl) h_v12 hinv10 h64 as ⟨v13, s11, hinv11, h_v13⟩ growing hG carrying dropping h_v12 he_v13 hinv10 e_v13 s10 v12
      ite_done hinv11 hG with (native_ite_true_rep _ hx_9 h_v13)
    · ite_branch hbv_9
      step as ⟨e_v14, he_v14⟩
      store_step with CtorSpec.eo__24emb_5fsm_2eNone.construct s6 e_v14 (by rw [he_v14]; exact empty_args) hinv6 h64 as ⟨v14, s7, hinv7, h_v14⟩ growing hG carrying dropping h_v2 h_v8 he_v14 hinv6 e_v14 s6 v2 v8
      ite_done hinv7 hG with (native_ite_false_rep _ hx_9 h_v14))
  store_step with h_ite_v15 as ⟨v15, s7, hinv7, h_v15⟩ growing hG carrying dropping h_ite_v15 h_v2 h_v8 hinv6 s6 v2 v8
  case_done hinv7 hG with h_v15 in EoCases.__eo_to_smt.case_44 using hn_v1 hn_v2

theorem case_45_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_45_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_45 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_45 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_45_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_45
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_45
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_concat.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_45
  store_step with ih.eo__24eo_5fto_5fsmt s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 dropping h_v4 h_v5 h_v6 hinv1 s1 v4 v5 v6
  store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v7 dropping h_v2 hinv2 s2 v2
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fsm_2econcat.construct s3 e_v9 (by rw [he_v9]; rfl) h_v7 h_v8 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying dropping h_v7 h_v8 he_v9 hinv3 e_v9 s3 v7 v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_to_smt.case_45 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_46_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_46_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_46 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_46 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_46_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_46
  pat_destruct CtorSpec.eo_extract.destruct h_v1 as ⟨v4, x_v4, h_v4⟩ ⟨v5, x_v5, h_v5⟩ else hinv hG in EoCases.__eo_to_smt.case_46
  obtain ⟨hn_v4, hn_v5⟩ := CtorSpec.eo_extract.fields_ne_stuck hinv h_v1
  store_step with ih.eo__24eo_5fto_5fsmt s v4 _ hinv h64 hrem h_v4 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v5 dropping h_a0 h_v1 h_v4 v1 v4
  store_step with ih.eo__24eo_5fto_5fsmt s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 h_v6 dropping h_v5 hinv1 s1 v5
  store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v6 h_v7 dropping h_v2 hinv2 s2 v2
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eextract.construct s3 e_v9 (by rw [he_v9]; rfl) h_v6 h_v7 h_v8 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying dropping h_v6 h_v7 h_v8 he_v9 hinv3 e_v9 s3 v6 v7 v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_to_smt.case_46 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_47_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_47_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_47 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_47 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_47_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_47
  pat_destruct CtorSpec.eo_repeat.destruct h_v1 as ⟨v4, x_v4, h_v4⟩ else hinv hG in EoCases.__eo_to_smt.case_47
  obtain hn_v4 := CtorSpec.eo_repeat.fields_ne_stuck hinv h_v1
  store_step with ih.eo__24eo_5fto_5fsmt s v4 _ hinv h64 hrem h_v4 as ⟨v5, s1, hinv1, h_v5⟩ growing hG carrying h_v2 dropping h_a0 h_v1 h_v4 v1 v4
  store_step with ih.eo__24eo_5fto_5fsmt s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v6, s2, hinv2, h_v6⟩ growing hG carrying h_v5 dropping h_v2 hinv1 s1 v2
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo__24emb_5fsm_2erepeat.construct s2 e_v7 (by rw [he_v7]; rfl) h_v5 h_v6 hinv2 h64 as ⟨v7, s3, hinv3, h_v7⟩ growing hG carrying dropping h_v5 h_v6 he_v7 hinv2 e_v7 s2 v5 v6
  case_done hinv3 hG with h_v7 in EoCases.__eo_to_smt.case_47 using hn_v1 hn_v2 hn_v4

theorem case_48_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_48_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_48 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_48 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_48_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_48
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_bvnot.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v1 h_v2 dropping h_a0 he_v3 e_v3
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_48
  store_step with ih.eo__24eo_5fto_5fsmt s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying dropping h_v1 h_v2 h_v3 hinv1 s1 v1 v2 v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5fsm_2ebvnot.construct s2 e_v5 (by rw [he_v5]; rfl) h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying dropping h_v4 he_v5 hinv2 e_v5 s2 v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_to_smt.case_48 using hn_v1 hn_v2

theorem case_49_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_49_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_49 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_49 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_49_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_49
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_49
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_bvand.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_49
  store_step with ih.eo__24eo_5fto_5fsmt s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 dropping h_v4 h_v5 h_v6 hinv1 s1 v4 v5 v6
  store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v7 dropping h_v2 hinv2 s2 v2
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fsm_2ebvand.construct s3 e_v9 (by rw [he_v9]; rfl) h_v7 h_v8 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying dropping h_v7 h_v8 he_v9 hinv3 e_v9 s3 v7 v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_to_smt.case_49 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_50_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_50_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_50 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_50 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_50_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_50
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_50
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_bvor.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_50
  store_step with ih.eo__24eo_5fto_5fsmt s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 dropping h_v4 h_v5 h_v6 hinv1 s1 v4 v5 v6
  store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v7 dropping h_v2 hinv2 s2 v2
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fsm_2ebvor.construct s3 e_v9 (by rw [he_v9]; rfl) h_v7 h_v8 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying dropping h_v7 h_v8 he_v9 hinv3 e_v9 s3 v7 v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_to_smt.case_50 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_51_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_51_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_51 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_51 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_51_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_51
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_51
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_bvnand.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_51
  store_step with ih.eo__24eo_5fto_5fsmt s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 dropping h_v4 h_v5 h_v6 hinv1 s1 v4 v5 v6
  store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v7 dropping h_v2 hinv2 s2 v2
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fsm_2ebvnand.construct s3 e_v9 (by rw [he_v9]; rfl) h_v7 h_v8 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying dropping h_v7 h_v8 he_v9 hinv3 e_v9 s3 v7 v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_to_smt.case_51 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_52_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_52_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_52 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_52 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_52_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_52
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_52
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_bvnor.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_52
  store_step with ih.eo__24eo_5fto_5fsmt s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 dropping h_v4 h_v5 h_v6 hinv1 s1 v4 v5 v6
  store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v7 dropping h_v2 hinv2 s2 v2
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fsm_2ebvnor.construct s3 e_v9 (by rw [he_v9]; rfl) h_v7 h_v8 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying dropping h_v7 h_v8 he_v9 hinv3 e_v9 s3 v7 v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_to_smt.case_52 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_53_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_53_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_53 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_53 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_53_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_53
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_53
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_bvxor.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_53
  store_step with ih.eo__24eo_5fto_5fsmt s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 dropping h_v4 h_v5 h_v6 hinv1 s1 v4 v5 v6
  store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v7 dropping h_v2 hinv2 s2 v2
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fsm_2ebvxor.construct s3 e_v9 (by rw [he_v9]; rfl) h_v7 h_v8 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying dropping h_v7 h_v8 he_v9 hinv3 e_v9 s3 v7 v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_to_smt.case_53 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_54_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_54_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_54 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_54 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_54_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_54
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_54
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_bvxnor.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_54
  store_step with ih.eo__24eo_5fto_5fsmt s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 dropping h_v4 h_v5 h_v6 hinv1 s1 v4 v5 v6
  store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v7 dropping h_v2 hinv2 s2 v2
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fsm_2ebvxnor.construct s3 e_v9 (by rw [he_v9]; rfl) h_v7 h_v8 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying dropping h_v7 h_v8 he_v9 hinv3 e_v9 s3 v7 v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_to_smt.case_54 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_55_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_55_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_55 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_55 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_55_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_55
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_55
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_bvcomp.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_55
  store_step with ih.eo__24eo_5fto_5fsmt s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 dropping h_v4 h_v5 h_v6 hinv1 s1 v4 v5 v6
  store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v7 dropping h_v2 hinv2 s2 v2
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fsm_2ebvcomp.construct s3 e_v9 (by rw [he_v9]; rfl) h_v7 h_v8 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying dropping h_v7 h_v8 he_v9 hinv3 e_v9 s3 v7 v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_to_smt.case_55 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_56_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_56_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_56 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_56 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_56_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_56
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_bvneg.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v1 h_v2 dropping h_a0 he_v3 e_v3
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_56
  store_step with ih.eo__24eo_5fto_5fsmt s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying dropping h_v1 h_v2 h_v3 hinv1 s1 v1 v2 v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5fsm_2ebvneg.construct s2 e_v5 (by rw [he_v5]; rfl) h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying dropping h_v4 he_v5 hinv2 e_v5 s2 v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_to_smt.case_56 using hn_v1 hn_v2

theorem case_57_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_57_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_57 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_57 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_57_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_57
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_57
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_bvadd.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_57
  store_step with ih.eo__24eo_5fto_5fsmt s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 dropping h_v4 h_v5 h_v6 hinv1 s1 v4 v5 v6
  store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v7 dropping h_v2 hinv2 s2 v2
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fsm_2ebvadd.construct s3 e_v9 (by rw [he_v9]; rfl) h_v7 h_v8 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying dropping h_v7 h_v8 he_v9 hinv3 e_v9 s3 v7 v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_to_smt.case_57 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_58_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_58_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_58 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_58 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_58_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_58
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_58
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_bvmul.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_58
  store_step with ih.eo__24eo_5fto_5fsmt s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 dropping h_v4 h_v5 h_v6 hinv1 s1 v4 v5 v6
  store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v7 dropping h_v2 hinv2 s2 v2
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fsm_2ebvmul.construct s3 e_v9 (by rw [he_v9]; rfl) h_v7 h_v8 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying dropping h_v7 h_v8 he_v9 hinv3 e_v9 s3 v7 v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_to_smt.case_58 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_59_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_59_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_59 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_59 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_59_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_59
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_59
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_bvudiv.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_59
  store_step with ih.eo__24eo_5fto_5fsmt s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 dropping h_v4 h_v5 h_v6 hinv1 s1 v4 v5 v6
  store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v7 dropping h_v2 hinv2 s2 v2
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fsm_2ebvudiv.construct s3 e_v9 (by rw [he_v9]; rfl) h_v7 h_v8 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying dropping h_v7 h_v8 he_v9 hinv3 e_v9 s3 v7 v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_to_smt.case_59 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_60_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_60_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_60 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_60 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_60_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_60
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_60
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_bvurem.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_60
  store_step with ih.eo__24eo_5fto_5fsmt s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 dropping h_v4 h_v5 h_v6 hinv1 s1 v4 v5 v6
  store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v7 dropping h_v2 hinv2 s2 v2
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fsm_2ebvurem.construct s3 e_v9 (by rw [he_v9]; rfl) h_v7 h_v8 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying dropping h_v7 h_v8 he_v9 hinv3 e_v9 s3 v7 v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_to_smt.case_60 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_61_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_61_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_61 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_61 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_61_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_61
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_61
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_bvsub.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_61
  store_step with ih.eo__24eo_5fto_5fsmt s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 dropping h_v4 h_v5 h_v6 hinv1 s1 v4 v5 v6
  store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v7 dropping h_v2 hinv2 s2 v2
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fsm_2ebvsub.construct s3 e_v9 (by rw [he_v9]; rfl) h_v7 h_v8 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying dropping h_v7 h_v8 he_v9 hinv3 e_v9 s3 v7 v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_to_smt.case_61 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_62_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_62_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_62 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_62 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_62_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_62
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_62
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_bvsdiv.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_62
  store_step with ih.eo__24eo_5fto_5fsmt s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 dropping h_v4 h_v5 h_v6 hinv1 s1 v4 v5 v6
  store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v7 dropping h_v2 hinv2 s2 v2
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fsm_2ebvsdiv.construct s3 e_v9 (by rw [he_v9]; rfl) h_v7 h_v8 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying dropping h_v7 h_v8 he_v9 hinv3 e_v9 s3 v7 v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_to_smt.case_62 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_63_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_63_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_63 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_63 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_63_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_63
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_63
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_bvsrem.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_63
  store_step with ih.eo__24eo_5fto_5fsmt s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 dropping h_v4 h_v5 h_v6 hinv1 s1 v4 v5 v6
  store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v7 dropping h_v2 hinv2 s2 v2
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fsm_2ebvsrem.construct s3 e_v9 (by rw [he_v9]; rfl) h_v7 h_v8 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying dropping h_v7 h_v8 he_v9 hinv3 e_v9 s3 v7 v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_to_smt.case_63 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_64_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_64_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_64 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_64 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_64_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_64
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_64
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_bvsmod.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_64
  store_step with ih.eo__24eo_5fto_5fsmt s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 dropping h_v4 h_v5 h_v6 hinv1 s1 v4 v5 v6
  store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v7 dropping h_v2 hinv2 s2 v2
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fsm_2ebvsmod.construct s3 e_v9 (by rw [he_v9]; rfl) h_v7 h_v8 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying dropping h_v7 h_v8 he_v9 hinv3 e_v9 s3 v7 v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_to_smt.case_64 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_65_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_65_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_65 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_65 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_65_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_65
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_65
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_bvult.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_65
  store_step with ih.eo__24eo_5fto_5fsmt s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 dropping h_v4 h_v5 h_v6 hinv1 s1 v4 v5 v6
  store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v7 dropping h_v2 hinv2 s2 v2
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fsm_2ebvult.construct s3 e_v9 (by rw [he_v9]; rfl) h_v7 h_v8 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying dropping h_v7 h_v8 he_v9 hinv3 e_v9 s3 v7 v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_to_smt.case_65 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_66_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_66_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_66 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_66 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_66_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_66
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_66
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_bvule.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_66
  store_step with ih.eo__24eo_5fto_5fsmt s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 dropping h_v4 h_v5 h_v6 hinv1 s1 v4 v5 v6
  store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v7 dropping h_v2 hinv2 s2 v2
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fsm_2ebvule.construct s3 e_v9 (by rw [he_v9]; rfl) h_v7 h_v8 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying dropping h_v7 h_v8 he_v9 hinv3 e_v9 s3 v7 v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_to_smt.case_66 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_67_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_67_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_67 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_67 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_67_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_67
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_67
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_bvugt.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_67
  store_step with ih.eo__24eo_5fto_5fsmt s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 dropping h_v4 h_v5 h_v6 hinv1 s1 v4 v5 v6
  store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v7 dropping h_v2 hinv2 s2 v2
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fsm_2ebvugt.construct s3 e_v9 (by rw [he_v9]; rfl) h_v7 h_v8 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying dropping h_v7 h_v8 he_v9 hinv3 e_v9 s3 v7 v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_to_smt.case_67 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_68_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_68_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_68 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_68 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_68_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_68
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_68
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_bvuge.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_68
  store_step with ih.eo__24eo_5fto_5fsmt s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 dropping h_v4 h_v5 h_v6 hinv1 s1 v4 v5 v6
  store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v7 dropping h_v2 hinv2 s2 v2
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fsm_2ebvuge.construct s3 e_v9 (by rw [he_v9]; rfl) h_v7 h_v8 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying dropping h_v7 h_v8 he_v9 hinv3 e_v9 s3 v7 v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_to_smt.case_68 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_69_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_69_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_69 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_69 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_69_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_69
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_69
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_bvslt.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_69
  store_step with ih.eo__24eo_5fto_5fsmt s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 dropping h_v4 h_v5 h_v6 hinv1 s1 v4 v5 v6
  store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v7 dropping h_v2 hinv2 s2 v2
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fsm_2ebvslt.construct s3 e_v9 (by rw [he_v9]; rfl) h_v7 h_v8 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying dropping h_v7 h_v8 he_v9 hinv3 e_v9 s3 v7 v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_to_smt.case_69 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_70_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_70_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_70 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_70 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_70_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_70
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_70
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_bvsle.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_70
  store_step with ih.eo__24eo_5fto_5fsmt s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 dropping h_v4 h_v5 h_v6 hinv1 s1 v4 v5 v6
  store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v7 dropping h_v2 hinv2 s2 v2
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fsm_2ebvsle.construct s3 e_v9 (by rw [he_v9]; rfl) h_v7 h_v8 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying dropping h_v7 h_v8 he_v9 hinv3 e_v9 s3 v7 v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_to_smt.case_70 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_71_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_71_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_71 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_71 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_71_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_71
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_71
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_bvsgt.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_71
  store_step with ih.eo__24eo_5fto_5fsmt s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 dropping h_v4 h_v5 h_v6 hinv1 s1 v4 v5 v6
  store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v7 dropping h_v2 hinv2 s2 v2
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fsm_2ebvsgt.construct s3 e_v9 (by rw [he_v9]; rfl) h_v7 h_v8 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying dropping h_v7 h_v8 he_v9 hinv3 e_v9 s3 v7 v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_to_smt.case_71 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_72_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_72_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_72 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_72 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_72_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_72
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_72
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_bvsge.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_72
  store_step with ih.eo__24eo_5fto_5fsmt s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 dropping h_v4 h_v5 h_v6 hinv1 s1 v4 v5 v6
  store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v7 dropping h_v2 hinv2 s2 v2
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fsm_2ebvsge.construct s3 e_v9 (by rw [he_v9]; rfl) h_v7 h_v8 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying dropping h_v7 h_v8 he_v9 hinv3 e_v9 s3 v7 v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_to_smt.case_72 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_73_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_73_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_73 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_73 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_73_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_73
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_73
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_bvshl.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_73
  store_step with ih.eo__24eo_5fto_5fsmt s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 dropping h_v4 h_v5 h_v6 hinv1 s1 v4 v5 v6
  store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v7 dropping h_v2 hinv2 s2 v2
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fsm_2ebvshl.construct s3 e_v9 (by rw [he_v9]; rfl) h_v7 h_v8 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying dropping h_v7 h_v8 he_v9 hinv3 e_v9 s3 v7 v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_to_smt.case_73 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_74_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_74_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_74 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_74 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_74_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_74
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_74
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_bvlshr.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_74
  store_step with ih.eo__24eo_5fto_5fsmt s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 dropping h_v4 h_v5 h_v6 hinv1 s1 v4 v5 v6
  store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v7 dropping h_v2 hinv2 s2 v2
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fsm_2ebvlshr.construct s3 e_v9 (by rw [he_v9]; rfl) h_v7 h_v8 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying dropping h_v7 h_v8 he_v9 hinv3 e_v9 s3 v7 v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_to_smt.case_74 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_75_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_75_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_75 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_75 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_75_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_75
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_75
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_bvashr.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_75
  store_step with ih.eo__24eo_5fto_5fsmt s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 dropping h_v4 h_v5 h_v6 hinv1 s1 v4 v5 v6
  store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v7 dropping h_v2 hinv2 s2 v2
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fsm_2ebvashr.construct s3 e_v9 (by rw [he_v9]; rfl) h_v7 h_v8 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying dropping h_v7 h_v8 he_v9 hinv3 e_v9 s3 v7 v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_to_smt.case_75 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_76_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_76_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_76 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_76 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_76_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_76
  pat_destruct CtorSpec.eo_zero_5fextend.destruct h_v1 as ⟨v4, x_v4, h_v4⟩ else hinv hG in EoCases.__eo_to_smt.case_76
  obtain hn_v4 := CtorSpec.eo_zero_5fextend.fields_ne_stuck hinv h_v1
  store_step with ih.eo__24eo_5fto_5fsmt s v4 _ hinv h64 hrem h_v4 as ⟨v5, s1, hinv1, h_v5⟩ growing hG carrying h_v2 dropping h_a0 h_v1 h_v4 v1 v4
  store_step with ih.eo__24eo_5fto_5fsmt s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v6, s2, hinv2, h_v6⟩ growing hG carrying h_v5 dropping h_v2 hinv1 s1 v2
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo__24emb_5fsm_2ezero_5fextend.construct s2 e_v7 (by rw [he_v7]; rfl) h_v5 h_v6 hinv2 h64 as ⟨v7, s3, hinv3, h_v7⟩ growing hG carrying dropping h_v5 h_v6 he_v7 hinv2 e_v7 s2 v5 v6
  case_done hinv3 hG with h_v7 in EoCases.__eo_to_smt.case_76 using hn_v1 hn_v2 hn_v4

theorem case_77_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_77_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_77 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_77 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_77_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_77
  pat_destruct CtorSpec.eo_sign_5fextend.destruct h_v1 as ⟨v4, x_v4, h_v4⟩ else hinv hG in EoCases.__eo_to_smt.case_77
  obtain hn_v4 := CtorSpec.eo_sign_5fextend.fields_ne_stuck hinv h_v1
  store_step with ih.eo__24eo_5fto_5fsmt s v4 _ hinv h64 hrem h_v4 as ⟨v5, s1, hinv1, h_v5⟩ growing hG carrying h_v2 dropping h_a0 h_v1 h_v4 v1 v4
  store_step with ih.eo__24eo_5fto_5fsmt s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v6, s2, hinv2, h_v6⟩ growing hG carrying h_v5 dropping h_v2 hinv1 s1 v2
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo__24emb_5fsm_2esign_5fextend.construct s2 e_v7 (by rw [he_v7]; rfl) h_v5 h_v6 hinv2 h64 as ⟨v7, s3, hinv3, h_v7⟩ growing hG carrying dropping h_v5 h_v6 he_v7 hinv2 e_v7 s2 v5 v6
  case_done hinv3 hG with h_v7 in EoCases.__eo_to_smt.case_77 using hn_v1 hn_v2 hn_v4

theorem case_78_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_78_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_78 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_78 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_78_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_78
  pat_destruct CtorSpec.eo_rotate_5fleft.destruct h_v1 as ⟨v4, x_v4, h_v4⟩ else hinv hG in EoCases.__eo_to_smt.case_78
  obtain hn_v4 := CtorSpec.eo_rotate_5fleft.fields_ne_stuck hinv h_v1
  store_step with ih.eo__24eo_5fto_5fsmt s v4 _ hinv h64 hrem h_v4 as ⟨v5, s1, hinv1, h_v5⟩ growing hG carrying h_v2 dropping h_a0 h_v1 h_v4 v1 v4
  store_step with ih.eo__24eo_5fto_5fsmt s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v6, s2, hinv2, h_v6⟩ growing hG carrying h_v5 dropping h_v2 hinv1 s1 v2
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo__24emb_5fsm_2erotate_5fleft.construct s2 e_v7 (by rw [he_v7]; rfl) h_v5 h_v6 hinv2 h64 as ⟨v7, s3, hinv3, h_v7⟩ growing hG carrying dropping h_v5 h_v6 he_v7 hinv2 e_v7 s2 v5 v6
  case_done hinv3 hG with h_v7 in EoCases.__eo_to_smt.case_78 using hn_v1 hn_v2 hn_v4

theorem case_79_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_79_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_79 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_79 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_79_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_79
  pat_destruct CtorSpec.eo_rotate_5fright.destruct h_v1 as ⟨v4, x_v4, h_v4⟩ else hinv hG in EoCases.__eo_to_smt.case_79
  obtain hn_v4 := CtorSpec.eo_rotate_5fright.fields_ne_stuck hinv h_v1
  store_step with ih.eo__24eo_5fto_5fsmt s v4 _ hinv h64 hrem h_v4 as ⟨v5, s1, hinv1, h_v5⟩ growing hG carrying h_v2 dropping h_a0 h_v1 h_v4 v1 v4
  store_step with ih.eo__24eo_5fto_5fsmt s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v6, s2, hinv2, h_v6⟩ growing hG carrying h_v5 dropping h_v2 hinv1 s1 v2
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo__24emb_5fsm_2erotate_5fright.construct s2 e_v7 (by rw [he_v7]; rfl) h_v5 h_v6 hinv2 h64 as ⟨v7, s3, hinv3, h_v7⟩ growing hG carrying dropping h_v5 h_v6 he_v7 hinv2 e_v7 s2 v5 v6
  case_done hinv3 hG with h_v7 in EoCases.__eo_to_smt.case_79 using hn_v1 hn_v2 hn_v4

theorem case_80_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_80_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_80 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_80 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_80_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_80
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_80
  pat_unapply h_v4 as ⟨v7, v8, x_v7, x_v8, h_v7, h_v8, hn_v7, hn_v8⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_80
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_bvite.construct s e_v9 (by rw [he_v9]; exact empty_args) hinv h64 as ⟨v9, s1, hinv1, h_v9⟩ growing hG carrying h_v2 h_v5 h_v7 h_v8 dropping h_a0 h_v1 h_v4 he_v9 e_v9 v1 v4
  pat_same v7 v9 with h_v7 h_v9 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_80
  store_step with ih.eo__24eo_5fto_5fsmt s1 v8 _ hinv1 h64 (hG.rem hrem) h_v8 as ⟨v10, s2, hinv2, h_v10⟩ growing hG carrying h_v2 h_v5 dropping h_v7 h_v8 h_v9 hinv1 s1 v7 v8 v9
  simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.raw_int_u32_spec s2 1#u32 (1) (by scalar_tac) hinv2 h64 as ⟨v11, s3, hinv3, h_v11⟩ growing hG carrying h_v2 h_v5 h_v10 dropping hinv2 s2
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.raw_int_u32_spec s3 1#u32 (1) (by scalar_tac) hinv3 h64 as ⟨v12, s4, hinv4, h_v12⟩ growing hG carrying h_v2 h_v5 h_v10 h_v11 dropping hinv3 s3
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eBinary.construct s4 e_v13 (by rw [he_v13]; rfl) h_v11 h_v12 hinv4 h64 as ⟨v13, s5, hinv5, h_v13⟩ growing hG carrying h_v2 h_v5 h_v10 dropping h_v11 h_v12 he_v13 hinv4 e_v13 s4 v11 v12
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo__24emb_5fsm_2e_3d.construct s5 e_v14 (by rw [he_v14]; rfl) h_v10 h_v13 hinv5 h64 as ⟨v14, s6, hinv6, h_v14⟩ growing hG carrying h_v2 h_v5 dropping h_v10 h_v13 he_v14 hinv5 e_v14 s5 v10 v13
  store_step with ih.eo__24eo_5fto_5fsmt s6 v5 _ hinv6 h64 (hG.rem hrem) h_v5 as ⟨v15, s7, hinv7, h_v15⟩ growing hG carrying h_v2 h_v14 dropping h_v5 hinv6 s6 v5
  store_step with ih.eo__24eo_5fto_5fsmt s7 v2 _ hinv7 h64 (hG.rem hrem) h_v2 as ⟨v16, s8, hinv8, h_v16⟩ growing hG carrying h_v14 h_v15 dropping h_v2 hinv7 s7 v2
  step as ⟨e_v17, he_v17⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eite.construct s8 e_v17 (by rw [he_v17]; rfl) h_v14 h_v15 h_v16 hinv8 h64 as ⟨v17, s9, hinv9, h_v17⟩ growing hG carrying dropping h_v14 h_v15 h_v16 he_v17 hinv8 e_v17 s8 v14 v15 v16
  case_done hinv9 hG with h_v17 in EoCases.__eo_to_smt.case_80 using hn_v1 hn_v2 hn_v4 hn_v5 hn_v7 hn_v8

theorem case_81_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_81_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_81 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_81 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_81_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_81
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_81
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_bvuaddo.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_81
  store_step with ih.eo__24eo_5fto_5fsmt s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 dropping h_v4 h_v5 h_v6 hinv1 s1 v4 v5 v6
  store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v7 dropping h_v2 hinv2 s2 v2
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fsm_2ebvuaddo.construct s3 e_v9 (by rw [he_v9]; rfl) h_v7 h_v8 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying dropping h_v7 h_v8 he_v9 hinv3 e_v9 s3 v7 v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_to_smt.case_81 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_82_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_82_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_82 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_82 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_82_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_82
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_bvnego.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v1 h_v2 dropping h_a0 he_v3 e_v3
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_82
  store_step with ih.eo__24eo_5fto_5fsmt s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying dropping h_v1 h_v2 h_v3 hinv1 s1 v1 v2 v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5fsm_2ebvnego.construct s2 e_v5 (by rw [he_v5]; rfl) h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying dropping h_v4 he_v5 hinv2 e_v5 s2 v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_to_smt.case_82 using hn_v1 hn_v2

theorem case_83_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_83_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_83 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_83 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_83_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_83
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_83
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_bvsaddo.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_83
  store_step with ih.eo__24eo_5fto_5fsmt s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 dropping h_v4 h_v5 h_v6 hinv1 s1 v4 v5 v6
  store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v7 dropping h_v2 hinv2 s2 v2
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fsm_2ebvsaddo.construct s3 e_v9 (by rw [he_v9]; rfl) h_v7 h_v8 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying dropping h_v7 h_v8 he_v9 hinv3 e_v9 s3 v7 v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_to_smt.case_83 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_84_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_84_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_84 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_84 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_84_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_84
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_84
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_bvumulo.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_84
  store_step with ih.eo__24eo_5fto_5fsmt s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 dropping h_v4 h_v5 h_v6 hinv1 s1 v4 v5 v6
  store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v7 dropping h_v2 hinv2 s2 v2
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fsm_2ebvumulo.construct s3 e_v9 (by rw [he_v9]; rfl) h_v7 h_v8 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying dropping h_v7 h_v8 he_v9 hinv3 e_v9 s3 v7 v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_to_smt.case_84 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_85_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_85_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_85 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_85 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_85_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_85
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_85
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_bvsmulo.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_85
  store_step with ih.eo__24eo_5fto_5fsmt s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 dropping h_v4 h_v5 h_v6 hinv1 s1 v4 v5 v6
  store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v7 dropping h_v2 hinv2 s2 v2
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fsm_2ebvsmulo.construct s3 e_v9 (by rw [he_v9]; rfl) h_v7 h_v8 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying dropping h_v7 h_v8 he_v9 hinv3 e_v9 s3 v7 v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_to_smt.case_85 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_86_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_86_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_86 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_86 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_86_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_86
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_86
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_bvusubo.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_86
  store_step with ih.eo__24eo_5fto_5fsmt s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 dropping h_v4 h_v5 h_v6 hinv1 s1 v4 v5 v6
  store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v7 dropping h_v2 hinv2 s2 v2
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fsm_2ebvusubo.construct s3 e_v9 (by rw [he_v9]; rfl) h_v7 h_v8 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying dropping h_v7 h_v8 he_v9 hinv3 e_v9 s3 v7 v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_to_smt.case_86 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_87_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_87_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_87 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_87 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_87_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_87
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_87
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_bvssubo.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_87
  store_step with ih.eo__24eo_5fto_5fsmt s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 dropping h_v4 h_v5 h_v6 hinv1 s1 v4 v5 v6
  store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v7 dropping h_v2 hinv2 s2 v2
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fsm_2ebvssubo.construct s3 e_v9 (by rw [he_v9]; rfl) h_v7 h_v8 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying dropping h_v7 h_v8 he_v9 hinv3 e_v9 s3 v7 v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_to_smt.case_87 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_88_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_88_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_88 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_88 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_88_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_88
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_88
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_bvsdivo.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_88
  store_step with ih.eo__24eo_5fto_5fsmt s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 dropping h_v4 h_v5 h_v6 hinv1 s1 v4 v5 v6
  store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v7 dropping h_v2 hinv2 s2 v2
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fsm_2ebvsdivo.construct s3 e_v9 (by rw [he_v9]; rfl) h_v7 h_v8 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying dropping h_v7 h_v8 he_v9 hinv3 e_v9 s3 v7 v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_to_smt.case_88 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_89_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_89_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_89 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_89 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_89_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_89
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_89
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_bvultbv.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_89
  store_step with ih.eo__24eo_5fto_5fsmt s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 dropping h_v4 h_v5 h_v6 hinv1 s1 v4 v5 v6
  store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v7 dropping h_v2 hinv2 s2 v2
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fsm_2ebvult.construct s3 e_v9 (by rw [he_v9]; rfl) h_v7 h_v8 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying dropping h_v7 h_v8 he_v9 hinv3 e_v9 s3 v7 v8
  simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.raw_int_u32_spec s4 1#u32 (1) (by scalar_tac) hinv4 h64 as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_v9 dropping hinv4 s4
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.raw_int_u32_spec s5 1#u32 (1) (by scalar_tac) hinv5 h64 as ⟨v11, s6, hinv6, h_v11⟩ growing hG carrying h_v9 h_v10 dropping hinv5 s5
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eBinary.construct s6 e_v12 (by rw [he_v12]; rfl) h_v10 h_v11 hinv6 h64 as ⟨v12, s7, hinv7, h_v12⟩ growing hG carrying h_v9 dropping h_v10 h_v11 he_v12 hinv6 e_v12 s6 v10 v11
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.raw_int_u32_spec s7 1#u32 (1) (by scalar_tac) hinv7 h64 as ⟨v13, s8, hinv8, h_v13⟩ growing hG carrying h_v9 h_v12 dropping hinv7 s7
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.raw_int_u32_spec s8 0#u32 (0) (by scalar_tac) hinv8 h64 as ⟨v14, s9, hinv9, h_v14⟩ growing hG carrying h_v9 h_v12 h_v13 dropping hinv8 s8
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eBinary.construct s9 e_v15 (by rw [he_v15]; rfl) h_v13 h_v14 hinv9 h64 as ⟨v15, s10, hinv10, h_v15⟩ growing hG carrying h_v9 h_v12 dropping h_v13 h_v14 he_v15 hinv9 e_v15 s9 v13 v14
  step as ⟨e_v16, he_v16⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eite.construct s10 e_v16 (by rw [he_v16]; rfl) h_v9 h_v12 h_v15 hinv10 h64 as ⟨v16, s11, hinv11, h_v16⟩ growing hG carrying dropping h_v12 h_v15 h_v9 he_v16 hinv10 e_v16 s10 v12 v15 v9
  case_done hinv11 hG with h_v16 in EoCases.__eo_to_smt.case_89 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_90_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_90_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_90 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_90 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_90_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_90
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_90
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_bvsltbv.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_90
  store_step with ih.eo__24eo_5fto_5fsmt s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 dropping h_v4 h_v5 h_v6 hinv1 s1 v4 v5 v6
  store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v7 dropping h_v2 hinv2 s2 v2
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fsm_2ebvslt.construct s3 e_v9 (by rw [he_v9]; rfl) h_v7 h_v8 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying dropping h_v7 h_v8 he_v9 hinv3 e_v9 s3 v7 v8
  simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.raw_int_u32_spec s4 1#u32 (1) (by scalar_tac) hinv4 h64 as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_v9 dropping hinv4 s4
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.raw_int_u32_spec s5 1#u32 (1) (by scalar_tac) hinv5 h64 as ⟨v11, s6, hinv6, h_v11⟩ growing hG carrying h_v9 h_v10 dropping hinv5 s5
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eBinary.construct s6 e_v12 (by rw [he_v12]; rfl) h_v10 h_v11 hinv6 h64 as ⟨v12, s7, hinv7, h_v12⟩ growing hG carrying h_v9 dropping h_v10 h_v11 he_v12 hinv6 e_v12 s6 v10 v11
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.raw_int_u32_spec s7 1#u32 (1) (by scalar_tac) hinv7 h64 as ⟨v13, s8, hinv8, h_v13⟩ growing hG carrying h_v9 h_v12 dropping hinv7 s7
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.raw_int_u32_spec s8 0#u32 (0) (by scalar_tac) hinv8 h64 as ⟨v14, s9, hinv9, h_v14⟩ growing hG carrying h_v9 h_v12 h_v13 dropping hinv8 s8
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eBinary.construct s9 e_v15 (by rw [he_v15]; rfl) h_v13 h_v14 hinv9 h64 as ⟨v15, s10, hinv10, h_v15⟩ growing hG carrying h_v9 h_v12 dropping h_v13 h_v14 he_v15 hinv9 e_v15 s9 v13 v14
  step as ⟨e_v16, he_v16⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eite.construct s10 e_v16 (by rw [he_v16]; rfl) h_v9 h_v12 h_v15 hinv10 h64 as ⟨v16, s11, hinv11, h_v16⟩ growing hG carrying dropping h_v12 h_v15 h_v9 he_v16 hinv10 e_v16 s10 v12 v15 v9
  case_done hinv11 hG with h_v16 in EoCases.__eo_to_smt.case_90 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_91_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_91_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_91 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_91 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_91_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_91
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_bvredand.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v1 h_v2 dropping h_a0 he_v3 e_v3
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_91
  store_step with ih.eo__24eo_5fto_5fsmt s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v2 dropping h_v1 h_v3 hinv1 s1 v1 v3
  store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_v4 dropping h_v2 hinv2 s2 v2
  store_step with ih.eo__24smtx_5ftypeof s3 v5 _ hinv3 h64 (hG.rem hrem) h_v5 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_v4 dropping h_v5 hinv3 s3 v5
  store_step with ih.eo__24eo_5fto_5fsmt_5fbv_5fsize s4 v6 _ hinv4 h64 (hG.rem hrem) h_v6 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_v4 dropping h_v6 hinv4 s4 v6
  simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.raw_int_u32_spec s5 0#u32 (0) (by scalar_tac) hinv5 h64 as ⟨v8, s6, hinv6, h_v8⟩ growing hG carrying h_v4 h_v7 dropping hinv5 s5
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eBinary.construct s6 e_v9 (by rw [he_v9]; rfl) h_v7 h_v8 hinv6 h64 as ⟨v9, s7, hinv7, h_v9⟩ growing hG carrying h_v4 dropping h_v7 h_v8 he_v9 hinv6 e_v9 s6 v7 v8
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo__24emb_5fsm_2ebvnot.construct s7 e_v10 (by rw [he_v10]; rfl) h_v9 hinv7 h64 as ⟨v10, s8, hinv8, h_v10⟩ growing hG carrying h_v4 dropping h_v9 he_v10 hinv7 e_v10 s7 v9
  step as ⟨e_v11, he_v11⟩
  store_step with CtorSpec.eo__24emb_5fsm_2ebvcomp.construct s8 e_v11 (by rw [he_v11]; rfl) h_v4 h_v10 hinv8 h64 as ⟨v11, s9, hinv9, h_v11⟩ growing hG carrying dropping h_v10 h_v4 he_v11 hinv8 e_v11 s8 v10 v4
  case_done hinv9 hG with h_v11 in EoCases.__eo_to_smt.case_91 using hn_v1 hn_v2

theorem case_92_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_92_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_92 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_92 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_92_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_92
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_bvredor.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v1 h_v2 dropping h_a0 he_v3 e_v3
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_92
  store_step with ih.eo__24eo_5fto_5fsmt s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v2 dropping h_v1 h_v3 hinv1 s1 v1 v3
  store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_v4 dropping h_v2 hinv2 s2 v2
  store_step with ih.eo__24smtx_5ftypeof s3 v5 _ hinv3 h64 (hG.rem hrem) h_v5 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_v4 dropping h_v5 hinv3 s3 v5
  store_step with ih.eo__24eo_5fto_5fsmt_5fbv_5fsize s4 v6 _ hinv4 h64 (hG.rem hrem) h_v6 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_v4 dropping h_v6 hinv4 s4 v6
  simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.raw_int_u32_spec s5 0#u32 (0) (by scalar_tac) hinv5 h64 as ⟨v8, s6, hinv6, h_v8⟩ growing hG carrying h_v4 h_v7 dropping hinv5 s5
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eBinary.construct s6 e_v9 (by rw [he_v9]; rfl) h_v7 h_v8 hinv6 h64 as ⟨v9, s7, hinv7, h_v9⟩ growing hG carrying h_v4 dropping h_v7 h_v8 he_v9 hinv6 e_v9 s6 v7 v8
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo__24emb_5fsm_2ebvcomp.construct s7 e_v10 (by rw [he_v10]; rfl) h_v4 h_v9 hinv7 h64 as ⟨v10, s8, hinv8, h_v10⟩ growing hG carrying dropping h_v4 h_v9 he_v10 hinv7 e_v10 s7 v4 v9
  step as ⟨e_v11, he_v11⟩
  store_step with CtorSpec.eo__24emb_5fsm_2ebvnot.construct s8 e_v11 (by rw [he_v11]; rfl) h_v10 hinv8 h64 as ⟨v11, s9, hinv9, h_v11⟩ growing hG carrying dropping h_v10 he_v11 hinv8 e_v11 s8 v10
  case_done hinv9 hG with h_v11 in EoCases.__eo_to_smt.case_92 using hn_v1 hn_v2

theorem case_93_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_93_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_93 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_93 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_93_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_93
  pat_destruct CtorSpec.eo__40bit.destruct h_v1 as ⟨v4, x_v4, h_v4⟩ else hinv hG in EoCases.__eo_to_smt.case_93
  obtain hn_v4 := CtorSpec.eo__40bit.fields_ne_stuck hinv h_v1
  store_step with ih.eo__24eo_5fto_5fsmt s v4 _ hinv h64 hrem h_v4 as ⟨v5, s1, hinv1, h_v5⟩ growing hG carrying h_v2 h_v4 dropping h_a0 h_v1 v1
  store_step with ih.eo__24eo_5fto_5fsmt s1 v4 _ hinv1 h64 (hG.rem hrem) h_v4 as ⟨v6, s2, hinv2, h_v6⟩ growing hG carrying h_v2 h_v5 dropping h_v4 hinv1 s1 v4
  store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v7, s3, hinv3, h_v7⟩ growing hG carrying h_v5 h_v6 dropping h_v2 hinv2 s2 v2
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eextract.construct s3 e_v8 (by rw [he_v8]; rfl) h_v5 h_v6 h_v7 hinv3 h64 as ⟨v8, s4, hinv4, h_v8⟩ growing hG carrying dropping h_v5 h_v6 h_v7 he_v8 hinv3 e_v8 s3 v5 v6 v7
  simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.raw_int_u32_spec s4 1#u32 (1) (by scalar_tac) hinv4 h64 as ⟨v9, s5, hinv5, h_v9⟩ growing hG carrying h_v8 dropping hinv4 s4
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.raw_int_u32_spec s5 1#u32 (1) (by scalar_tac) hinv5 h64 as ⟨v10, s6, hinv6, h_v10⟩ growing hG carrying h_v8 h_v9 dropping hinv5 s5
  step as ⟨e_v11, he_v11⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eBinary.construct s6 e_v11 (by rw [he_v11]; rfl) h_v9 h_v10 hinv6 h64 as ⟨v11, s7, hinv7, h_v11⟩ growing hG carrying h_v8 dropping h_v10 h_v9 he_v11 hinv6 e_v11 s6 v10 v9
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo__24emb_5fsm_2e_3d.construct s7 e_v12 (by rw [he_v12]; rfl) h_v8 h_v11 hinv7 h64 as ⟨v12, s8, hinv8, h_v12⟩ growing hG carrying dropping h_v11 h_v8 he_v12 hinv7 e_v12 s7 v11 v8
  case_done hinv8 hG with h_v12 in EoCases.__eo_to_smt.case_93 using hn_v1 hn_v2 hn_v4

theorem case_94_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_94_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_94 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_94 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_94_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_94
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_94
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_94
  store_step with ih.eo__24eo_5fto_5fsmt s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v5 dropping h_v2 h_v4 h_v6 hinv1 s1 v2 v4 v6
  store_step with ih.eo__24eo_5fto_5fsmt s2 v5 _ hinv2 h64 (hG.rem hrem) h_v5 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v7 dropping h_v5 hinv2 s2 v5
  simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.raw_int_u32_spec s3 1#u32 (1) (by scalar_tac) hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_v7 h_v8 dropping hinv3 s3
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.raw_int_u32_spec s4 1#u32 (1) (by scalar_tac) hinv4 h64 as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_v7 h_v8 h_v9 dropping hinv4 s4
  step as ⟨e_v11, he_v11⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eBinary.construct s5 e_v11 (by rw [he_v11]; rfl) h_v9 h_v10 hinv5 h64 as ⟨v11, s6, hinv6, h_v11⟩ growing hG carrying h_v7 h_v8 dropping h_v10 h_v9 he_v11 hinv5 e_v11 s5 v10 v9
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.raw_int_u32_spec s6 1#u32 (1) (by scalar_tac) hinv6 h64 as ⟨v12, s7, hinv7, h_v12⟩ growing hG carrying h_v7 h_v8 h_v11 dropping hinv6 s6
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.raw_int_u32_spec s7 0#u32 (0) (by scalar_tac) hinv7 h64 as ⟨v13, s8, hinv8, h_v13⟩ growing hG carrying h_v7 h_v8 h_v11 h_v12 dropping hinv7 s7
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eBinary.construct s8 e_v14 (by rw [he_v14]; rfl) h_v12 h_v13 hinv8 h64 as ⟨v14, s9, hinv9, h_v14⟩ growing hG carrying h_v7 h_v8 h_v11 dropping h_v12 h_v13 he_v14 hinv8 e_v14 s8 v12 v13
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eite.construct s9 e_v15 (by rw [he_v15]; rfl) h_v8 h_v11 h_v14 hinv9 h64 as ⟨v15, s10, hinv10, h_v15⟩ growing hG carrying h_v7 dropping h_v11 h_v14 h_v8 he_v15 hinv9 e_v15 s9 v11 v14 v8
  step as ⟨e_v16, he_v16⟩
  store_step with CtorSpec.eo__24emb_5fsm_2econcat.construct s10 e_v16 (by rw [he_v16]; rfl) h_v7 h_v15 hinv10 h64 as ⟨v16, s11, hinv11, h_v16⟩ growing hG carrying dropping h_v15 h_v7 he_v16 hinv10 e_v16 s10 v15 v7
  case_done hinv11 hG with h_v16 in EoCases.__eo_to_smt.case_94 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_95_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_95_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_95 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_95 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_95_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo_seq_2eempty.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_to_smt.case_95
  obtain hn_v1 := CtorSpec.eo_seq_2eempty.fields_ne_stuck hinv h_a0
  store_step with ih.eo__24eo_5fto_5fsmt_5ftype s v1 _ hinv h64 hrem h_v1 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying dropping h_a0 h_v1 v1
  store_step with ih.eo__24eo_5fto_5fsmt_5fseq_2eempty s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying dropping h_v2 hinv1 s1 v2
  case_done hinv2 hG with h_v3 in EoCases.__eo_to_smt.case_95 using hn_v1

theorem case_96_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_96_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_96 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_96 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_96_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_96
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_str_2elen.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v1 h_v2 dropping h_a0 he_v3 e_v3
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_96
  store_step with ih.eo__24eo_5fto_5fsmt s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying dropping h_v1 h_v2 h_v3 hinv1 s1 v1 v2 v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5fsm_2estr_2elen.construct s2 e_v5 (by rw [he_v5]; rfl) h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying dropping h_v4 he_v5 hinv2 e_v5 s2 v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_to_smt.case_96 using hn_v1 hn_v2

theorem case_97_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_97_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_97 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_97 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_97_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_97
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_97
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_97
  store_step with ih.eo__24eo_5fto_5fsmt s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 dropping h_v4 h_v5 h_v6 hinv1 s1 v4 v5 v6
  store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v7 dropping h_v2 hinv2 s2 v2
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fsm_2estr_2e_2b_2b.construct s3 e_v9 (by rw [he_v9]; rfl) h_v7 h_v8 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying dropping h_v7 h_v8 he_v9 hinv3 e_v9 s3 v7 v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_to_smt.case_97 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_98_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_98_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_98 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_98 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_98_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_98
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_98
  pat_unapply h_v4 as ⟨v7, v8, x_v7, x_v8, h_v7, h_v8, hn_v7, hn_v8⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_98
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s e_v9 (by rw [he_v9]; exact empty_args) hinv h64 as ⟨v9, s1, hinv1, h_v9⟩ growing hG carrying h_v2 h_v5 h_v7 h_v8 dropping h_a0 h_v1 h_v4 he_v9 e_v9 v1 v4
  pat_same v7 v9 with h_v7 h_v9 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_98
  store_step with ih.eo__24eo_5fto_5fsmt s1 v8 _ hinv1 h64 (hG.rem hrem) h_v8 as ⟨v10, s2, hinv2, h_v10⟩ growing hG carrying h_v2 h_v5 dropping h_v7 h_v8 h_v9 hinv1 s1 v7 v8 v9
  store_step with ih.eo__24eo_5fto_5fsmt s2 v5 _ hinv2 h64 (hG.rem hrem) h_v5 as ⟨v11, s3, hinv3, h_v11⟩ growing hG carrying h_v2 h_v10 dropping h_v5 hinv2 s2 v5
  store_step with ih.eo__24eo_5fto_5fsmt s3 v2 _ hinv3 h64 (hG.rem hrem) h_v2 as ⟨v12, s4, hinv4, h_v12⟩ growing hG carrying h_v10 h_v11 dropping h_v2 hinv3 s3 v2
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo__24emb_5fsm_2estr_2esubstr.construct s4 e_v13 (by rw [he_v13]; rfl) h_v10 h_v11 h_v12 hinv4 h64 as ⟨v13, s5, hinv5, h_v13⟩ growing hG carrying dropping h_v10 h_v11 h_v12 he_v13 hinv4 e_v13 s4 v10 v11 v12
  case_done hinv5 hG with h_v13 in EoCases.__eo_to_smt.case_98 using hn_v1 hn_v2 hn_v4 hn_v5 hn_v7 hn_v8

theorem case_99_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_99_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_99 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_99 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_99_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_99
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_99
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_str_2econtains.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_99
  store_step with ih.eo__24eo_5fto_5fsmt s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 dropping h_v4 h_v5 h_v6 hinv1 s1 v4 v5 v6
  store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v7 dropping h_v2 hinv2 s2 v2
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fsm_2estr_2econtains.construct s3 e_v9 (by rw [he_v9]; rfl) h_v7 h_v8 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying dropping h_v7 h_v8 he_v9 hinv3 e_v9 s3 v7 v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_to_smt.case_99 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_100_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_100_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_100 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_100 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_100_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_100
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_100
  pat_unapply h_v4 as ⟨v7, v8, x_v7, x_v8, h_v7, h_v8, hn_v7, hn_v8⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_100
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_str_2ereplace.construct s e_v9 (by rw [he_v9]; exact empty_args) hinv h64 as ⟨v9, s1, hinv1, h_v9⟩ growing hG carrying h_v2 h_v5 h_v7 h_v8 dropping h_a0 h_v1 h_v4 he_v9 e_v9 v1 v4
  pat_same v7 v9 with h_v7 h_v9 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_100
  store_step with ih.eo__24eo_5fto_5fsmt s1 v8 _ hinv1 h64 (hG.rem hrem) h_v8 as ⟨v10, s2, hinv2, h_v10⟩ growing hG carrying h_v2 h_v5 dropping h_v7 h_v8 h_v9 hinv1 s1 v7 v8 v9
  store_step with ih.eo__24eo_5fto_5fsmt s2 v5 _ hinv2 h64 (hG.rem hrem) h_v5 as ⟨v11, s3, hinv3, h_v11⟩ growing hG carrying h_v2 h_v10 dropping h_v5 hinv2 s2 v5
  store_step with ih.eo__24eo_5fto_5fsmt s3 v2 _ hinv3 h64 (hG.rem hrem) h_v2 as ⟨v12, s4, hinv4, h_v12⟩ growing hG carrying h_v10 h_v11 dropping h_v2 hinv3 s3 v2
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo__24emb_5fsm_2estr_2ereplace.construct s4 e_v13 (by rw [he_v13]; rfl) h_v10 h_v11 h_v12 hinv4 h64 as ⟨v13, s5, hinv5, h_v13⟩ growing hG carrying dropping h_v10 h_v11 h_v12 he_v13 hinv4 e_v13 s4 v10 v11 v12
  case_done hinv5 hG with h_v13 in EoCases.__eo_to_smt.case_100 using hn_v1 hn_v2 hn_v4 hn_v5 hn_v7 hn_v8

theorem case_101_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_101_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_101 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_101 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_101_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_101
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_101
  pat_unapply h_v4 as ⟨v7, v8, x_v7, x_v8, h_v7, h_v8, hn_v7, hn_v8⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_101
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_str_2eindexof.construct s e_v9 (by rw [he_v9]; exact empty_args) hinv h64 as ⟨v9, s1, hinv1, h_v9⟩ growing hG carrying h_v2 h_v5 h_v7 h_v8 dropping h_a0 h_v1 h_v4 he_v9 e_v9 v1 v4
  pat_same v7 v9 with h_v7 h_v9 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_101
  store_step with ih.eo__24eo_5fto_5fsmt s1 v8 _ hinv1 h64 (hG.rem hrem) h_v8 as ⟨v10, s2, hinv2, h_v10⟩ growing hG carrying h_v2 h_v5 dropping h_v7 h_v8 h_v9 hinv1 s1 v7 v8 v9
  store_step with ih.eo__24eo_5fto_5fsmt s2 v5 _ hinv2 h64 (hG.rem hrem) h_v5 as ⟨v11, s3, hinv3, h_v11⟩ growing hG carrying h_v2 h_v10 dropping h_v5 hinv2 s2 v5
  store_step with ih.eo__24eo_5fto_5fsmt s3 v2 _ hinv3 h64 (hG.rem hrem) h_v2 as ⟨v12, s4, hinv4, h_v12⟩ growing hG carrying h_v10 h_v11 dropping h_v2 hinv3 s3 v2
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo__24emb_5fsm_2estr_2eindexof.construct s4 e_v13 (by rw [he_v13]; rfl) h_v10 h_v11 h_v12 hinv4 h64 as ⟨v13, s5, hinv5, h_v13⟩ growing hG carrying dropping h_v10 h_v11 h_v12 he_v13 hinv4 e_v13 s4 v10 v11 v12
  case_done hinv5 hG with h_v13 in EoCases.__eo_to_smt.case_101 using hn_v1 hn_v2 hn_v4 hn_v5 hn_v7 hn_v8

theorem case_102_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_102_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_102 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_102 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_102_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_102
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_102
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_str_2eat.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_102
  store_step with ih.eo__24eo_5fto_5fsmt s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 dropping h_v4 h_v5 h_v6 hinv1 s1 v4 v5 v6
  store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v7 dropping h_v2 hinv2 s2 v2
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fsm_2estr_2eat.construct s3 e_v9 (by rw [he_v9]; rfl) h_v7 h_v8 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying dropping h_v7 h_v8 he_v9 hinv3 e_v9 s3 v7 v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_to_smt.case_102 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_103_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_103_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_103 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_103 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_103_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_103
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_103
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_str_2eprefixof.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_103
  store_step with ih.eo__24eo_5fto_5fsmt s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 dropping h_v4 h_v5 h_v6 hinv1 s1 v4 v5 v6
  store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v7 dropping h_v2 hinv2 s2 v2
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fsm_2estr_2eprefixof.construct s3 e_v9 (by rw [he_v9]; rfl) h_v7 h_v8 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying dropping h_v7 h_v8 he_v9 hinv3 e_v9 s3 v7 v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_to_smt.case_103 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_104_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_104_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_104 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_104 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_104_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_104
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_104
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_str_2esuffixof.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_104
  store_step with ih.eo__24eo_5fto_5fsmt s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 dropping h_v4 h_v5 h_v6 hinv1 s1 v4 v5 v6
  store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v7 dropping h_v2 hinv2 s2 v2
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fsm_2estr_2esuffixof.construct s3 e_v9 (by rw [he_v9]; rfl) h_v7 h_v8 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying dropping h_v7 h_v8 he_v9 hinv3 e_v9 s3 v7 v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_to_smt.case_104 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_105_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_105_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_105 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_105 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_105_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_105
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_str_2erev.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v1 h_v2 dropping h_a0 he_v3 e_v3
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_105
  store_step with ih.eo__24eo_5fto_5fsmt s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying dropping h_v1 h_v2 h_v3 hinv1 s1 v1 v2 v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5fsm_2estr_2erev.construct s2 e_v5 (by rw [he_v5]; rfl) h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying dropping h_v4 he_v5 hinv2 e_v5 s2 v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_to_smt.case_105 using hn_v1 hn_v2

theorem case_106_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_106_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_106 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_106 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_106_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_106
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_106
  pat_unapply h_v4 as ⟨v7, v8, x_v7, x_v8, h_v7, h_v8, hn_v7, hn_v8⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_106
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_str_2eupdate.construct s e_v9 (by rw [he_v9]; exact empty_args) hinv h64 as ⟨v9, s1, hinv1, h_v9⟩ growing hG carrying h_v2 h_v5 h_v7 h_v8 dropping h_a0 h_v1 h_v4 he_v9 e_v9 v1 v4
  pat_same v7 v9 with h_v7 h_v9 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_106
  store_step with ih.eo__24eo_5fto_5fsmt s1 v8 _ hinv1 h64 (hG.rem hrem) h_v8 as ⟨v10, s2, hinv2, h_v10⟩ growing hG carrying h_v2 h_v5 dropping h_v7 h_v8 h_v9 hinv1 s1 v7 v8 v9
  store_step with ih.eo__24eo_5fto_5fsmt s2 v5 _ hinv2 h64 (hG.rem hrem) h_v5 as ⟨v11, s3, hinv3, h_v11⟩ growing hG carrying h_v2 h_v10 dropping h_v5 hinv2 s2 v5
  store_step with ih.eo__24eo_5fto_5fsmt s3 v2 _ hinv3 h64 (hG.rem hrem) h_v2 as ⟨v12, s4, hinv4, h_v12⟩ growing hG carrying h_v10 h_v11 dropping h_v2 hinv3 s3 v2
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo__24emb_5fsm_2estr_2eupdate.construct s4 e_v13 (by rw [he_v13]; rfl) h_v10 h_v11 h_v12 hinv4 h64 as ⟨v13, s5, hinv5, h_v13⟩ growing hG carrying dropping h_v10 h_v11 h_v12 he_v13 hinv4 e_v13 s4 v10 v11 v12
  case_done hinv5 hG with h_v13 in EoCases.__eo_to_smt.case_106 using hn_v1 hn_v2 hn_v4 hn_v5 hn_v7 hn_v8

theorem case_107_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_107_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_107 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_107 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_107_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_107
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_str_2eto_5flower.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v1 h_v2 dropping h_a0 he_v3 e_v3
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_107
  store_step with ih.eo__24eo_5fto_5fsmt s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying dropping h_v1 h_v2 h_v3 hinv1 s1 v1 v2 v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5fsm_2estr_2eto_5flower.construct s2 e_v5 (by rw [he_v5]; rfl) h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying dropping h_v4 he_v5 hinv2 e_v5 s2 v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_to_smt.case_107 using hn_v1 hn_v2

theorem case_108_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_108_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_108 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_108 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_108_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_108
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_str_2eto_5fupper.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v1 h_v2 dropping h_a0 he_v3 e_v3
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_108
  store_step with ih.eo__24eo_5fto_5fsmt s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying dropping h_v1 h_v2 h_v3 hinv1 s1 v1 v2 v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5fsm_2estr_2eto_5fupper.construct s2 e_v5 (by rw [he_v5]; rfl) h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying dropping h_v4 he_v5 hinv2 e_v5 s2 v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_to_smt.case_108 using hn_v1 hn_v2

theorem case_109_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_109_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_109 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_109 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_109_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_109
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_str_2eto_5fcode.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v1 h_v2 dropping h_a0 he_v3 e_v3
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_109
  store_step with ih.eo__24eo_5fto_5fsmt s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying dropping h_v1 h_v2 h_v3 hinv1 s1 v1 v2 v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5fsm_2estr_2eto_5fcode.construct s2 e_v5 (by rw [he_v5]; rfl) h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying dropping h_v4 he_v5 hinv2 e_v5 s2 v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_to_smt.case_109 using hn_v1 hn_v2

theorem case_110_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_110_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_110 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_110 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_110_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_110
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_str_2efrom_5fcode.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v1 h_v2 dropping h_a0 he_v3 e_v3
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_110
  store_step with ih.eo__24eo_5fto_5fsmt s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying dropping h_v1 h_v2 h_v3 hinv1 s1 v1 v2 v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5fsm_2estr_2efrom_5fcode.construct s2 e_v5 (by rw [he_v5]; rfl) h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying dropping h_v4 he_v5 hinv2 e_v5 s2 v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_to_smt.case_110 using hn_v1 hn_v2

theorem case_111_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_111_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_111 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_111 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_111_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_111
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_str_2eis_5fdigit.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v1 h_v2 dropping h_a0 he_v3 e_v3
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_111
  store_step with ih.eo__24eo_5fto_5fsmt s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying dropping h_v1 h_v2 h_v3 hinv1 s1 v1 v2 v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5fsm_2estr_2eis_5fdigit.construct s2 e_v5 (by rw [he_v5]; rfl) h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying dropping h_v4 he_v5 hinv2 e_v5 s2 v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_to_smt.case_111 using hn_v1 hn_v2

theorem case_112_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_112_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_112 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_112 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_112_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_112
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_str_2eto_5fint.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v1 h_v2 dropping h_a0 he_v3 e_v3
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_112
  store_step with ih.eo__24eo_5fto_5fsmt s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying dropping h_v1 h_v2 h_v3 hinv1 s1 v1 v2 v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5fsm_2estr_2eto_5fint.construct s2 e_v5 (by rw [he_v5]; rfl) h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying dropping h_v4 he_v5 hinv2 e_v5 s2 v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_to_smt.case_112 using hn_v1 hn_v2

theorem case_113_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_113_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_113 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_113 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_113_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_113
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_str_2efrom_5fint.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v1 h_v2 dropping h_a0 he_v3 e_v3
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_113
  store_step with ih.eo__24eo_5fto_5fsmt s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying dropping h_v1 h_v2 h_v3 hinv1 s1 v1 v2 v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5fsm_2estr_2efrom_5fint.construct s2 e_v5 (by rw [he_v5]; rfl) h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying dropping h_v4 he_v5 hinv2 e_v5 s2 v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_to_smt.case_113 using hn_v1 hn_v2

theorem case_114_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_114_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_114 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_114 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_114_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_114
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_114
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_str_2e_3c.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_114
  store_step with ih.eo__24eo_5fto_5fsmt s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 dropping h_v4 h_v5 h_v6 hinv1 s1 v4 v5 v6
  store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v7 dropping h_v2 hinv2 s2 v2
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fsm_2estr_2e_3c.construct s3 e_v9 (by rw [he_v9]; rfl) h_v7 h_v8 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying dropping h_v7 h_v8 he_v9 hinv3 e_v9 s3 v7 v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_to_smt.case_114 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_115_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_115_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_115 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_115 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_115_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_115
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_115
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_str_2e_3c_3d.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_115
  store_step with ih.eo__24eo_5fto_5fsmt s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 dropping h_v4 h_v5 h_v6 hinv1 s1 v4 v5 v6
  store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v7 dropping h_v2 hinv2 s2 v2
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fsm_2estr_2e_3c_3d.construct s3 e_v9 (by rw [he_v9]; rfl) h_v7 h_v8 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying dropping h_v7 h_v8 he_v9 hinv3 e_v9 s3 v7 v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_to_smt.case_115 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_116_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_116_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_116 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_116 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_116_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_116
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_116
  pat_unapply h_v4 as ⟨v7, v8, x_v7, x_v8, h_v7, h_v8, hn_v7, hn_v8⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_116
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_str_2ereplace_5fall.construct s e_v9 (by rw [he_v9]; exact empty_args) hinv h64 as ⟨v9, s1, hinv1, h_v9⟩ growing hG carrying h_v2 h_v5 h_v7 h_v8 dropping h_a0 h_v1 h_v4 he_v9 e_v9 v1 v4
  pat_same v7 v9 with h_v7 h_v9 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_116
  store_step with ih.eo__24eo_5fto_5fsmt s1 v8 _ hinv1 h64 (hG.rem hrem) h_v8 as ⟨v10, s2, hinv2, h_v10⟩ growing hG carrying h_v2 h_v5 dropping h_v7 h_v8 h_v9 hinv1 s1 v7 v8 v9
  store_step with ih.eo__24eo_5fto_5fsmt s2 v5 _ hinv2 h64 (hG.rem hrem) h_v5 as ⟨v11, s3, hinv3, h_v11⟩ growing hG carrying h_v2 h_v10 dropping h_v5 hinv2 s2 v5
  store_step with ih.eo__24eo_5fto_5fsmt s3 v2 _ hinv3 h64 (hG.rem hrem) h_v2 as ⟨v12, s4, hinv4, h_v12⟩ growing hG carrying h_v10 h_v11 dropping h_v2 hinv3 s3 v2
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo__24emb_5fsm_2estr_2ereplace_5fall.construct s4 e_v13 (by rw [he_v13]; rfl) h_v10 h_v11 h_v12 hinv4 h64 as ⟨v13, s5, hinv5, h_v13⟩ growing hG carrying dropping h_v10 h_v11 h_v12 he_v13 hinv4 e_v13 s4 v10 v11 v12
  case_done hinv5 hG with h_v13 in EoCases.__eo_to_smt.case_116 using hn_v1 hn_v2 hn_v4 hn_v5 hn_v7 hn_v8

theorem case_117_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_117_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_117 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_117 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_117_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_117
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_117
  pat_unapply h_v4 as ⟨v7, v8, x_v7, x_v8, h_v7, h_v8, hn_v7, hn_v8⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_117
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_str_2ereplace_5fre.construct s e_v9 (by rw [he_v9]; exact empty_args) hinv h64 as ⟨v9, s1, hinv1, h_v9⟩ growing hG carrying h_v2 h_v5 h_v7 h_v8 dropping h_a0 h_v1 h_v4 he_v9 e_v9 v1 v4
  pat_same v7 v9 with h_v7 h_v9 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_117
  store_step with ih.eo__24eo_5fto_5fsmt s1 v8 _ hinv1 h64 (hG.rem hrem) h_v8 as ⟨v10, s2, hinv2, h_v10⟩ growing hG carrying h_v2 h_v5 dropping h_v7 h_v8 h_v9 hinv1 s1 v7 v8 v9
  store_step with ih.eo__24eo_5fto_5fsmt s2 v5 _ hinv2 h64 (hG.rem hrem) h_v5 as ⟨v11, s3, hinv3, h_v11⟩ growing hG carrying h_v2 h_v10 dropping h_v5 hinv2 s2 v5
  store_step with ih.eo__24eo_5fto_5fsmt s3 v2 _ hinv3 h64 (hG.rem hrem) h_v2 as ⟨v12, s4, hinv4, h_v12⟩ growing hG carrying h_v10 h_v11 dropping h_v2 hinv3 s3 v2
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo__24emb_5fsm_2estr_2ereplace_5fre.construct s4 e_v13 (by rw [he_v13]; rfl) h_v10 h_v11 h_v12 hinv4 h64 as ⟨v13, s5, hinv5, h_v13⟩ growing hG carrying dropping h_v10 h_v11 h_v12 he_v13 hinv4 e_v13 s4 v10 v11 v12
  case_done hinv5 hG with h_v13 in EoCases.__eo_to_smt.case_117 using hn_v1 hn_v2 hn_v4 hn_v5 hn_v7 hn_v8

theorem case_118_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_118_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_118 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_118 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_118_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_118
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_118
  pat_unapply h_v4 as ⟨v7, v8, x_v7, x_v8, h_v7, h_v8, hn_v7, hn_v8⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_118
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_str_2ereplace_5fre_5fall.construct s e_v9 (by rw [he_v9]; exact empty_args) hinv h64 as ⟨v9, s1, hinv1, h_v9⟩ growing hG carrying h_v2 h_v5 h_v7 h_v8 dropping h_a0 h_v1 h_v4 he_v9 e_v9 v1 v4
  pat_same v7 v9 with h_v7 h_v9 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_118
  store_step with ih.eo__24eo_5fto_5fsmt s1 v8 _ hinv1 h64 (hG.rem hrem) h_v8 as ⟨v10, s2, hinv2, h_v10⟩ growing hG carrying h_v2 h_v5 dropping h_v7 h_v8 h_v9 hinv1 s1 v7 v8 v9
  store_step with ih.eo__24eo_5fto_5fsmt s2 v5 _ hinv2 h64 (hG.rem hrem) h_v5 as ⟨v11, s3, hinv3, h_v11⟩ growing hG carrying h_v2 h_v10 dropping h_v5 hinv2 s2 v5
  store_step with ih.eo__24eo_5fto_5fsmt s3 v2 _ hinv3 h64 (hG.rem hrem) h_v2 as ⟨v12, s4, hinv4, h_v12⟩ growing hG carrying h_v10 h_v11 dropping h_v2 hinv3 s3 v2
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo__24emb_5fsm_2estr_2ereplace_5fre_5fall.construct s4 e_v13 (by rw [he_v13]; rfl) h_v10 h_v11 h_v12 hinv4 h64 as ⟨v13, s5, hinv5, h_v13⟩ growing hG carrying dropping h_v10 h_v11 h_v12 he_v13 hinv4 e_v13 s4 v10 v11 v12
  case_done hinv5 hG with h_v13 in EoCases.__eo_to_smt.case_118 using hn_v1 hn_v2 hn_v4 hn_v5 hn_v7 hn_v8

theorem case_119_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_119_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_119 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_119 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_119_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_119
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_119
  pat_unapply h_v4 as ⟨v7, v8, x_v7, x_v8, h_v7, h_v8, hn_v7, hn_v8⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_119
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_str_2eindexof_5fre.construct s e_v9 (by rw [he_v9]; exact empty_args) hinv h64 as ⟨v9, s1, hinv1, h_v9⟩ growing hG carrying h_v2 h_v5 h_v7 h_v8 dropping h_a0 h_v1 h_v4 he_v9 e_v9 v1 v4
  pat_same v7 v9 with h_v7 h_v9 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_119
  store_step with ih.eo__24eo_5fto_5fsmt s1 v8 _ hinv1 h64 (hG.rem hrem) h_v8 as ⟨v10, s2, hinv2, h_v10⟩ growing hG carrying h_v2 h_v5 dropping h_v7 h_v8 h_v9 hinv1 s1 v7 v8 v9
  store_step with ih.eo__24eo_5fto_5fsmt s2 v5 _ hinv2 h64 (hG.rem hrem) h_v5 as ⟨v11, s3, hinv3, h_v11⟩ growing hG carrying h_v2 h_v10 dropping h_v5 hinv2 s2 v5
  store_step with ih.eo__24eo_5fto_5fsmt s3 v2 _ hinv3 h64 (hG.rem hrem) h_v2 as ⟨v12, s4, hinv4, h_v12⟩ growing hG carrying h_v10 h_v11 dropping h_v2 hinv3 s3 v2
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo__24emb_5fsm_2estr_2eindexof_5fre.construct s4 e_v13 (by rw [he_v13]; rfl) h_v10 h_v11 h_v12 hinv4 h64 as ⟨v13, s5, hinv5, h_v13⟩ growing hG carrying dropping h_v10 h_v11 h_v12 he_v13 hinv4 e_v13 s4 v10 v11 v12
  case_done hinv5 hG with h_v13 in EoCases.__eo_to_smt.case_119 using hn_v1 hn_v2 hn_v4 hn_v5 hn_v7 hn_v8

theorem case_120_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_120_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_120 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_120 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_120_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_re_2eallchar.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 dropping he_v0 e_v0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_120
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24emb_5fsm_2ere_2eallchar.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying dropping h_a0 h_v0 he_v1 hinv1 e_v1 s1 v0
  case_done hinv2 hG with h_v1 in EoCases.__eo_to_smt.case_120 using

theorem case_121_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_121_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_121 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_121 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_121_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_re_2enone.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 dropping he_v0 e_v0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_121
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24emb_5fsm_2ere_2enone.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying dropping h_a0 h_v0 he_v1 hinv1 e_v1 s1 v0
  case_done hinv2 hG with h_v1 in EoCases.__eo_to_smt.case_121 using

theorem case_122_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_122_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_122 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_122 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_122_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_re_2eall.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 dropping he_v0 e_v0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_122
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24emb_5fsm_2ere_2eall.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying dropping h_a0 h_v0 he_v1 hinv1 e_v1 s1 v0
  case_done hinv2 hG with h_v1 in EoCases.__eo_to_smt.case_122 using

theorem case_123_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_123_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_123 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_123 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_123_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_123
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_str_2eto_5fre.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v1 h_v2 dropping h_a0 he_v3 e_v3
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_123
  store_step with ih.eo__24eo_5fto_5fsmt s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying dropping h_v1 h_v2 h_v3 hinv1 s1 v1 v2 v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5fsm_2estr_2eto_5fre.construct s2 e_v5 (by rw [he_v5]; rfl) h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying dropping h_v4 he_v5 hinv2 e_v5 s2 v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_to_smt.case_123 using hn_v1 hn_v2

theorem case_124_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_124_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_124 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_124 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_124_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_124
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_re_2e_2a.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v1 h_v2 dropping h_a0 he_v3 e_v3
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_124
  store_step with ih.eo__24eo_5fto_5fsmt s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying dropping h_v1 h_v2 h_v3 hinv1 s1 v1 v2 v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5fsm_2ere_2e_2a.construct s2 e_v5 (by rw [he_v5]; rfl) h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying dropping h_v4 he_v5 hinv2 e_v5 s2 v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_to_smt.case_124 using hn_v1 hn_v2

theorem case_125_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_125_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_125 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_125 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_125_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_125
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_re_2e_2b.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v1 h_v2 dropping h_a0 he_v3 e_v3
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_125
  store_step with ih.eo__24eo_5fto_5fsmt s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying dropping h_v1 h_v2 h_v3 hinv1 s1 v1 v2 v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5fsm_2ere_2e_2b.construct s2 e_v5 (by rw [he_v5]; rfl) h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying dropping h_v4 he_v5 hinv2 e_v5 s2 v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_to_smt.case_125 using hn_v1 hn_v2

theorem case_126_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_126_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_126 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_126 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_126_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_126
  pat_destruct CtorSpec.eo_re_2e_5e.destruct h_v1 as ⟨v4, x_v4, h_v4⟩ else hinv hG in EoCases.__eo_to_smt.case_126
  obtain hn_v4 := CtorSpec.eo_re_2e_5e.fields_ne_stuck hinv h_v1
  store_step with ih.eo__24eo_5fto_5fsmt s v4 _ hinv h64 hrem h_v4 as ⟨v5, s1, hinv1, h_v5⟩ growing hG carrying h_v2 dropping h_a0 h_v1 h_v4 v1 v4
  store_step with ih.eo__24eo_5fto_5fsmt s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v6, s2, hinv2, h_v6⟩ growing hG carrying h_v5 dropping h_v2 hinv1 s1 v2
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo__24emb_5fsm_2ere_2e_5e.construct s2 e_v7 (by rw [he_v7]; rfl) h_v5 h_v6 hinv2 h64 as ⟨v7, s3, hinv3, h_v7⟩ growing hG carrying dropping h_v5 h_v6 he_v7 hinv2 e_v7 s2 v5 v6
  case_done hinv3 hG with h_v7 in EoCases.__eo_to_smt.case_126 using hn_v1 hn_v2 hn_v4

theorem case_127_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_127_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_127 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_127 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_127_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_127
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_re_2eopt.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v1 h_v2 dropping h_a0 he_v3 e_v3
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_127
  store_step with ih.eo__24eo_5fto_5fsmt s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying dropping h_v1 h_v2 h_v3 hinv1 s1 v1 v2 v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5fsm_2ere_2eopt.construct s2 e_v5 (by rw [he_v5]; rfl) h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying dropping h_v4 he_v5 hinv2 e_v5 s2 v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_to_smt.case_127 using hn_v1 hn_v2

theorem case_128_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_128_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_128 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_128 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_128_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_128
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_re_2ecomp.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v1 h_v2 dropping h_a0 he_v3 e_v3
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_128
  store_step with ih.eo__24eo_5fto_5fsmt s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying dropping h_v1 h_v2 h_v3 hinv1 s1 v1 v2 v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5fsm_2ere_2ecomp.construct s2 e_v5 (by rw [he_v5]; rfl) h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying dropping h_v4 he_v5 hinv2 e_v5 s2 v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_to_smt.case_128 using hn_v1 hn_v2

theorem case_129_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_129_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_129 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_129 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_129_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_129
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_129
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_re_2erange.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_129
  store_step with ih.eo__24eo_5fto_5fsmt s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 dropping h_v4 h_v5 h_v6 hinv1 s1 v4 v5 v6
  store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v7 dropping h_v2 hinv2 s2 v2
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fsm_2ere_2erange.construct s3 e_v9 (by rw [he_v9]; rfl) h_v7 h_v8 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying dropping h_v7 h_v8 he_v9 hinv3 e_v9 s3 v7 v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_to_smt.case_129 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_130_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_130_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_130 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_130 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_130_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_130
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_130
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_re_2e_2b_2b.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_130
  store_step with ih.eo__24eo_5fto_5fsmt s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 dropping h_v4 h_v5 h_v6 hinv1 s1 v4 v5 v6
  store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v7 dropping h_v2 hinv2 s2 v2
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fsm_2ere_2e_2b_2b.construct s3 e_v9 (by rw [he_v9]; rfl) h_v7 h_v8 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying dropping h_v7 h_v8 he_v9 hinv3 e_v9 s3 v7 v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_to_smt.case_130 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_131_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_131_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_131 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_131 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_131_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_131
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_131
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_re_2einter.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_131
  store_step with ih.eo__24eo_5fto_5fsmt s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 dropping h_v4 h_v5 h_v6 hinv1 s1 v4 v5 v6
  store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v7 dropping h_v2 hinv2 s2 v2
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fsm_2ere_2einter.construct s3 e_v9 (by rw [he_v9]; rfl) h_v7 h_v8 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying dropping h_v7 h_v8 he_v9 hinv3 e_v9 s3 v7 v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_to_smt.case_131 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_132_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_132_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_132 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_132 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_132_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_132
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_132
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_re_2eunion.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_132
  store_step with ih.eo__24eo_5fto_5fsmt s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 dropping h_v4 h_v5 h_v6 hinv1 s1 v4 v5 v6
  store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v7 dropping h_v2 hinv2 s2 v2
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fsm_2ere_2eunion.construct s3 e_v9 (by rw [he_v9]; rfl) h_v7 h_v8 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying dropping h_v7 h_v8 he_v9 hinv3 e_v9 s3 v7 v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_to_smt.case_132 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_133_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_133_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_133 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_133 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_133_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_133
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_133
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_re_2ediff.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_133
  store_step with ih.eo__24eo_5fto_5fsmt s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 dropping h_v4 h_v5 h_v6 hinv1 s1 v4 v5 v6
  store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v7 dropping h_v2 hinv2 s2 v2
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fsm_2ere_2ediff.construct s3 e_v9 (by rw [he_v9]; rfl) h_v7 h_v8 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying dropping h_v7 h_v8 he_v9 hinv3 e_v9 s3 v7 v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_to_smt.case_133 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_134_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_134_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_134 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_134 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_134_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_134
  pat_destruct CtorSpec.eo_re_2eloop.destruct h_v1 as ⟨v4, x_v4, h_v4⟩ ⟨v5, x_v5, h_v5⟩ else hinv hG in EoCases.__eo_to_smt.case_134
  obtain ⟨hn_v4, hn_v5⟩ := CtorSpec.eo_re_2eloop.fields_ne_stuck hinv h_v1
  store_step with ih.eo__24eo_5fto_5fsmt s v4 _ hinv h64 hrem h_v4 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v5 dropping h_a0 h_v1 h_v4 v1 v4
  store_step with ih.eo__24eo_5fto_5fsmt s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 h_v6 dropping h_v5 hinv1 s1 v5
  store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v6 h_v7 dropping h_v2 hinv2 s2 v2
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fsm_2ere_2eloop.construct s3 e_v9 (by rw [he_v9]; rfl) h_v6 h_v7 h_v8 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying dropping h_v6 h_v7 h_v8 he_v9 hinv3 e_v9 s3 v6 v7 v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_to_smt.case_134 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_135_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_135_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_135 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_135 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_135_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_135
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_135
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_str_2ein_5fre.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_135
  store_step with ih.eo__24eo_5fto_5fsmt s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 dropping h_v4 h_v5 h_v6 hinv1 s1 v4 v5 v6
  store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v7 dropping h_v2 hinv2 s2 v2
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fsm_2estr_2ein_5fre.construct s3 e_v9 (by rw [he_v9]; rfl) h_v7 h_v8 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying dropping h_v7 h_v8 he_v9 hinv3 e_v9 s3 v7 v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_to_smt.case_135 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_136_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_136_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_136 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_136 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_136_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_136
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_seq_2eunit.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v1 h_v2 dropping h_a0 he_v3 e_v3
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_136
  store_step with ih.eo__24eo_5fto_5fsmt s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying dropping h_v1 h_v2 h_v3 hinv1 s1 v1 v2 v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eseq_2eunit.construct s2 e_v5 (by rw [he_v5]; rfl) h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying dropping h_v4 he_v5 hinv2 e_v5 s2 v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_to_smt.case_136 using hn_v1 hn_v2

theorem case_137_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_137_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_137 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_137 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_137_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_137
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_137
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_seq_2enth.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_137
  store_step with ih.eo__24eo_5fto_5fsmt s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 dropping h_v4 h_v5 h_v6 hinv1 s1 v4 v5 v6
  store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v7 dropping h_v2 hinv2 s2 v2
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eseq_2enth.construct s3 e_v9 (by rw [he_v9]; rfl) h_v7 h_v8 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying dropping h_v7 h_v8 he_v9 hinv3 e_v9 s3 v7 v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_to_smt.case_137 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_138_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_138_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_138 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_138 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_138_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__40re_5funfold_5fpos_5fcomponent.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ ⟨v3, x_v3, h_v3⟩ else hinv hG in EoCases.__eo_to_smt.case_138
  obtain ⟨hn_v1, hn_v2, hn_v3⟩ := CtorSpec.eo__40re_5funfold_5fpos_5fcomponent.fields_ne_stuck hinv h_a0
  store_step with ih.eo__24eo_5fto_5fsmt_5fnat_5fis_5fvalid s v3 _ hinv h64 hrem h_v3 as ⟨v4, s1, hinv1, h_v4⟩ growing hG carrying h_v1 h_v2 h_v3 dropping h_a0
  have h_ite_v10 := (show if_9_eo__24eo_5fto_5fsmt s1 v4 v1 v2 v3 ⦃ r s' => s'.Inv ∧ s1.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_9_eo__24eo_5fto_5fsmt
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s1
    rcases Store.boolean_value_native h_v4 with ⟨hx_5, hbv_5⟩ | ⟨hx_5, hbv_5⟩
    · ite_branch hbv_5
      store_step with ih.eo__24eo_5fto_5fsmt s1 v1 _ hinv1 h64 (hG.rem hrem) h_v1 as ⟨v5, s2, hinv2, h_v5⟩ growing hG carrying h_v2 h_v3 dropping h_v1 h_v4 v1 v4
      store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v6, s3, hinv3, h_v6⟩ growing hG carrying h_v3 h_v5 dropping h_v2 v2
      store_step with ih.eo__24eo_5fto_5fsmt_5fnat s3 v3 _ hinv3 h64 (hG.rem hrem) h_v3 as ⟨v7, s4, hinv4, h_v7⟩ growing hG carrying h_v5 h_v6 dropping h_v3 hinv3 s3 v3
      store_step with ih.eo__24eo_5fto_5fsmt_5fre_5funfold_5fpos_5fcomponent s4 v5 v6 v7 _ _ _ hinv4 h64 (hG.rem hrem) h_v5 h_v6 h_v7 as ⟨v8, s5, hinv5, h_v8⟩ growing hG carrying dropping h_v5 h_v6 h_v7 hinv4 s4 v5 v6 v7
      ite_done hinv5 hG with (native_ite_true_rep _ hx_5 h_v8)
    · ite_branch hbv_5
      step as ⟨e_v9, he_v9⟩
      store_step with CtorSpec.eo__24emb_5fsm_2eNone.construct s1 e_v9 (by rw [he_v9]; exact empty_args) hinv1 h64 as ⟨v9, s2, hinv2, h_v9⟩ growing hG carrying dropping h_v1 h_v2 h_v3 h_v4 he_v9 hinv1 e_v9 s1 v1 v2 v3 v4
      ite_done hinv2 hG with (native_ite_false_rep _ hx_5 h_v9))
  store_step with h_ite_v10 as ⟨v10, s2, hinv2, h_v10⟩ growing hG carrying dropping h_ite_v10 h_v1 h_v2 h_v3 h_v4 hinv1 s1 v1 v2 v3 v4
  case_done hinv2 hG with h_v10 in EoCases.__eo_to_smt.case_138 using hn_v1 hn_v2 hn_v3

theorem case_139_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_139_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_139 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_139 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_139_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_139
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_139
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__40strings_5fdeq_5fdiff.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_139
  store_step with ih.eo__24eo_5fto_5fsmt s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 dropping h_v4 h_v5 h_v6 hinv1 s1 v4 v5 v6
  store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v7 dropping h_v2 hinv2 s2 v2
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eseq_5fdiff.construct s3 e_v9 (by rw [he_v9]; rfl) h_v7 h_v8 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying dropping h_v7 h_v8 he_v9 hinv3 e_v9 s3 v7 v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_to_smt.case_139 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_140_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_140_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_140 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_140 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_140_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_140
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_140
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__40strings_5fstoi_5fresult.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_140
  store_step with ih.eo__24eo_5fto_5fsmt s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 h_v5 dropping h_v4 h_v6 hinv1 s1 v4 v6
  simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.raw_int_u32_spec s2 0#u32 (0) (by scalar_tac) hinv2 h64 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v2 h_v5 h_v7 dropping hinv2 s2
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eNumeral.construct s3 e_v9 (by rw [he_v9]; rfl) h_v8 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_v2 h_v5 h_v7 dropping h_v8 he_v9 hinv3 e_v9 s3 v8
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo__24emb_5fsm_2e_3d.construct s4 e_v10 (by rw [he_v10]; rfl) h_v7 h_v9 hinv4 h64 as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_v2 h_v5 dropping h_v7 h_v9 he_v10 hinv4 e_v10 s4 v7 v9
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.raw_int_u32_spec s5 0#u32 (0) (by scalar_tac) hinv5 h64 as ⟨v11, s6, hinv6, h_v11⟩ growing hG carrying h_v2 h_v5 h_v10 dropping hinv5 s5
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eNumeral.construct s6 e_v12 (by rw [he_v12]; rfl) h_v11 hinv6 h64 as ⟨v12, s7, hinv7, h_v12⟩ growing hG carrying h_v2 h_v5 h_v10 dropping h_v11 he_v12 hinv6 e_v12 s6 v11
  store_step with ih.eo__24eo_5fto_5fsmt s7 v5 _ hinv7 h64 (hG.rem hrem) h_v5 as ⟨v13, s8, hinv8, h_v13⟩ growing hG carrying h_v2 h_v10 h_v12 dropping h_v5 hinv7 s7 v5
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.raw_int_u32_spec s8 0#u32 (0) (by scalar_tac) hinv8 h64 as ⟨v14, s9, hinv9, h_v14⟩ growing hG carrying h_v2 h_v10 h_v12 h_v13 dropping hinv8 s8
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eNumeral.construct s9 e_v15 (by rw [he_v15]; rfl) h_v14 hinv9 h64 as ⟨v15, s10, hinv10, h_v15⟩ growing hG carrying h_v2 h_v10 h_v12 h_v13 dropping h_v14 he_v15 hinv9 e_v15 s9 v14
  store_step with ih.eo__24eo_5fto_5fsmt s10 v2 _ hinv10 h64 (hG.rem hrem) h_v2 as ⟨v16, s11, hinv11, h_v16⟩ growing hG carrying h_v10 h_v12 h_v13 h_v15 dropping h_v2 hinv10 s10 v2
  step as ⟨e_v17, he_v17⟩
  store_step with CtorSpec.eo__24emb_5fsm_2estr_2esubstr.construct s11 e_v17 (by rw [he_v17]; rfl) h_v13 h_v15 h_v16 hinv11 h64 as ⟨v17, s12, hinv12, h_v17⟩ growing hG carrying h_v10 h_v12 dropping h_v13 h_v15 h_v16 he_v17 hinv11 e_v17 s11 v13 v15 v16
  step as ⟨e_v18, he_v18⟩
  store_step with CtorSpec.eo__24emb_5fsm_2estr_2eto_5fint.construct s12 e_v18 (by rw [he_v18]; rfl) h_v17 hinv12 h64 as ⟨v18, s13, hinv13, h_v18⟩ growing hG carrying h_v10 h_v12 dropping h_v17 he_v18 hinv12 e_v18 s12 v17
  step as ⟨e_v19, he_v19⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eite.construct s13 e_v19 (by rw [he_v19]; rfl) h_v10 h_v12 h_v18 hinv13 h64 as ⟨v19, s14, hinv14, h_v19⟩ growing hG carrying dropping h_v10 h_v12 h_v18 he_v19 hinv13 e_v19 s13 v10 v12 v18
  case_done hinv14 hG with h_v19 in EoCases.__eo_to_smt.case_140 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_141_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_141_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_141 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_141 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_141_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_141
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__40strings_5fstoi_5fnon_5fdigit.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v1 h_v2 dropping h_a0 he_v3 e_v3
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_141
  store_step with ih.eo__24eo_5fto_5fsmt s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying dropping h_v1 h_v2 h_v3 hinv1 s1 v1 v2 v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5fsm_2ere_2eallchar.construct s2 e_v5 (by rw [he_v5]; exact empty_args) hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_v4 dropping he_v5 hinv2 e_v5 s2
  step as ⟨e_v6, he_v6⟩
  simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.raw_str_vec_spec s3 _ _ rfl hinv3 h64 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_v4 h_v5 dropping hinv3 s3
  replace h_v6 := Represents.rep_of_eq h_v6 (y := SmtEval.native_string_lit "0") (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v6]; decide)
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eString.construct s4 e_v7 (by rw [he_v7]; rfl) h_v6 hinv4 h64 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_v4 h_v5 dropping h_v6 he_v6 he_v7 hinv4 e_v6 e_v7 s4 v6
  step as ⟨e_v8, he_v8⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.raw_str_vec_spec s5 _ _ rfl hinv5 h64 as ⟨v8, s6, hinv6, h_v8⟩ growing hG carrying h_v4 h_v5 h_v7 dropping hinv5 s5
  replace h_v8 := Represents.rep_of_eq h_v8 (y := SmtEval.native_string_lit "9") (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v8]; decide)
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eString.construct s6 e_v9 (by rw [he_v9]; rfl) h_v8 hinv6 h64 as ⟨v9, s7, hinv7, h_v9⟩ growing hG carrying h_v4 h_v5 h_v7 dropping h_v8 he_v8 he_v9 hinv6 e_v8 e_v9 s6 v8
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo__24emb_5fsm_2ere_2erange.construct s7 e_v10 (by rw [he_v10]; rfl) h_v7 h_v9 hinv7 h64 as ⟨v10, s8, hinv8, h_v10⟩ growing hG carrying h_v4 h_v5 dropping h_v7 h_v9 he_v10 hinv7 e_v10 s7 v7 v9
  step as ⟨e_v11, he_v11⟩
  store_step with CtorSpec.eo__24emb_5fsm_2ere_2ecomp.construct s8 e_v11 (by rw [he_v11]; rfl) h_v10 hinv8 h64 as ⟨v11, s9, hinv9, h_v11⟩ growing hG carrying h_v4 h_v5 dropping h_v10 he_v11 hinv8 e_v11 s8 v10
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo__24emb_5fsm_2ere_2einter.construct s9 e_v12 (by rw [he_v12]; rfl) h_v5 h_v11 hinv9 h64 as ⟨v12, s10, hinv10, h_v12⟩ growing hG carrying h_v4 dropping h_v11 h_v5 he_v12 hinv9 e_v12 s9 v11 v5
  simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.raw_int_u32_spec s10 0#u32 (0) (by scalar_tac) hinv10 h64 as ⟨v13, s11, hinv11, h_v13⟩ growing hG carrying h_v4 h_v12 dropping hinv10 s10
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eNumeral.construct s11 e_v14 (by rw [he_v14]; rfl) h_v13 hinv11 h64 as ⟨v14, s12, hinv12, h_v14⟩ growing hG carrying h_v4 h_v12 dropping h_v13 he_v14 hinv11 e_v14 s11 v13
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__24emb_5fsm_2estr_2eindexof_5fre.construct s12 e_v15 (by rw [he_v15]; rfl) h_v4 h_v12 h_v14 hinv12 h64 as ⟨v15, s13, hinv13, h_v15⟩ growing hG carrying dropping h_v12 h_v14 h_v4 he_v15 hinv12 e_v15 s12 v12 v14 v4
  case_done hinv13 hG with h_v15 in EoCases.__eo_to_smt.case_141 using hn_v1 hn_v2

theorem case_142_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_142_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_142 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_142 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_142_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_142
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_142
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__40strings_5fitos_5fresult.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_142
  store_step with ih.eo__24eo_5fto_5fsmt s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 h_v5 dropping h_v4 h_v6 hinv1 s1 v4 v6
  simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.raw_int_u32_spec s2 0#u32 (0) (by scalar_tac) hinv2 h64 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v2 h_v5 h_v7 dropping hinv2 s2
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eNumeral.construct s3 e_v9 (by rw [he_v9]; rfl) h_v8 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_v2 h_v5 h_v7 dropping h_v8 he_v9 hinv3 e_v9 s3 v8
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo__24emb_5fsm_2e_3d.construct s4 e_v10 (by rw [he_v10]; rfl) h_v7 h_v9 hinv4 h64 as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_v2 h_v5 dropping h_v7 h_v9 he_v10 hinv4 e_v10 s4 v7 v9
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.raw_int_u32_spec s5 0#u32 (0) (by scalar_tac) hinv5 h64 as ⟨v11, s6, hinv6, h_v11⟩ growing hG carrying h_v2 h_v5 h_v10 dropping hinv5 s5
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eNumeral.construct s6 e_v12 (by rw [he_v12]; rfl) h_v11 hinv6 h64 as ⟨v12, s7, hinv7, h_v12⟩ growing hG carrying h_v2 h_v5 h_v10 dropping h_v11 he_v12 hinv6 e_v12 s6 v11
  store_step with ih.eo__24eo_5fto_5fsmt s7 v5 _ hinv7 h64 (hG.rem hrem) h_v5 as ⟨v13, s8, hinv8, h_v13⟩ growing hG carrying h_v2 h_v10 h_v12 dropping h_v5 hinv7 s7 v5
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo__24emb_5fsm_2estr_2efrom_5fint.construct s8 e_v14 (by rw [he_v14]; rfl) h_v13 hinv8 h64 as ⟨v14, s9, hinv9, h_v14⟩ growing hG carrying h_v2 h_v10 h_v12 dropping h_v13 he_v14 hinv8 e_v14 s8 v13
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.raw_int_u32_spec s9 0#u32 (0) (by scalar_tac) hinv9 h64 as ⟨v15, s10, hinv10, h_v15⟩ growing hG carrying h_v2 h_v10 h_v12 h_v14 dropping hinv9 s9
  step as ⟨e_v16, he_v16⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eNumeral.construct s10 e_v16 (by rw [he_v16]; rfl) h_v15 hinv10 h64 as ⟨v16, s11, hinv11, h_v16⟩ growing hG carrying h_v2 h_v10 h_v12 h_v14 dropping h_v15 he_v16 hinv10 e_v16 s10 v15
  store_step with ih.eo__24eo_5fto_5fsmt s11 v2 _ hinv11 h64 (hG.rem hrem) h_v2 as ⟨v17, s12, hinv12, h_v17⟩ growing hG carrying h_v10 h_v12 h_v14 h_v16 dropping h_v2 hinv11 s11 v2
  step as ⟨e_v18, he_v18⟩
  store_step with CtorSpec.eo__24emb_5fsm_2estr_2esubstr.construct s12 e_v18 (by rw [he_v18]; rfl) h_v14 h_v16 h_v17 hinv12 h64 as ⟨v18, s13, hinv13, h_v18⟩ growing hG carrying h_v10 h_v12 dropping h_v14 h_v16 h_v17 he_v18 hinv12 e_v18 s12 v14 v16 v17
  step as ⟨e_v19, he_v19⟩
  store_step with CtorSpec.eo__24emb_5fsm_2estr_2eto_5fint.construct s13 e_v19 (by rw [he_v19]; rfl) h_v18 hinv13 h64 as ⟨v19, s14, hinv14, h_v19⟩ growing hG carrying h_v10 h_v12 dropping h_v18 he_v19 hinv13 e_v19 s13 v18
  step as ⟨e_v20, he_v20⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eite.construct s14 e_v20 (by rw [he_v20]; rfl) h_v10 h_v12 h_v19 hinv14 h64 as ⟨v20, s15, hinv15, h_v20⟩ growing hG carrying dropping h_v10 h_v12 h_v19 he_v20 hinv14 e_v20 s14 v10 v12 v19
  case_done hinv15 hG with h_v20 in EoCases.__eo_to_smt.case_142 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_143_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_143_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_143 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_143 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_143_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_143
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_143
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__40strings_5fnum_5foccur.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_143
  store_step with ih.eo__24eo_5fto_5fsmt s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 h_v5 dropping h_v4 h_v6 hinv1 s1 v4 v6
  store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v2 h_v5 h_v7 dropping hinv2 s2
  store_step with ih.eo__24eo_5fto_5fsmt s3 v5 _ hinv3 h64 (hG.rem hrem) h_v5 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_v2 h_v5 h_v7 h_v8 dropping hinv3 s3
  simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.raw_int_u32_spec s4 0#u32 (0) (by scalar_tac) hinv4 h64 as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_v2 h_v5 h_v7 h_v8 h_v9 dropping hinv4 s4
  step as ⟨e_v11, he_v11⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eNumeral.construct s5 e_v11 (by rw [he_v11]; rfl) h_v10 hinv5 h64 as ⟨v11, s6, hinv6, h_v11⟩ growing hG carrying h_v2 h_v5 h_v7 h_v8 h_v9 dropping h_v10 he_v11 hinv5 e_v11 s5 v10
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.raw_int_u32_spec s6 1#u32 (1) (by scalar_tac) hinv6 h64 as ⟨v12, s7, hinv7, h_v12⟩ growing hG carrying h_v2 h_v5 h_v7 h_v8 h_v9 h_v11 dropping hinv6 s6
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eNumeral.construct s7 e_v13 (by rw [he_v13]; rfl) h_v12 hinv7 h64 as ⟨v13, s8, hinv8, h_v13⟩ growing hG carrying h_v2 h_v5 h_v7 h_v8 h_v9 h_v11 dropping h_v12 he_v13 hinv7 e_v13 s7 v12
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo__24emb_5fsm_2estr_2esubstr.construct s8 e_v14 (by rw [he_v14]; rfl) h_v9 h_v11 h_v13 hinv8 h64 as ⟨v14, s9, hinv9, h_v14⟩ growing hG carrying h_v2 h_v5 h_v7 h_v8 dropping h_v11 h_v13 h_v9 he_v14 hinv8 e_v14 s8 v11 v13 v9
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__24emb_5fsm_2estr_2ereplace_5fall.construct s9 e_v15 (by rw [he_v15]; rfl) h_v7 h_v8 h_v14 hinv9 h64 as ⟨v15, s10, hinv10, h_v15⟩ growing hG carrying h_v2 h_v5 dropping h_v14 h_v7 h_v8 he_v15 hinv9 e_v15 s9 v14 v7 v8
  step as ⟨e_v16, he_v16⟩
  store_step with CtorSpec.eo__24emb_5fsm_2estr_2elen.construct s10 e_v16 (by rw [he_v16]; rfl) h_v15 hinv10 h64 as ⟨v16, s11, hinv11, h_v16⟩ growing hG carrying h_v2 h_v5 dropping h_v15 he_v16 hinv10 e_v16 s10 v15
  store_step with ih.eo__24eo_5fto_5fsmt s11 v5 _ hinv11 h64 (hG.rem hrem) h_v5 as ⟨v17, s12, hinv12, h_v17⟩ growing hG carrying h_v2 h_v5 h_v16 dropping hinv11 s11
  store_step with ih.eo__24eo_5fto_5fsmt s12 v2 _ hinv12 h64 (hG.rem hrem) h_v2 as ⟨v18, s13, hinv13, h_v18⟩ growing hG carrying h_v5 h_v16 h_v17 dropping h_v2 hinv12 s12 v2
  store_step with ih.eo__24eo_5fto_5fsmt s13 v5 _ hinv13 h64 (hG.rem hrem) h_v5 as ⟨v19, s14, hinv14, h_v19⟩ growing hG carrying h_v16 h_v17 h_v18 dropping h_v5 hinv13 s13 v5
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.raw_int_u32_spec s14 0#u32 (0) (by scalar_tac) hinv14 h64 as ⟨v20, s15, hinv15, h_v20⟩ growing hG carrying h_v16 h_v17 h_v18 h_v19 dropping hinv14 s14
  step as ⟨e_v21, he_v21⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eNumeral.construct s15 e_v21 (by rw [he_v21]; rfl) h_v20 hinv15 h64 as ⟨v21, s16, hinv16, h_v21⟩ growing hG carrying h_v16 h_v17 h_v18 h_v19 dropping h_v20 he_v21 hinv15 e_v21 s15 v20
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.raw_int_u32_spec s16 0#u32 (0) (by scalar_tac) hinv16 h64 as ⟨v22, s17, hinv17, h_v22⟩ growing hG carrying h_v16 h_v17 h_v18 h_v19 h_v21 dropping hinv16 s16
  step as ⟨e_v23, he_v23⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eNumeral.construct s17 e_v23 (by rw [he_v23]; rfl) h_v22 hinv17 h64 as ⟨v23, s18, hinv18, h_v23⟩ growing hG carrying h_v16 h_v17 h_v18 h_v19 h_v21 dropping h_v22 he_v23 hinv17 e_v23 s17 v22
  step as ⟨e_v24, he_v24⟩
  store_step with CtorSpec.eo__24emb_5fsm_2estr_2esubstr.construct s18 e_v24 (by rw [he_v24]; rfl) h_v19 h_v21 h_v23 hinv18 h64 as ⟨v24, s19, hinv19, h_v24⟩ growing hG carrying h_v16 h_v17 h_v18 dropping h_v19 h_v21 h_v23 he_v24 hinv18 e_v24 s18 v19 v21 v23
  step as ⟨e_v25, he_v25⟩
  store_step with CtorSpec.eo__24emb_5fsm_2estr_2ereplace_5fall.construct s19 e_v25 (by rw [he_v25]; rfl) h_v17 h_v18 h_v24 hinv19 h64 as ⟨v25, s20, hinv20, h_v25⟩ growing hG carrying h_v16 dropping h_v17 h_v18 h_v24 he_v25 hinv19 e_v25 s19 v17 v18 v24
  step as ⟨e_v26, he_v26⟩
  store_step with CtorSpec.eo__24emb_5fsm_2estr_2elen.construct s20 e_v26 (by rw [he_v26]; rfl) h_v25 hinv20 h64 as ⟨v26, s21, hinv21, h_v26⟩ growing hG carrying h_v16 dropping h_v25 he_v26 hinv20 e_v26 s20 v25
  step as ⟨e_v27, he_v27⟩
  store_step with CtorSpec.eo__24emb_5fsm_2e_2d.construct s21 e_v27 (by rw [he_v27]; rfl) h_v16 h_v26 hinv21 h64 as ⟨v27, s22, hinv22, h_v27⟩ growing hG carrying dropping h_v16 h_v26 he_v27 hinv21 e_v27 s21 v16 v26
  case_done hinv22 hG with h_v27 in EoCases.__eo_to_smt.case_143 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_144_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_144_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_144 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_144 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_144_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_144
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_144
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__40strings_5fnum_5foccur_5fre.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_144
  store_step with ih.eo__24eo_5fto_5fsmt s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 h_v5 dropping h_v4 h_v6 hinv1 s1 v4 v6
  store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v2 h_v5 h_v7 dropping hinv2 s2
  store_step with ih.eo__24eo_5fto_5fsmt s3 v5 _ hinv3 h64 (hG.rem hrem) h_v5 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_v2 h_v5 h_v7 h_v8 dropping hinv3 s3
  simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.raw_int_u32_spec s4 0#u32 (0) (by scalar_tac) hinv4 h64 as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_v2 h_v5 h_v7 h_v8 h_v9 dropping hinv4 s4
  step as ⟨e_v11, he_v11⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eNumeral.construct s5 e_v11 (by rw [he_v11]; rfl) h_v10 hinv5 h64 as ⟨v11, s6, hinv6, h_v11⟩ growing hG carrying h_v2 h_v5 h_v7 h_v8 h_v9 dropping h_v10 he_v11 hinv5 e_v11 s5 v10
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.raw_int_u32_spec s6 1#u32 (1) (by scalar_tac) hinv6 h64 as ⟨v12, s7, hinv7, h_v12⟩ growing hG carrying h_v2 h_v5 h_v7 h_v8 h_v9 h_v11 dropping hinv6 s6
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eNumeral.construct s7 e_v13 (by rw [he_v13]; rfl) h_v12 hinv7 h64 as ⟨v13, s8, hinv8, h_v13⟩ growing hG carrying h_v2 h_v5 h_v7 h_v8 h_v9 h_v11 dropping h_v12 he_v13 hinv7 e_v13 s7 v12
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo__24emb_5fsm_2estr_2esubstr.construct s8 e_v14 (by rw [he_v14]; rfl) h_v9 h_v11 h_v13 hinv8 h64 as ⟨v14, s9, hinv9, h_v14⟩ growing hG carrying h_v2 h_v5 h_v7 h_v8 dropping h_v11 h_v13 h_v9 he_v14 hinv8 e_v14 s8 v11 v13 v9
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__24emb_5fsm_2estr_2ereplace_5fre_5fall.construct s9 e_v15 (by rw [he_v15]; rfl) h_v7 h_v8 h_v14 hinv9 h64 as ⟨v15, s10, hinv10, h_v15⟩ growing hG carrying h_v2 h_v5 dropping h_v14 h_v7 h_v8 he_v15 hinv9 e_v15 s9 v14 v7 v8
  step as ⟨e_v16, he_v16⟩
  store_step with CtorSpec.eo__24emb_5fsm_2estr_2elen.construct s10 e_v16 (by rw [he_v16]; rfl) h_v15 hinv10 h64 as ⟨v16, s11, hinv11, h_v16⟩ growing hG carrying h_v2 h_v5 dropping h_v15 he_v16 hinv10 e_v16 s10 v15
  store_step with ih.eo__24eo_5fto_5fsmt s11 v5 _ hinv11 h64 (hG.rem hrem) h_v5 as ⟨v17, s12, hinv12, h_v17⟩ growing hG carrying h_v2 h_v5 h_v16 dropping hinv11 s11
  store_step with ih.eo__24eo_5fto_5fsmt s12 v2 _ hinv12 h64 (hG.rem hrem) h_v2 as ⟨v18, s13, hinv13, h_v18⟩ growing hG carrying h_v5 h_v16 h_v17 dropping h_v2 hinv12 s12 v2
  store_step with ih.eo__24eo_5fto_5fsmt s13 v5 _ hinv13 h64 (hG.rem hrem) h_v5 as ⟨v19, s14, hinv14, h_v19⟩ growing hG carrying h_v16 h_v17 h_v18 dropping h_v5 hinv13 s13 v5
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.raw_int_u32_spec s14 0#u32 (0) (by scalar_tac) hinv14 h64 as ⟨v20, s15, hinv15, h_v20⟩ growing hG carrying h_v16 h_v17 h_v18 h_v19 dropping hinv14 s14
  step as ⟨e_v21, he_v21⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eNumeral.construct s15 e_v21 (by rw [he_v21]; rfl) h_v20 hinv15 h64 as ⟨v21, s16, hinv16, h_v21⟩ growing hG carrying h_v16 h_v17 h_v18 h_v19 dropping h_v20 he_v21 hinv15 e_v21 s15 v20
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.raw_int_u32_spec s16 0#u32 (0) (by scalar_tac) hinv16 h64 as ⟨v22, s17, hinv17, h_v22⟩ growing hG carrying h_v16 h_v17 h_v18 h_v19 h_v21 dropping hinv16 s16
  step as ⟨e_v23, he_v23⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eNumeral.construct s17 e_v23 (by rw [he_v23]; rfl) h_v22 hinv17 h64 as ⟨v23, s18, hinv18, h_v23⟩ growing hG carrying h_v16 h_v17 h_v18 h_v19 h_v21 dropping h_v22 he_v23 hinv17 e_v23 s17 v22
  step as ⟨e_v24, he_v24⟩
  store_step with CtorSpec.eo__24emb_5fsm_2estr_2esubstr.construct s18 e_v24 (by rw [he_v24]; rfl) h_v19 h_v21 h_v23 hinv18 h64 as ⟨v24, s19, hinv19, h_v24⟩ growing hG carrying h_v16 h_v17 h_v18 dropping h_v19 h_v21 h_v23 he_v24 hinv18 e_v24 s18 v19 v21 v23
  step as ⟨e_v25, he_v25⟩
  store_step with CtorSpec.eo__24emb_5fsm_2estr_2ereplace_5fre_5fall.construct s19 e_v25 (by rw [he_v25]; rfl) h_v17 h_v18 h_v24 hinv19 h64 as ⟨v25, s20, hinv20, h_v25⟩ growing hG carrying h_v16 dropping h_v17 h_v18 h_v24 he_v25 hinv19 e_v25 s19 v17 v18 v24
  step as ⟨e_v26, he_v26⟩
  store_step with CtorSpec.eo__24emb_5fsm_2estr_2elen.construct s20 e_v26 (by rw [he_v26]; rfl) h_v25 hinv20 h64 as ⟨v26, s21, hinv21, h_v26⟩ growing hG carrying h_v16 dropping h_v25 he_v26 hinv20 e_v26 s20 v25
  step as ⟨e_v27, he_v27⟩
  store_step with CtorSpec.eo__24emb_5fsm_2e_2d.construct s21 e_v27 (by rw [he_v27]; rfl) h_v16 h_v26 hinv21 h64 as ⟨v27, s22, hinv22, h_v27⟩ growing hG carrying dropping h_v16 h_v26 he_v27 hinv21 e_v27 s21 v16 v26
  case_done hinv22 hG with h_v27 in EoCases.__eo_to_smt.case_144 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_145_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_145_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_145 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_145 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_145_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_145
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_145
  pat_unapply h_v4 as ⟨v7, v8, x_v7, x_v8, h_v7, h_v8, hn_v7, hn_v8⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_145
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__40strings_5foccur_5findex.construct s e_v9 (by rw [he_v9]; exact empty_args) hinv h64 as ⟨v9, s1, hinv1, h_v9⟩ growing hG carrying h_v2 h_v5 h_v7 h_v8 dropping h_a0 h_v1 h_v4 he_v9 e_v9 v1 v4
  pat_same v7 v9 with h_v7 h_v9 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_145
  store_step with ih.eo__24eo_5fto_5fsmt s1 v8 _ hinv1 h64 (hG.rem hrem) h_v8 as ⟨v10, s2, hinv2, h_v10⟩ growing hG carrying h_v2 h_v5 dropping h_v7 h_v8 h_v9 hinv1 s1 v7 v8 v9
  store_step with ih.eo__24eo_5fto_5fsmt s2 v5 _ hinv2 h64 (hG.rem hrem) h_v5 as ⟨v11, s3, hinv3, h_v11⟩ growing hG carrying h_v2 h_v10 dropping h_v5 hinv2 s2 v5
  store_step with ih.eo__24eo_5fto_5fsmt s3 v2 _ hinv3 h64 (hG.rem hrem) h_v2 as ⟨v12, s4, hinv4, h_v12⟩ growing hG carrying h_v10 h_v11 dropping h_v2 hinv3 s3 v2
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo__24emb_5fsm_2e_40strings_5foccur_5findex.construct s4 e_v13 (by rw [he_v13]; rfl) h_v10 h_v11 h_v12 hinv4 h64 as ⟨v13, s5, hinv5, h_v13⟩ growing hG carrying dropping h_v10 h_v11 h_v12 he_v13 hinv4 e_v13 s4 v10 v11 v12
  case_done hinv5 hG with h_v13 in EoCases.__eo_to_smt.case_145 using hn_v1 hn_v2 hn_v4 hn_v5 hn_v7 hn_v8

theorem case_146_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_146_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_146 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_146 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_146_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_146
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_146
  pat_unapply h_v4 as ⟨v7, v8, x_v7, x_v8, h_v7, h_v8, hn_v7, hn_v8⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_146
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__40strings_5foccur_5findex_5fre.construct s e_v9 (by rw [he_v9]; exact empty_args) hinv h64 as ⟨v9, s1, hinv1, h_v9⟩ growing hG carrying h_v2 h_v5 h_v7 h_v8 dropping h_a0 h_v1 h_v4 he_v9 e_v9 v1 v4
  pat_same v7 v9 with h_v7 h_v9 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_146
  store_step with ih.eo__24eo_5fto_5fsmt s1 v8 _ hinv1 h64 (hG.rem hrem) h_v8 as ⟨v10, s2, hinv2, h_v10⟩ growing hG carrying h_v2 h_v5 dropping h_v7 h_v8 h_v9 hinv1 s1 v7 v8 v9
  store_step with ih.eo__24eo_5fto_5fsmt s2 v5 _ hinv2 h64 (hG.rem hrem) h_v5 as ⟨v11, s3, hinv3, h_v11⟩ growing hG carrying h_v2 h_v10 dropping h_v5 hinv2 s2 v5
  store_step with ih.eo__24eo_5fto_5fsmt s3 v2 _ hinv3 h64 (hG.rem hrem) h_v2 as ⟨v12, s4, hinv4, h_v12⟩ growing hG carrying h_v10 h_v11 dropping h_v2 hinv3 s3 v2
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo__24emb_5fsm_2e_40strings_5foccur_5findex_5fre.construct s4 e_v13 (by rw [he_v13]; rfl) h_v10 h_v11 h_v12 hinv4 h64 as ⟨v13, s5, hinv5, h_v13⟩ growing hG carrying dropping h_v10 h_v11 h_v12 he_v13 hinv4 e_v13 s4 v10 v11 v12
  case_done hinv5 hG with h_v13 in EoCases.__eo_to_smt.case_146 using hn_v1 hn_v2 hn_v4 hn_v5 hn_v7 hn_v8

theorem case_147_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_147_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_147 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_147 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_147_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_147
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_147
  pat_unapply h_v4 as ⟨v7, v8, x_v7, x_v8, h_v7, h_v8, hn_v7, hn_v8⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_147
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_147
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo__40strings_5freplace_5fall_5fresult.construct s e_v12 (by rw [he_v12]; exact empty_args) hinv h64 as ⟨v12, s1, hinv1, h_v12⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 h_v11 dropping h_a0 h_v1 h_v4 h_v7 he_v12 e_v12 v1 v4 v7
  pat_same v10 v12 with h_v10 h_v12 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_147
  store_step with ih.eo__24eo_5fto_5fsmt s1 v11 _ hinv1 h64 (hG.rem hrem) h_v11 as ⟨v13, s2, hinv2, h_v13⟩ growing hG carrying h_v2 h_v5 h_v8 h_v11 dropping h_v10 h_v12 hinv1 s1 v10 v12
  store_step with ih.eo__24eo_5fto_5fsmt s2 v11 _ hinv2 h64 (hG.rem hrem) h_v11 as ⟨v14, s3, hinv3, h_v14⟩ growing hG carrying h_v2 h_v5 h_v8 h_v11 h_v13 dropping hinv2 s2
  store_step with ih.eo__24eo_5fto_5fsmt s3 v8 _ hinv3 h64 (hG.rem hrem) h_v8 as ⟨v15, s4, hinv4, h_v15⟩ growing hG carrying h_v2 h_v5 h_v8 h_v11 h_v13 h_v14 dropping hinv3 s3
  store_step with ih.eo__24eo_5fto_5fsmt s4 v2 _ hinv4 h64 (hG.rem hrem) h_v2 as ⟨v16, s5, hinv5, h_v16⟩ growing hG carrying h_v5 h_v8 h_v11 h_v13 h_v14 h_v15 dropping h_v2 hinv4 s4 v2
  step as ⟨e_v17, he_v17⟩
  store_step with CtorSpec.eo__24emb_5fsm_2e_40strings_5foccur_5findex.construct s5 e_v17 (by rw [he_v17]; rfl) h_v14 h_v15 h_v16 hinv5 h64 as ⟨v17, s6, hinv6, h_v17⟩ growing hG carrying h_v5 h_v8 h_v11 h_v13 dropping h_v14 h_v15 h_v16 he_v17 hinv5 e_v17 s5 v14 v15 v16
  store_step with ih.eo__24eo_5fto_5fsmt s6 v11 _ hinv6 h64 (hG.rem hrem) h_v11 as ⟨v18, s7, hinv7, h_v18⟩ growing hG carrying h_v5 h_v8 h_v13 h_v17 dropping h_v11 hinv6 s6 v11
  step as ⟨e_v19, he_v19⟩
  store_step with CtorSpec.eo__24emb_5fsm_2estr_2elen.construct s7 e_v19 (by rw [he_v19]; rfl) h_v18 hinv7 h64 as ⟨v19, s8, hinv8, h_v19⟩ growing hG carrying h_v5 h_v8 h_v13 h_v17 dropping h_v18 he_v19 hinv7 e_v19 s7 v18
  step as ⟨e_v20, he_v20⟩
  store_step with CtorSpec.eo__24emb_5fsm_2estr_2esubstr.construct s8 e_v20 (by rw [he_v20]; rfl) h_v13 h_v17 h_v19 hinv8 h64 as ⟨v20, s9, hinv9, h_v20⟩ growing hG carrying h_v5 h_v8 dropping h_v13 h_v17 h_v19 he_v20 hinv8 e_v20 s8 v13 v17 v19
  store_step with ih.eo__24eo_5fto_5fsmt s9 v8 _ hinv9 h64 (hG.rem hrem) h_v8 as ⟨v21, s10, hinv10, h_v21⟩ growing hG carrying h_v5 h_v20 dropping h_v8 hinv9 s9 v8
  store_step with ih.eo__24eo_5fto_5fsmt s10 v5 _ hinv10 h64 (hG.rem hrem) h_v5 as ⟨v22, s11, hinv11, h_v22⟩ growing hG carrying h_v20 h_v21 dropping h_v5 hinv10 s10 v5
  step as ⟨e_v23, he_v23⟩
  store_step with CtorSpec.eo__24emb_5fsm_2estr_2ereplace_5fall.construct s11 e_v23 (by rw [he_v23]; rfl) h_v20 h_v21 h_v22 hinv11 h64 as ⟨v23, s12, hinv12, h_v23⟩ growing hG carrying dropping h_v20 h_v21 h_v22 he_v23 hinv11 e_v23 s11 v20 v21 v22
  case_done hinv12 hG with h_v23 in EoCases.__eo_to_smt.case_147 using hn_v1 hn_v2 hn_v4 hn_v5 hn_v7 hn_v8 hn_v10 hn_v11

theorem case_148_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_148_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_148 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_148 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_148_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_148
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_148
  pat_unapply h_v4 as ⟨v7, v8, x_v7, x_v8, h_v7, h_v8, hn_v7, hn_v8⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_148
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_148
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo__40strings_5freplace_5fre_5fall_5fresult.construct s e_v12 (by rw [he_v12]; exact empty_args) hinv h64 as ⟨v12, s1, hinv1, h_v12⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 h_v11 dropping h_a0 h_v1 h_v4 h_v7 he_v12 e_v12 v1 v4 v7
  pat_same v10 v12 with h_v10 h_v12 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_148
  store_step with ih.eo__24eo_5fto_5fsmt s1 v11 _ hinv1 h64 (hG.rem hrem) h_v11 as ⟨v13, s2, hinv2, h_v13⟩ growing hG carrying h_v2 h_v5 h_v8 h_v11 dropping h_v10 h_v12 hinv1 s1 v10 v12
  store_step with ih.eo__24eo_5fto_5fsmt s2 v11 _ hinv2 h64 (hG.rem hrem) h_v11 as ⟨v14, s3, hinv3, h_v14⟩ growing hG carrying h_v2 h_v5 h_v8 h_v11 h_v13 dropping hinv2 s2
  store_step with ih.eo__24eo_5fto_5fsmt s3 v8 _ hinv3 h64 (hG.rem hrem) h_v8 as ⟨v15, s4, hinv4, h_v15⟩ growing hG carrying h_v2 h_v5 h_v8 h_v11 h_v13 h_v14 dropping hinv3 s3
  store_step with ih.eo__24eo_5fto_5fsmt s4 v2 _ hinv4 h64 (hG.rem hrem) h_v2 as ⟨v16, s5, hinv5, h_v16⟩ growing hG carrying h_v5 h_v8 h_v11 h_v13 h_v14 h_v15 dropping h_v2 hinv4 s4 v2
  step as ⟨e_v17, he_v17⟩
  store_step with CtorSpec.eo__24emb_5fsm_2e_40strings_5foccur_5findex_5fre.construct s5 e_v17 (by rw [he_v17]; rfl) h_v14 h_v15 h_v16 hinv5 h64 as ⟨v17, s6, hinv6, h_v17⟩ growing hG carrying h_v5 h_v8 h_v11 h_v13 dropping h_v14 h_v15 h_v16 he_v17 hinv5 e_v17 s5 v14 v15 v16
  store_step with ih.eo__24eo_5fto_5fsmt s6 v11 _ hinv6 h64 (hG.rem hrem) h_v11 as ⟨v18, s7, hinv7, h_v18⟩ growing hG carrying h_v5 h_v8 h_v13 h_v17 dropping h_v11 hinv6 s6 v11
  step as ⟨e_v19, he_v19⟩
  store_step with CtorSpec.eo__24emb_5fsm_2estr_2elen.construct s7 e_v19 (by rw [he_v19]; rfl) h_v18 hinv7 h64 as ⟨v19, s8, hinv8, h_v19⟩ growing hG carrying h_v5 h_v8 h_v13 h_v17 dropping h_v18 he_v19 hinv7 e_v19 s7 v18
  step as ⟨e_v20, he_v20⟩
  store_step with CtorSpec.eo__24emb_5fsm_2estr_2esubstr.construct s8 e_v20 (by rw [he_v20]; rfl) h_v13 h_v17 h_v19 hinv8 h64 as ⟨v20, s9, hinv9, h_v20⟩ growing hG carrying h_v5 h_v8 dropping h_v13 h_v17 h_v19 he_v20 hinv8 e_v20 s8 v13 v17 v19
  store_step with ih.eo__24eo_5fto_5fsmt s9 v8 _ hinv9 h64 (hG.rem hrem) h_v8 as ⟨v21, s10, hinv10, h_v21⟩ growing hG carrying h_v5 h_v20 dropping h_v8 hinv9 s9 v8
  store_step with ih.eo__24eo_5fto_5fsmt s10 v5 _ hinv10 h64 (hG.rem hrem) h_v5 as ⟨v22, s11, hinv11, h_v22⟩ growing hG carrying h_v20 h_v21 dropping h_v5 hinv10 s10 v5
  step as ⟨e_v23, he_v23⟩
  store_step with CtorSpec.eo__24emb_5fsm_2estr_2ereplace_5fre_5fall.construct s11 e_v23 (by rw [he_v23]; rfl) h_v20 h_v21 h_v22 hinv11 h64 as ⟨v23, s12, hinv12, h_v23⟩ growing hG carrying dropping h_v20 h_v21 h_v22 he_v23 hinv11 e_v23 s11 v20 v21 v22
  case_done hinv12 hG with h_v23 in EoCases.__eo_to_smt.case_148 using hn_v1 hn_v2 hn_v4 hn_v5 hn_v7 hn_v8 hn_v10 hn_v11

theorem case_149_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_149_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_149 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_149 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_149_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__40witness_5fstring_5flength.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ ⟨v3, x_v3, h_v3⟩ else hinv hG in EoCases.__eo_to_smt.case_149
  obtain ⟨hn_v1, hn_v2, hn_v3⟩ := CtorSpec.eo__40witness_5fstring_5flength.fields_ne_stuck hinv h_a0
  store_step with ih.eo__24eo_5fto_5fsmt_5fnat_5fis_5fvalid s v2 _ hinv h64 hrem h_v2 as ⟨v4, s1, hinv1, h_v4⟩ growing hG carrying h_v1 h_v2 h_v3 dropping h_a0
  have h_ite_v18 := (show if_20_eo__24eo_5fto_5fsmt s1 v4 v3 v1 v2 ⦃ r s' => s'.Inv ∧ s1.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_20_eo__24eo_5fto_5fsmt
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s1
    rcases Store.boolean_value_native h_v4 with ⟨hx_5, hbv_5⟩ | ⟨hx_5, hbv_5⟩
    · ite_branch hbv_5
      store_step with ih.eo__24eo_5fto_5fsmt_5fnat_5fis_5fvalid s1 v3 _ hinv1 h64 (hG.rem hrem) h_v3 as ⟨v5, s2, hinv2, h_v5⟩ growing hG carrying h_v1 h_v2 dropping h_v3 h_v4 v3 v4
      have h_ite_v16 := (show if_19_eo__24eo_5fto_5fsmt s2 v5 v1 v2 ⦃ r s' => s'.Inv ∧ s2.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_19_eo__24eo_5fto_5fsmt
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s2
        rcases Store.boolean_value_native h_v5 with ⟨hx_6, hbv_6⟩ | ⟨hx_6, hbv_6⟩
        · ite_branch hbv_6
          step as ⟨e_v6, he_v6⟩
          simp only [eostring.EoString.from_code_points, Std.bind_ok]
          store_step with Store.raw_str_vec_spec s2 _ _ rfl hinv2 h64 as ⟨v6, s3, hinv3, h_v6⟩ growing hG carrying h_v1 h_v2 dropping h_v5 v5
          replace h_v6 := Represents.rep_of_eq h_v6 (y := SmtEval.native_string_lit "@x") (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v6]; decide)
          store_step with ih.eo__24eo_5fto_5fsmt_5ftype s3 v1 _ hinv3 h64 (hG.rem hrem) h_v1 as ⟨v7, s4, hinv4, h_v7⟩ growing hG carrying h_v1 h_v2 h_v6 dropping he_v6 e_v6
          step as ⟨e_v8, he_v8⟩
          try simp only [eostring.EoString.from_code_points, Std.bind_ok]
          store_step with Store.raw_str_vec_spec s4 _ _ rfl hinv4 h64 as ⟨v8, s5, hinv5, h_v8⟩ growing hG carrying h_v1 h_v2 h_v6 h_v7 dropping hinv4 s4
          replace h_v8 := Represents.rep_of_eq h_v8 (y := SmtEval.native_string_lit "@x") (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v8]; decide)
          store_step with ih.eo__24eo_5fto_5fsmt_5ftype s5 v1 _ hinv5 h64 (hG.rem hrem) h_v1 as ⟨v9, s6, hinv6, h_v9⟩ growing hG carrying h_v2 h_v6 h_v7 h_v8 dropping h_v1 he_v8 hinv5 e_v8 s5 v1
          step as ⟨e_v10, he_v10⟩
          store_step with CtorSpec.eo__24emb_5fsm_2eVar.construct s6 e_v10 (by rw [he_v10]; rfl) h_v8 h_v9 hinv6 h64 as ⟨v10, s7, hinv7, h_v10⟩ growing hG carrying h_v2 h_v6 h_v7 dropping h_v8 h_v9 he_v10 hinv6 e_v10 s6 v8 v9
          step as ⟨e_v11, he_v11⟩
          store_step with CtorSpec.eo__24emb_5fsm_2estr_2elen.construct s7 e_v11 (by rw [he_v11]; rfl) h_v10 hinv7 h64 as ⟨v11, s8, hinv8, h_v11⟩ growing hG carrying h_v2 h_v6 h_v7 dropping h_v10 he_v11 hinv7 e_v11 s7 v10
          store_step with ih.eo__24eo_5fto_5fsmt s8 v2 _ hinv8 h64 (hG.rem hrem) h_v2 as ⟨v12, s9, hinv9, h_v12⟩ growing hG carrying h_v6 h_v7 h_v11 dropping h_v2 hinv8 s8 v2
          step as ⟨e_v13, he_v13⟩
          store_step with CtorSpec.eo__24emb_5fsm_2e_3d.construct s9 e_v13 (by rw [he_v13]; rfl) h_v11 h_v12 hinv9 h64 as ⟨v13, s10, hinv10, h_v13⟩ growing hG carrying h_v6 h_v7 dropping h_v11 h_v12 he_v13 hinv9 e_v13 s9 v11 v12
          step as ⟨e_v14, he_v14⟩
          store_step with CtorSpec.eo__24emb_5fsm_2echoice.construct s10 e_v14 (by rw [he_v14]; rfl) h_v6 h_v7 h_v13 hinv10 h64 as ⟨v14, s11, hinv11, h_v14⟩ growing hG carrying dropping h_v13 h_v6 h_v7 he_v14 hinv10 e_v14 s10 v13 v6 v7
          ite_done hinv11 hG with (native_ite_true_rep _ hx_6 h_v14)
        · ite_branch hbv_6
          step as ⟨e_v15, he_v15⟩
          store_step with CtorSpec.eo__24emb_5fsm_2eNone.construct s2 e_v15 (by rw [he_v15]; exact empty_args) hinv2 h64 as ⟨v15, s3, hinv3, h_v15⟩ growing hG carrying dropping h_v1 h_v2 h_v5 he_v15 e_v15 v1 v2 v5
          ite_done hinv3 hG with (native_ite_false_rep _ hx_6 h_v15))
      store_step with h_ite_v16 as ⟨v16, s3, hinv3, h_v16⟩ growing hG carrying dropping h_ite_v16 h_v1 h_v2 h_v5 v1 v2 v5
      ite_done hinv3 hG with (native_ite_true_rep _ hx_5 h_v16)
    · ite_branch hbv_5
      step as ⟨e_v17, he_v17⟩
      store_step with CtorSpec.eo__24emb_5fsm_2eNone.construct s1 e_v17 (by rw [he_v17]; exact empty_args) hinv1 h64 as ⟨v17, s2, hinv2, h_v17⟩ growing hG carrying dropping h_v1 h_v2 h_v3 h_v4 he_v17 hinv1 e_v17 s1 v1 v2 v3 v4
      ite_done hinv2 hG with (native_ite_false_rep _ hx_5 h_v17))
  store_step with h_ite_v18 as ⟨v18, s2, hinv2, h_v18⟩ growing hG carrying dropping h_ite_v18 h_v1 h_v2 h_v3 h_v4 hinv1 s1 v1 v2 v3 v4
  case_done hinv2 hG with h_v18 in EoCases.__eo_to_smt.case_149 using hn_v1 hn_v2 hn_v3

theorem case_150_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_150_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_150 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_150 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_150_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_150
  pat_destruct CtorSpec.eo_is.destruct h_v1 as ⟨v4, x_v4, h_v4⟩ else hinv hG in EoCases.__eo_to_smt.case_150
  obtain hn_v4 := CtorSpec.eo_is.fields_ne_stuck hinv h_v1
  store_step with ih.eo__24eo_5fto_5fsmt s v4 _ hinv h64 hrem h_v4 as ⟨v5, s1, hinv1, h_v5⟩ growing hG carrying h_v2 dropping h_a0 h_v1 h_v4 v1 v4
  store_step with ih.eo__24eo_5fto_5fsmt_5ftester s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v6, s2, hinv2, h_v6⟩ growing hG carrying h_v2 dropping h_v5 hinv1 s1 v5
  store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v7, s3, hinv3, h_v7⟩ growing hG carrying h_v6 dropping h_v2 hinv2 s2 v2
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eApply.construct s3 e_v8 (by rw [he_v8]; rfl) h_v6 h_v7 hinv3 h64 as ⟨v8, s4, hinv4, h_v8⟩ growing hG carrying dropping h_v6 h_v7 he_v8 hinv3 e_v8 s3 v6 v7
  case_done hinv4 hG with h_v8 in EoCases.__eo_to_smt.case_150 using hn_v1 hn_v2 hn_v4

theorem case_151_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_151_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_151 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_151 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_151_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_151
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_151
  pat_destruct CtorSpec.eo_update.destruct h_v4 as ⟨v7, x_v7, h_v7⟩ else hinv hG in EoCases.__eo_to_smt.case_151
  obtain hn_v7 := CtorSpec.eo_update.fields_ne_stuck hinv h_v4
  store_step with ih.eo__24eo_5fto_5fsmt s v7 _ hinv h64 hrem h_v7 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_v2 h_v5 dropping h_a0 h_v1 h_v4 h_v7 v1 v4 v7
  store_step with ih.eo__24eo_5fto_5fsmt s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v9, s2, hinv2, h_v9⟩ growing hG carrying h_v2 h_v8 dropping h_v5 hinv1 s1 v5
  store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v10, s3, hinv3, h_v10⟩ growing hG carrying h_v8 h_v9 dropping h_v2 hinv2 s2 v2
  store_step with ih.eo__24eo_5fto_5fsmt_5fupdater s3 v8 v9 v10 _ _ _ hinv3 h64 (hG.rem hrem) h_v8 h_v9 h_v10 as ⟨v11, s4, hinv4, h_v11⟩ growing hG carrying dropping h_v10 h_v8 h_v9 hinv3 s3 v10 v8 v9
  case_done hinv4 hG with h_v11 in EoCases.__eo_to_smt.case_151 using hn_v1 hn_v2 hn_v4 hn_v5 hn_v7

theorem case_152_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_152_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_152 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_152 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_152_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_tuple_2eunit.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 dropping he_v0 e_v0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_152
  step as ⟨e_v1, he_v1⟩
  simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.raw_str_vec_spec s1 _ _ rfl hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying dropping h_a0 h_v0 hinv1 s1 v0
  replace h_v1 := Represents.rep_of_eq h_v1 (y := SmtEval.native_string_lit "@Tuple") (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v1]; decide)
  step as ⟨e_v2, he_v2⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.raw_str_vec_spec s2 _ _ rfl hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_v1 dropping he_v1 hinv2 e_v1 s2
  replace h_v2 := Represents.rep_of_eq h_v2 (y := SmtEval.native_string_lit "@Tuple") (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v2]; decide)
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__24emb_5fdtc_2eunit.construct s3 e_v3 (by rw [he_v3]; exact empty_args) hinv3 h64 as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_v1 h_v2 dropping he_v2 he_v3 hinv3 e_v2 e_v3 s3
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo__24emb_5fdt_2enull.construct s4 e_v4 (by rw [he_v4]; exact empty_args) hinv4 h64 as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_v1 h_v2 h_v3 dropping he_v4 hinv4 e_v4 s4
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5fdt_2esum.construct s5 e_v5 (by rw [he_v5]; rfl) h_v3 h_v4 hinv5 h64 as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_v1 h_v2 dropping h_v3 h_v4 he_v5 hinv5 e_v5 s5 v3 v4
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__24emb_5fdd_2enil.construct s6 e_v6 (by rw [he_v6]; exact empty_args) hinv6 h64 as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_v1 h_v2 h_v5 dropping he_v6 hinv6 e_v6 s6
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo__24emb_5fdd_2econs.construct s7 e_v7 (by rw [he_v7]; rfl) h_v2 h_v5 h_v6 hinv7 h64 as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_v1 dropping h_v2 h_v5 h_v6 he_v7 hinv7 e_v7 s7 v2 v5 v6
  store_step with Store.native_nat_zero_spec s8 hinv8 h64 as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_v1 h_v7 dropping hinv8 s8
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eDtCons.construct s9 e_v9 (by rw [he_v9]; rfl) h_v1 h_v7 h_v8 hinv9 h64 as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying dropping h_v1 h_v7 h_v8 he_v9 hinv9 e_v9 s9 v1 v7 v8
  case_done hinv10 hG with h_v9 in EoCases.__eo_to_smt.case_152 using

theorem case_153_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_153_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_153 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_153 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_153_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_153
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_153
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_tuple.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_153
  store_step with ih.eo__24eo_5fto_5fsmt s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 h_v5 dropping h_v4 h_v6 hinv1 s1 v4 v6
  store_step with ih.eo__24eo_5fto_5fsmt s2 v5 _ hinv2 h64 (hG.rem hrem) h_v5 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v2 h_v7 dropping h_v5 hinv2 s2 v5
  store_step with ih.eo__24smtx_5ftypeof s3 v8 _ hinv3 h64 (hG.rem hrem) h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_v2 h_v7 dropping h_v8 hinv3 s3 v8
  store_step with ih.eo__24eo_5fto_5fsmt s4 v2 _ hinv4 h64 (hG.rem hrem) h_v2 as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_v7 h_v9 dropping h_v2 hinv4 s4 v2
  store_step with ih.eo__24eo_5fto_5fsmt_5ftuple_5fprepend s5 v7 v9 v10 _ _ _ hinv5 h64 (hG.rem hrem) h_v7 h_v9 h_v10 as ⟨v11, s6, hinv6, h_v11⟩ growing hG carrying dropping h_v10 h_v7 h_v9 hinv5 s5 v10 v7 v9
  case_done hinv6 hG with h_v11 in EoCases.__eo_to_smt.case_153 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_154_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_154_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_154 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_154 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_154_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_154
  pat_destruct CtorSpec.eo_tuple_2eselect.destruct h_v1 as ⟨v4, x_v4, h_v4⟩ else hinv hG in EoCases.__eo_to_smt.case_154
  obtain hn_v4 := CtorSpec.eo_tuple_2eselect.fields_ne_stuck hinv h_v1
  store_step with ih.eo__24eo_5fto_5fsmt s v2 _ hinv h64 hrem h_v2 as ⟨v5, s1, hinv1, h_v5⟩ growing hG carrying h_v2 h_v4 dropping h_a0 h_v1 v1
  store_step with ih.eo__24smtx_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v6, s2, hinv2, h_v6⟩ growing hG carrying h_v2 h_v4 dropping h_v5 hinv1 s1 v5
  store_step with ih.eo__24eo_5fto_5fsmt s2 v4 _ hinv2 h64 (hG.rem hrem) h_v4 as ⟨v7, s3, hinv3, h_v7⟩ growing hG carrying h_v2 h_v6 dropping h_v4 hinv2 s2 v4
  store_step with ih.eo__24eo_5fto_5fsmt s3 v2 _ hinv3 h64 (hG.rem hrem) h_v2 as ⟨v8, s4, hinv4, h_v8⟩ growing hG carrying h_v6 h_v7 dropping h_v2 hinv3 s3 v2
  store_step with ih.eo__24eo_5fto_5fsmt_5ftuple_5fselect s4 v6 v7 v8 _ _ _ hinv4 h64 (hG.rem hrem) h_v6 h_v7 h_v8 as ⟨v9, s5, hinv5, h_v9⟩ growing hG carrying dropping h_v6 h_v7 h_v8 hinv4 s4 v6 v7 v8
  case_done hinv5 hG with h_v9 in EoCases.__eo_to_smt.case_154 using hn_v1 hn_v2 hn_v4

theorem case_155_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_155_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_155 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_155 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_155_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_155
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_155
  pat_destruct CtorSpec.eo_tuple_2eupdate.destruct h_v4 as ⟨v7, x_v7, h_v7⟩ else hinv hG in EoCases.__eo_to_smt.case_155
  obtain hn_v7 := CtorSpec.eo_tuple_2eupdate.fields_ne_stuck hinv h_v4
  store_step with ih.eo__24eo_5fto_5fsmt s v5 _ hinv h64 hrem h_v5 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_v2 h_v5 h_v7 dropping h_a0 h_v1 h_v4 v1 v4
  store_step with ih.eo__24smtx_5ftypeof s1 v8 _ hinv1 h64 (hG.rem hrem) h_v8 as ⟨v9, s2, hinv2, h_v9⟩ growing hG carrying h_v2 h_v5 h_v7 dropping h_v8 hinv1 s1 v8
  store_step with ih.eo__24eo_5fto_5fsmt s2 v7 _ hinv2 h64 (hG.rem hrem) h_v7 as ⟨v10, s3, hinv3, h_v10⟩ growing hG carrying h_v2 h_v5 h_v9 dropping h_v7 hinv2 s2 v7
  store_step with ih.eo__24eo_5fto_5fsmt s3 v5 _ hinv3 h64 (hG.rem hrem) h_v5 as ⟨v11, s4, hinv4, h_v11⟩ growing hG carrying h_v2 h_v9 h_v10 dropping h_v5 hinv3 s3 v5
  store_step with ih.eo__24eo_5fto_5fsmt s4 v2 _ hinv4 h64 (hG.rem hrem) h_v2 as ⟨v12, s5, hinv5, h_v12⟩ growing hG carrying h_v9 h_v10 h_v11 dropping h_v2 hinv4 s4 v2
  store_step with ih.eo__24eo_5fto_5fsmt_5ftuple_5fupdate s5 v9 v10 v11 v12 _ _ _ _ hinv5 h64 (hG.rem hrem) h_v9 h_v10 h_v11 h_v12 as ⟨v13, s6, hinv6, h_v13⟩ growing hG carrying dropping h_v10 h_v11 h_v12 h_v9 hinv5 s5 v10 v11 v12 v9
  case_done hinv6 hG with h_v13 in EoCases.__eo_to_smt.case_155 using hn_v1 hn_v2 hn_v4 hn_v5 hn_v7

theorem case_156_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_156_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_156 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_156 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_156_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo_set_2eempty.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_to_smt.case_156
  obtain hn_v1 := CtorSpec.eo_set_2eempty.fields_ne_stuck hinv h_a0
  store_step with ih.eo__24eo_5fto_5fsmt_5ftype s v1 _ hinv h64 hrem h_v1 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying dropping h_a0 h_v1 v1
  store_step with ih.eo__24eo_5fto_5fsmt_5fset_2eempty s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying dropping h_v2 hinv1 s1 v2
  case_done hinv2 hG with h_v3 in EoCases.__eo_to_smt.case_156 using hn_v1

theorem case_157_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_157_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_157 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_157 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_157_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_157
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_set_2esingleton.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v1 h_v2 dropping h_a0 he_v3 e_v3
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_157
  store_step with ih.eo__24eo_5fto_5fsmt s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying dropping h_v1 h_v2 h_v3 hinv1 s1 v1 v2 v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eset_2esingleton.construct s2 e_v5 (by rw [he_v5]; rfl) h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying dropping h_v4 he_v5 hinv2 e_v5 s2 v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_to_smt.case_157 using hn_v1 hn_v2

theorem case_158_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_158_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_158 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_158 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_158_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_158
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_158
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_set_2eunion.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_158
  store_step with ih.eo__24eo_5fto_5fsmt s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 dropping h_v4 h_v5 h_v6 hinv1 s1 v4 v5 v6
  store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v7 dropping h_v2 hinv2 s2 v2
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eset_2eunion.construct s3 e_v9 (by rw [he_v9]; rfl) h_v7 h_v8 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying dropping h_v7 h_v8 he_v9 hinv3 e_v9 s3 v7 v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_to_smt.case_158 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_159_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_159_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_159 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_159 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_159_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_159
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_159
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_set_2einter.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_159
  store_step with ih.eo__24eo_5fto_5fsmt s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 dropping h_v4 h_v5 h_v6 hinv1 s1 v4 v5 v6
  store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v7 dropping h_v2 hinv2 s2 v2
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eset_2einter.construct s3 e_v9 (by rw [he_v9]; rfl) h_v7 h_v8 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying dropping h_v7 h_v8 he_v9 hinv3 e_v9 s3 v7 v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_to_smt.case_159 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_160_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_160_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_160 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_160 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_160_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_160
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_160
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_set_2eminus.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_160
  store_step with ih.eo__24eo_5fto_5fsmt s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 dropping h_v4 h_v5 h_v6 hinv1 s1 v4 v5 v6
  store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v7 dropping h_v2 hinv2 s2 v2
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eset_2eminus.construct s3 e_v9 (by rw [he_v9]; rfl) h_v7 h_v8 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying dropping h_v7 h_v8 he_v9 hinv3 e_v9 s3 v7 v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_to_smt.case_160 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_161_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_161_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_161 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_161 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_161_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_161
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_161
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_set_2emember.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_161
  store_step with ih.eo__24eo_5fto_5fsmt s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 dropping h_v4 h_v5 h_v6 hinv1 s1 v4 v5 v6
  store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v7 dropping h_v2 hinv2 s2 v2
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eset_2emember.construct s3 e_v9 (by rw [he_v9]; rfl) h_v7 h_v8 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying dropping h_v7 h_v8 he_v9 hinv3 e_v9 s3 v7 v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_to_smt.case_161 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_162_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_162_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_162 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_162 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_162_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_162
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_162
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_set_2esubset.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_162
  store_step with ih.eo__24eo_5fto_5fsmt s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 dropping h_v4 h_v5 h_v6 hinv1 s1 v4 v5 v6
  store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v7 dropping h_v2 hinv2 s2 v2
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eset_2esubset.construct s3 e_v9 (by rw [he_v9]; rfl) h_v7 h_v8 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying dropping h_v7 h_v8 he_v9 hinv3 e_v9 s3 v7 v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_to_smt.case_162 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_163_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_163_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_163 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_163 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_163_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_163
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_set_2echoose.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v1 h_v2 dropping h_a0 he_v3 e_v3
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_163
  store_step with ih.eo__24eo_5fto_5fsmt s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v2 dropping h_v1 h_v3 hinv1 s1 v1 v3
  store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_v4 dropping h_v2 hinv2 s2 v2
  store_step with ih.eo__24smtx_5ftypeof s3 v5 _ hinv3 h64 (hG.rem hrem) h_v5 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_v4 dropping h_v5 hinv3 s3 v5
  store_step with ih.eo__24eo_5fto_5fsmt_5fset_5felem_5ftype s4 v6 _ hinv4 h64 (hG.rem hrem) h_v6 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_v4 dropping h_v6 hinv4 s4 v6
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eset_2eempty.construct s5 e_v8 (by rw [he_v8]; rfl) h_v7 hinv5 h64 as ⟨v8, s6, hinv6, h_v8⟩ growing hG carrying h_v4 dropping h_v7 he_v8 hinv5 e_v8 s5 v7
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fsm_2emap_5fdiff.construct s6 e_v9 (by rw [he_v9]; rfl) h_v4 h_v8 hinv6 h64 as ⟨v9, s7, hinv7, h_v9⟩ growing hG carrying dropping h_v4 h_v8 he_v9 hinv6 e_v9 s6 v4 v8
  case_done hinv7 hG with h_v9 in EoCases.__eo_to_smt.case_163 using hn_v1 hn_v2

theorem case_164_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_164_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_164 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_164 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_164_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_164
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_set_2eis_5fempty.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v1 h_v2 dropping h_a0 he_v3 e_v3
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_164
  store_step with ih.eo__24eo_5fto_5fsmt s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v2 dropping h_v1 h_v3 hinv1 s1 v1 v3
  store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_v4 dropping h_v2 hinv2 s2 v2
  store_step with ih.eo__24smtx_5ftypeof s3 v5 _ hinv3 h64 (hG.rem hrem) h_v5 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_v4 dropping h_v5 hinv3 s3 v5
  store_step with ih.eo__24eo_5fto_5fsmt_5fset_5felem_5ftype s4 v6 _ hinv4 h64 (hG.rem hrem) h_v6 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_v4 dropping h_v6 hinv4 s4 v6
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eset_2eempty.construct s5 e_v8 (by rw [he_v8]; rfl) h_v7 hinv5 h64 as ⟨v8, s6, hinv6, h_v8⟩ growing hG carrying h_v4 dropping h_v7 he_v8 hinv5 e_v8 s5 v7
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fsm_2e_3d.construct s6 e_v9 (by rw [he_v9]; rfl) h_v4 h_v8 hinv6 h64 as ⟨v9, s7, hinv7, h_v9⟩ growing hG carrying dropping h_v4 h_v8 he_v9 hinv6 e_v9 s6 v4 v8
  case_done hinv7 hG with h_v9 in EoCases.__eo_to_smt.case_164 using hn_v1 hn_v2

theorem case_165_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_165_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_165 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_165 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_165_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_165
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_set_2eis_5fsingleton.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v1 h_v2 dropping h_a0 he_v3 e_v3
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_165
  store_step with ih.eo__24eo_5fto_5fsmt s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v2 dropping h_v1 h_v3 hinv1 s1 v1 v3
  store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_v2 h_v4 dropping hinv2 s2
  store_step with ih.eo__24eo_5fto_5fsmt s3 v2 _ hinv3 h64 (hG.rem hrem) h_v2 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_v4 h_v5 dropping h_v2 hinv3 s3 v2
  store_step with ih.eo__24smtx_5ftypeof s4 v6 _ hinv4 h64 (hG.rem hrem) h_v6 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_v4 h_v5 dropping h_v6 hinv4 s4 v6
  store_step with ih.eo__24eo_5fto_5fsmt_5fset_5felem_5ftype s5 v7 _ hinv5 h64 (hG.rem hrem) h_v7 as ⟨v8, s6, hinv6, h_v8⟩ growing hG carrying h_v4 h_v5 dropping h_v7 hinv5 s5 v7
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eset_2eempty.construct s6 e_v9 (by rw [he_v9]; rfl) h_v8 hinv6 h64 as ⟨v9, s7, hinv7, h_v9⟩ growing hG carrying h_v4 h_v5 dropping h_v8 he_v9 hinv6 e_v9 s6 v8
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo__24emb_5fsm_2emap_5fdiff.construct s7 e_v10 (by rw [he_v10]; rfl) h_v5 h_v9 hinv7 h64 as ⟨v10, s8, hinv8, h_v10⟩ growing hG carrying h_v4 dropping h_v5 h_v9 he_v10 hinv7 e_v10 s7 v5 v9
  step as ⟨e_v11, he_v11⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eset_2esingleton.construct s8 e_v11 (by rw [he_v11]; rfl) h_v10 hinv8 h64 as ⟨v11, s9, hinv9, h_v11⟩ growing hG carrying h_v4 dropping h_v10 he_v11 hinv8 e_v11 s8 v10
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo__24emb_5fsm_2e_3d.construct s9 e_v12 (by rw [he_v12]; rfl) h_v4 h_v11 hinv9 h64 as ⟨v12, s10, hinv10, h_v12⟩ growing hG carrying dropping h_v11 h_v4 he_v12 hinv9 e_v12 s9 v11 v4
  case_done hinv10 hG with h_v12 in EoCases.__eo_to_smt.case_165 using hn_v1 hn_v2

theorem case_166_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_166_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_166 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_166 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_166_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_166
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_166
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_set_2einsert.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_166
  store_step with ih.eo__24eo_5fto_5fsmt s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 dropping h_v4 h_v5 h_v6 hinv1 s1 v4 v5 v6
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eset_2esingleton.construct s2 e_v8 (by rw [he_v8]; rfl) h_v7 hinv2 h64 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v2 dropping h_v7 he_v8 hinv2 e_v8 s2 v7
  store_step with ih.eo__24eo_5fto_5fsmt s3 v2 _ hinv3 h64 (hG.rem hrem) h_v2 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_v8 dropping h_v2 hinv3 s3 v2
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eset_2eunion.construct s4 e_v10 (by rw [he_v10]; rfl) h_v8 h_v9 hinv4 h64 as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying dropping h_v8 h_v9 he_v10 hinv4 e_v10 s4 v8 v9
  case_done hinv5 hG with h_v10 in EoCases.__eo_to_smt.case_166 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_167_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_167_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_167 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_167 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_167_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_167
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_167
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__40sets_5fdeq_5fdiff.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_167
  store_step with ih.eo__24eo_5fto_5fsmt s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 h_v5 dropping h_v4 h_v6 hinv1 s1 v4 v6
  store_step with ih.eo__24eo_5fto_5fsmt s2 v5 _ hinv2 h64 (hG.rem hrem) h_v5 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v2 h_v7 dropping h_v5 hinv2 s2 v5
  store_step with ih.eo__24smtx_5ftypeof s3 v8 _ hinv3 h64 (hG.rem hrem) h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_v2 h_v7 dropping h_v8 hinv3 s3 v8
  store_step with ih.eo__24eo_5fto_5fsmt s4 v2 _ hinv4 h64 (hG.rem hrem) h_v2 as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_v2 h_v7 h_v9 dropping hinv4 s4
  store_step with ih.eo__24eo_5fto_5fsmt s5 v2 _ hinv5 h64 (hG.rem hrem) h_v2 as ⟨v11, s6, hinv6, h_v11⟩ growing hG carrying h_v7 h_v9 h_v10 dropping h_v2 hinv5 s5 v2
  store_step with ih.eo__24smtx_5ftypeof s6 v11 _ hinv6 h64 (hG.rem hrem) h_v11 as ⟨v12, s7, hinv7, h_v12⟩ growing hG carrying h_v7 h_v9 h_v10 dropping h_v11 hinv6 s6 v11
  store_step with ih.eo__24eo_5fto_5fsmt_5fsets_5fdeq_5fdiff s7 v7 v9 v10 v12 _ _ _ _ hinv7 h64 (hG.rem hrem) h_v7 h_v9 h_v10 h_v12 as ⟨v13, s8, hinv8, h_v13⟩ growing hG carrying dropping h_v10 h_v12 h_v7 h_v9 hinv7 s7 v10 v12 v7 v9
  case_done hinv8 hG with h_v13 in EoCases.__eo_to_smt.case_167 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_168_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_168_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_168 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_168 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_168_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_168
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_168
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__2f.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_168
  store_step with ih.eo__24eo_5fto_5fsmt s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 dropping h_v4 h_v5 h_v6 hinv1 s1 v4 v5 v6
  store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v7 dropping h_v2 hinv2 s2 v2
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fsm_2e_2f.construct s3 e_v9 (by rw [he_v9]; rfl) h_v7 h_v8 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying dropping h_v7 h_v8 he_v9 hinv3 e_v9 s3 v7 v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_to_smt.case_168 using hn_v1 hn_v2 hn_v4 hn_v5

end pathos_compiled_checker
