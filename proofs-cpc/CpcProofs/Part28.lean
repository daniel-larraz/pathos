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

theorem case_0_eo__24smtx_5ftype_5fwf_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24smtx_5ftype_5fwf_5frec s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_type_wf_rec.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_type_wf_rec.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24smtx_5ftype_5fwf_5frec
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__smtx_type_wf_rec.case_0
  store_step with Store.native_bool_spec s1 false hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__smtx_type_wf_rec.case_0 using

theorem case_1_eo__24smtx_5ftype_5fwf_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_1_eo__24smtx_5ftype_5fwf_5frec s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_type_wf_rec.case_1 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_type_wf_rec.case_1 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24smtx_5ftype_5fwf_5frec
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eRegLan.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__smtx_type_wf_rec.case_1
  store_step with Store.native_bool_spec s1 false hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__smtx_type_wf_rec.case_1 using

theorem case_2_eo__24smtx_5ftype_5fwf_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_2_eo__24smtx_5ftype_5fwf_5frec s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_type_wf_rec.case_2 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_type_wf_rec.case_2 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24smtx_5ftype_5fwf_5frec
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5ftsm_2eMap.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_type_wf_rec.case_2
  store_step with ih.eo__24smtx_5finhabited_5ftype s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24smtx_5ftype_5fwf_5frec s1 v1 _ hinv1 h64 (hG.rem hrem) h_v1 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with Store.native_spec_and s2 e_v5 (by rw [he_v5]; rfl) h_v3 h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  rw [← Bridge.native_and] at h_v5
  store_step with ih.eo__24smtx_5finhabited_5ftype s3 v2 _ hinv3 h64 (hG.rem hrem) h_v2 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with ih.eo__24smtx_5ftype_5fwf_5frec s4 v2 _ hinv4 h64 (hG.rem hrem) h_v2 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  step as ⟨e_v8, he_v8⟩
  store_step with Store.native_spec_and s5 e_v8 (by rw [he_v8]; rfl) h_v6 h_v7 hinv5 h64 as ⟨v8, s6, hinv6, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  rw [← Bridge.native_and] at h_v8
  step as ⟨e_v9, he_v9⟩
  store_step with Store.native_spec_and s6 e_v9 (by rw [he_v9]; rfl) h_v5 h_v8 hinv6 h64 as ⟨v9, s7, hinv7, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
  rw [← Bridge.native_and] at h_v9
  case_done hinv7 hG with h_v9 in EoCases.__smtx_type_wf_rec.case_2 using

theorem case_3_eo__24smtx_5ftype_5fwf_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_3_eo__24smtx_5ftype_5fwf_5frec s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_type_wf_rec.case_3 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_type_wf_rec.case_3 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_3_eo__24smtx_5ftype_5fwf_5frec
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5ftsm_2eSet.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__smtx_type_wf_rec.case_3
  store_step with ih.eo__24smtx_5finhabited_5ftype s v1 _ hinv h64 hrem h_v1 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying h_a0 h_v1
  store_step with ih.eo__24smtx_5ftype_5fwf_5frec s1 v1 _ hinv1 h64 (hG.rem hrem) h_v1 as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  step as ⟨e_v4, he_v4⟩
  store_step with Store.native_spec_and s2 e_v4 (by rw [he_v4]; rfl) h_v2 h_v3 hinv2 h64 as ⟨v4, s3, hinv3, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  rw [← Bridge.native_and] at h_v4
  case_done hinv3 hG with h_v4 in EoCases.__smtx_type_wf_rec.case_3 using

theorem case_4_eo__24smtx_5ftype_5fwf_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_4_eo__24smtx_5ftype_5fwf_5frec s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_type_wf_rec.case_4 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_type_wf_rec.case_4 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_4_eo__24smtx_5ftype_5fwf_5frec
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5ftsm_2eSeq.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__smtx_type_wf_rec.case_4
  store_step with ih.eo__24smtx_5finhabited_5ftype s v1 _ hinv h64 hrem h_v1 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying h_a0 h_v1
  store_step with ih.eo__24smtx_5ftype_5fwf_5frec s1 v1 _ hinv1 h64 (hG.rem hrem) h_v1 as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  step as ⟨e_v4, he_v4⟩
  store_step with Store.native_spec_and s2 e_v4 (by rw [he_v4]; rfl) h_v2 h_v3 hinv2 h64 as ⟨v4, s3, hinv3, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  rw [← Bridge.native_and] at h_v4
  case_done hinv3 hG with h_v4 in EoCases.__smtx_type_wf_rec.case_4 using

theorem case_5_eo__24smtx_5ftype_5fwf_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_5_eo__24smtx_5ftype_5fwf_5frec s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_type_wf_rec.case_5 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_type_wf_rec.case_5 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_5_eo__24smtx_5ftype_5fwf_5frec
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5ftsm_2eDatatype.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_type_wf_rec.case_5
  store_step with ih.eo__24smtx_5fdd_5fhas_5fdt s v1 v2 _ _ hinv h64 hrem h_v1 h_v2 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24smtx_5fdecl_5fwf_5frec s1 v2 v2 _ _ hinv1 h64 (hG.rem hrem) h_v2 h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with Store.native_spec_and s2 e_v5 (by rw [he_v5]; rfl) h_v3 h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  rw [← Bridge.native_and] at h_v5
  case_done hinv3 hG with h_v5 in EoCases.__smtx_type_wf_rec.case_5 using

theorem case_6_eo__24smtx_5ftype_5fwf_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_6_eo__24smtx_5ftype_5fwf_5frec s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_type_wf_rec.case_6 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_type_wf_rec.case_6 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_6_eo__24smtx_5ftype_5fwf_5frec
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5ftsm_2eTypeRef.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__smtx_type_wf_rec.case_6
  store_step with Store.native_bool_spec s false hinv h64 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying h_a0 h_v1
  case_done hinv1 hG with h_v2 in EoCases.__smtx_type_wf_rec.case_6 using

theorem case_7_eo__24smtx_5ftype_5fwf_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_7_eo__24smtx_5ftype_5fwf_5frec s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_type_wf_rec.case_7 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_type_wf_rec.case_7 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_7_eo__24smtx_5ftype_5fwf_5frec
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5ftsm_2eFunType.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_type_wf_rec.case_7
  store_step with Store.native_bool_spec s false hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  case_done hinv1 hG with h_v3 in EoCases.__smtx_type_wf_rec.case_7 using

theorem case_8_eo__24smtx_5ftype_5fwf_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_8_eo__24smtx_5ftype_5fwf_5frec s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_type_wf_rec.case_8 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_type_wf_rec.case_8 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_8_eo__24smtx_5ftype_5fwf_5frec
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5ftsm_2eDtcAppType.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_type_wf_rec.case_8
  store_step with Store.native_bool_spec s false hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  case_done hinv1 hG with h_v3 in EoCases.__smtx_type_wf_rec.case_8 using

theorem case_9_eo__24smtx_5ftype_5fwf_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_9_eo__24smtx_5ftype_5fwf_5frec s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_type_wf_rec.case_9 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_type_wf_rec.case_9 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_9_eo__24smtx_5ftype_5fwf_5frec
  have hG := Store.Grows.refl s
  store_step with Store.native_bool_spec s true hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  case_done hinv1 hG with h_v0 in EoCases.__smtx_type_wf_rec.case_9 using

theorem cases_0_0_eo__24smtx_5ftype_5fwf_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_0_eo__24smtx_5ftype_5fwf_5frec s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__smtx_type_wf_rec.case_0 x_a0, EoCases.__smtx_type_wf_rec.case_1 x_a0, EoCases.__smtx_type_wf_rec.case_2 x_a0, EoCases.__smtx_type_wf_rec.case_3 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_type_wf_rec.case_0 x_a0 = none ∧ EoCases.__smtx_type_wf_rec.case_1 x_a0 = none ∧ EoCases.__smtx_type_wf_rec.case_2 x_a0 = none ∧ EoCases.__smtx_type_wf_rec.case_3 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_0_eo__24smtx_5ftype_5fwf_5frec
  have hG := Store.Grows.refl s
  group_step with case_0_eo__24smtx_5ftype_5fwf_5frec_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_type_wf_rec.case_0 x_a0, EoCases.__smtx_type_wf_rec.case_1 x_a0, EoCases.__smtx_type_wf_rec.case_2 x_a0, EoCases.__smtx_type_wf_rec.case_3 x_a0] = [] ++ [EoCases.__smtx_type_wf_rec.case_0 x_a0] ++ [EoCases.__smtx_type_wf_rec.case_1 x_a0, EoCases.__smtx_type_wf_rec.case_2 x_a0, EoCases.__smtx_type_wf_rec.case_3 x_a0] from rfl)
    otherwise ⟨hl_0⟩ using
  group_step with case_1_eo__24smtx_5ftype_5fwf_5frec_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_type_wf_rec.case_0 x_a0, EoCases.__smtx_type_wf_rec.case_1 x_a0, EoCases.__smtx_type_wf_rec.case_2 x_a0, EoCases.__smtx_type_wf_rec.case_3 x_a0] = [EoCases.__smtx_type_wf_rec.case_0 x_a0] ++ [EoCases.__smtx_type_wf_rec.case_1 x_a0] ++ [EoCases.__smtx_type_wf_rec.case_2 x_a0, EoCases.__smtx_type_wf_rec.case_3 x_a0] from rfl)
    otherwise ⟨hl_1⟩ using hl_0
  group_step with case_2_eo__24smtx_5ftype_5fwf_5frec_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_type_wf_rec.case_0 x_a0, EoCases.__smtx_type_wf_rec.case_1 x_a0, EoCases.__smtx_type_wf_rec.case_2 x_a0, EoCases.__smtx_type_wf_rec.case_3 x_a0] = [EoCases.__smtx_type_wf_rec.case_0 x_a0, EoCases.__smtx_type_wf_rec.case_1 x_a0] ++ [EoCases.__smtx_type_wf_rec.case_2 x_a0] ++ [EoCases.__smtx_type_wf_rec.case_3 x_a0] from rfl)
    otherwise ⟨hl_2⟩ using hl_0 hl_1
  group_step with case_3_eo__24smtx_5ftype_5fwf_5frec_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_type_wf_rec.case_0 x_a0, EoCases.__smtx_type_wf_rec.case_1 x_a0, EoCases.__smtx_type_wf_rec.case_2 x_a0, EoCases.__smtx_type_wf_rec.case_3 x_a0] = [EoCases.__smtx_type_wf_rec.case_0 x_a0, EoCases.__smtx_type_wf_rec.case_1 x_a0, EoCases.__smtx_type_wf_rec.case_2 x_a0] ++ [EoCases.__smtx_type_wf_rec.case_3 x_a0] ++ [] from rfl)
    otherwise ⟨hl_3⟩ using hl_0 hl_1 hl_2
  group_none hinv4 hG with ⟨hl_0, hl_1, hl_2, hl_3⟩

theorem cases_0_1_eo__24smtx_5ftype_5fwf_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_1_eo__24smtx_5ftype_5fwf_5frec s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__smtx_type_wf_rec.case_4 x_a0, EoCases.__smtx_type_wf_rec.case_5 x_a0, EoCases.__smtx_type_wf_rec.case_6 x_a0, EoCases.__smtx_type_wf_rec.case_7 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_type_wf_rec.case_4 x_a0 = none ∧ EoCases.__smtx_type_wf_rec.case_5 x_a0 = none ∧ EoCases.__smtx_type_wf_rec.case_6 x_a0 = none ∧ EoCases.__smtx_type_wf_rec.case_7 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_1_eo__24smtx_5ftype_5fwf_5frec
  have hG := Store.Grows.refl s
  group_step with case_4_eo__24smtx_5ftype_5fwf_5frec_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_type_wf_rec.case_4 x_a0, EoCases.__smtx_type_wf_rec.case_5 x_a0, EoCases.__smtx_type_wf_rec.case_6 x_a0, EoCases.__smtx_type_wf_rec.case_7 x_a0] = [] ++ [EoCases.__smtx_type_wf_rec.case_4 x_a0] ++ [EoCases.__smtx_type_wf_rec.case_5 x_a0, EoCases.__smtx_type_wf_rec.case_6 x_a0, EoCases.__smtx_type_wf_rec.case_7 x_a0] from rfl)
    otherwise ⟨hl_4⟩ using
  group_step with case_5_eo__24smtx_5ftype_5fwf_5frec_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_type_wf_rec.case_4 x_a0, EoCases.__smtx_type_wf_rec.case_5 x_a0, EoCases.__smtx_type_wf_rec.case_6 x_a0, EoCases.__smtx_type_wf_rec.case_7 x_a0] = [EoCases.__smtx_type_wf_rec.case_4 x_a0] ++ [EoCases.__smtx_type_wf_rec.case_5 x_a0] ++ [EoCases.__smtx_type_wf_rec.case_6 x_a0, EoCases.__smtx_type_wf_rec.case_7 x_a0] from rfl)
    otherwise ⟨hl_5⟩ using hl_4
  group_step with case_6_eo__24smtx_5ftype_5fwf_5frec_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_type_wf_rec.case_4 x_a0, EoCases.__smtx_type_wf_rec.case_5 x_a0, EoCases.__smtx_type_wf_rec.case_6 x_a0, EoCases.__smtx_type_wf_rec.case_7 x_a0] = [EoCases.__smtx_type_wf_rec.case_4 x_a0, EoCases.__smtx_type_wf_rec.case_5 x_a0] ++ [EoCases.__smtx_type_wf_rec.case_6 x_a0] ++ [EoCases.__smtx_type_wf_rec.case_7 x_a0] from rfl)
    otherwise ⟨hl_6⟩ using hl_4 hl_5
  group_step with case_7_eo__24smtx_5ftype_5fwf_5frec_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_type_wf_rec.case_4 x_a0, EoCases.__smtx_type_wf_rec.case_5 x_a0, EoCases.__smtx_type_wf_rec.case_6 x_a0, EoCases.__smtx_type_wf_rec.case_7 x_a0] = [EoCases.__smtx_type_wf_rec.case_4 x_a0, EoCases.__smtx_type_wf_rec.case_5 x_a0, EoCases.__smtx_type_wf_rec.case_6 x_a0] ++ [EoCases.__smtx_type_wf_rec.case_7 x_a0] ++ [] from rfl)
    otherwise ⟨hl_7⟩ using hl_4 hl_5 hl_6
  group_none hinv4 hG with ⟨hl_4, hl_5, hl_6, hl_7⟩

theorem cases_0_2_eo__24smtx_5ftype_5fwf_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_2_eo__24smtx_5ftype_5fwf_5frec s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__smtx_type_wf_rec.case_8 x_a0, EoCases.__smtx_type_wf_rec.case_9 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_type_wf_rec.case_8 x_a0 = none ∧ EoCases.__smtx_type_wf_rec.case_9 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_2_eo__24smtx_5ftype_5fwf_5frec
  have hG := Store.Grows.refl s
  group_step with case_8_eo__24smtx_5ftype_5fwf_5frec_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_type_wf_rec.case_8 x_a0, EoCases.__smtx_type_wf_rec.case_9 x_a0] = [] ++ [EoCases.__smtx_type_wf_rec.case_8 x_a0] ++ [EoCases.__smtx_type_wf_rec.case_9 x_a0] from rfl)
    otherwise ⟨hl_8⟩ using
  group_step with case_9_eo__24smtx_5ftype_5fwf_5frec_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_type_wf_rec.case_8 x_a0, EoCases.__smtx_type_wf_rec.case_9 x_a0] = [EoCases.__smtx_type_wf_rec.case_8 x_a0] ++ [EoCases.__smtx_type_wf_rec.case_9 x_a0] ++ [] from rfl)
    otherwise ⟨hl_9⟩ using hl_8
  group_none hinv2 hG with ⟨hl_8, hl_9⟩

/-- logos's `__smtx_type_wf_rec` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24smtx_5ftype_5fwf_5frec.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __smtx_type_wf_rec x_a0 =
      (firstSome [EoCases.__smtx_type_wf_rec.case_0 x_a0, EoCases.__smtx_type_wf_rec.case_1 x_a0, EoCases.__smtx_type_wf_rec.case_2 x_a0, EoCases.__smtx_type_wf_rec.case_3 x_a0, EoCases.__smtx_type_wf_rec.case_4 x_a0, EoCases.__smtx_type_wf_rec.case_5 x_a0, EoCases.__smtx_type_wf_rec.case_6 x_a0, EoCases.__smtx_type_wf_rec.case_7 x_a0, EoCases.__smtx_type_wf_rec.case_8 x_a0, EoCases.__smtx_type_wf_rec.case_9 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __smtx_type_wf_rec
  unfold EoCases.__smtx_type_wf_rec.case_0 EoCases.__smtx_type_wf_rec.case_1 EoCases.__smtx_type_wf_rec.case_2 EoCases.__smtx_type_wf_rec.case_3 EoCases.__smtx_type_wf_rec.case_4 EoCases.__smtx_type_wf_rec.case_5 EoCases.__smtx_type_wf_rec.case_6 EoCases.__smtx_type_wf_rec.case_7 EoCases.__smtx_type_wf_rec.case_8 EoCases.__smtx_type_wf_rec.case_9
  logos_eq

theorem body_eo__24smtx_5ftype_5fwf_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24smtx_5ftype_5fwf_5frec s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_type_wf_rec x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24smtx_5ftype_5fwf_5frec.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24smtx_5ftype_5fwf_5frec
  have hG := Store.Grows.refl s
  body_group_step with cases_0_0_eo__24smtx_5ftype_5fwf_5frec_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_type_wf_rec.case_0 x_a0, EoCases.__smtx_type_wf_rec.case_1 x_a0, EoCases.__smtx_type_wf_rec.case_2 x_a0, EoCases.__smtx_type_wf_rec.case_3 x_a0, EoCases.__smtx_type_wf_rec.case_4 x_a0, EoCases.__smtx_type_wf_rec.case_5 x_a0, EoCases.__smtx_type_wf_rec.case_6 x_a0, EoCases.__smtx_type_wf_rec.case_7 x_a0, EoCases.__smtx_type_wf_rec.case_8 x_a0, EoCases.__smtx_type_wf_rec.case_9 x_a0] = [] ++ [EoCases.__smtx_type_wf_rec.case_0 x_a0, EoCases.__smtx_type_wf_rec.case_1 x_a0, EoCases.__smtx_type_wf_rec.case_2 x_a0, EoCases.__smtx_type_wf_rec.case_3 x_a0] ++ [EoCases.__smtx_type_wf_rec.case_4 x_a0, EoCases.__smtx_type_wf_rec.case_5 x_a0, EoCases.__smtx_type_wf_rec.case_6 x_a0, EoCases.__smtx_type_wf_rec.case_7 x_a0, EoCases.__smtx_type_wf_rec.case_8 x_a0, EoCases.__smtx_type_wf_rec.case_9 x_a0] from rfl)
    otherwise ⟨hl_0, hl_1, hl_2, hl_3⟩ using
  body_group_step with cases_0_1_eo__24smtx_5ftype_5fwf_5frec_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_type_wf_rec.case_0 x_a0, EoCases.__smtx_type_wf_rec.case_1 x_a0, EoCases.__smtx_type_wf_rec.case_2 x_a0, EoCases.__smtx_type_wf_rec.case_3 x_a0, EoCases.__smtx_type_wf_rec.case_4 x_a0, EoCases.__smtx_type_wf_rec.case_5 x_a0, EoCases.__smtx_type_wf_rec.case_6 x_a0, EoCases.__smtx_type_wf_rec.case_7 x_a0, EoCases.__smtx_type_wf_rec.case_8 x_a0, EoCases.__smtx_type_wf_rec.case_9 x_a0] = [EoCases.__smtx_type_wf_rec.case_0 x_a0, EoCases.__smtx_type_wf_rec.case_1 x_a0, EoCases.__smtx_type_wf_rec.case_2 x_a0, EoCases.__smtx_type_wf_rec.case_3 x_a0] ++ [EoCases.__smtx_type_wf_rec.case_4 x_a0, EoCases.__smtx_type_wf_rec.case_5 x_a0, EoCases.__smtx_type_wf_rec.case_6 x_a0, EoCases.__smtx_type_wf_rec.case_7 x_a0] ++ [EoCases.__smtx_type_wf_rec.case_8 x_a0, EoCases.__smtx_type_wf_rec.case_9 x_a0] from rfl)
    otherwise ⟨hl_4, hl_5, hl_6, hl_7⟩ using hl_0 hl_1 hl_2 hl_3
  body_group_step with cases_0_2_eo__24smtx_5ftype_5fwf_5frec_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_type_wf_rec.case_0 x_a0, EoCases.__smtx_type_wf_rec.case_1 x_a0, EoCases.__smtx_type_wf_rec.case_2 x_a0, EoCases.__smtx_type_wf_rec.case_3 x_a0, EoCases.__smtx_type_wf_rec.case_4 x_a0, EoCases.__smtx_type_wf_rec.case_5 x_a0, EoCases.__smtx_type_wf_rec.case_6 x_a0, EoCases.__smtx_type_wf_rec.case_7 x_a0, EoCases.__smtx_type_wf_rec.case_8 x_a0, EoCases.__smtx_type_wf_rec.case_9 x_a0] = [EoCases.__smtx_type_wf_rec.case_0 x_a0, EoCases.__smtx_type_wf_rec.case_1 x_a0, EoCases.__smtx_type_wf_rec.case_2 x_a0, EoCases.__smtx_type_wf_rec.case_3 x_a0, EoCases.__smtx_type_wf_rec.case_4 x_a0, EoCases.__smtx_type_wf_rec.case_5 x_a0, EoCases.__smtx_type_wf_rec.case_6 x_a0, EoCases.__smtx_type_wf_rec.case_7 x_a0] ++ [EoCases.__smtx_type_wf_rec.case_8 x_a0, EoCases.__smtx_type_wf_rec.case_9 x_a0] ++ [] from rfl)
    otherwise ⟨hl_8, hl_9⟩ using hl_0 hl_1 hl_2 hl_3 hl_4 hl_5 hl_6 hl_7
  body_stuck hinv3 hG using hl_0 hl_1 hl_2 hl_3 hl_4 hl_5 hl_6 hl_7 hl_8 hl_9 in EoCases.__smtx_type_wf_rec.case_0 EoCases.__smtx_type_wf_rec.case_1 EoCases.__smtx_type_wf_rec.case_2 EoCases.__smtx_type_wf_rec.case_3 EoCases.__smtx_type_wf_rec.case_4 EoCases.__smtx_type_wf_rec.case_5 EoCases.__smtx_type_wf_rec.case_6 EoCases.__smtx_type_wf_rec.case_7 EoCases.__smtx_type_wf_rec.case_8 EoCases.__smtx_type_wf_rec.case_9 splitting x_a0

theorem eo__24smtx_5ftype_5fwf_5frec_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24smtx_5ftype_5fwf_5frec.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24smtx_5ftype_5fwf_5frec
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 1003#u32 _ [a0] rfl
    (fun s1 => body_eo__24smtx_5ftype_5fwf_5frec s1 a0) (fun s' t => Represents.rep s' t (__smtx_type_wf_rec x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, y0, hargs, hb0, hr⟩ := ProgramSem.of_1003 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_1003 ⟨a0, x_a0, rfl, Rep.mono hpre h_a0, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24smtx_5ftype_5fwf_5frec_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

end pathos_compiled_checker
