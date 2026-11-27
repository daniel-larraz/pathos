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

theorem case_0_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_0 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2eBoolean.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__smtx_typeof.case_0
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s e_v2 (by rw [he_v2]; exact empty_args) hinv h64 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying h_a0 h_v1
  case_done hinv1 hG with h_v2 in EoCases.__smtx_typeof.case_0 using

theorem case_1_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_1_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_1 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_1 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_1 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2eNumeral.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__smtx_typeof.case_1
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eInt.construct s e_v2 (by rw [he_v2]; exact empty_args) hinv h64 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying h_a0 h_v1
  case_done hinv1 hG with h_v2 in EoCases.__smtx_typeof.case_1 using

theorem case_2_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_2_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_2 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_2 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_2 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2eRational.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__smtx_typeof.case_2
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eReal.construct s e_v2 (by rw [he_v2]; exact empty_args) hinv h64 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying h_a0 h_v1
  case_done hinv1 hG with h_v2 in EoCases.__smtx_typeof.case_2 using

theorem case_3_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_3_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_3 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_3 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_3 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_3_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2eString.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__smtx_typeof.case_3
  step as ⟨e_v2, he_v2⟩
  store_step with Store.native_spec_string_valid s e_v2 (by rw [he_v2]; rfl) h_v1 hinv h64 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying h_a0 h_v1
  rw [← Bridge.native_string_valid] at h_v2
  have h_ite_v6 := (show if_0_eo__24smtx_5ftypeof s1 v2 ⦃ r s' => s'.Inv ∧ s1.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_0_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s1
    rcases Store.boolean_value_native h_v2 with ⟨hx_3, hbv_3⟩ | ⟨hx_3, hbv_3⟩
    · ite_branch hbv_3
      step as ⟨e_v3, he_v3⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eChar.construct s1 e_v3 (by rw [he_v3]; exact empty_args) hinv1 h64 as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
      step as ⟨e_v4, he_v4⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eSeq.construct s2 e_v4 (by rw [he_v4]; rfl) h_v3 hinv2 h64 as ⟨v4, s3, hinv3, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
      ite_done hinv3 hG with (native_ite_true_rep _ hx_3 h_v4)
    · ite_branch hbv_3
      step as ⟨e_v5, he_v5⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s1 e_v5 (by rw [he_v5]; exact empty_args) hinv1 h64 as ⟨v5, s2, hinv2, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2
      ite_done hinv2 hG with (native_ite_false_rep _ hx_3 h_v5))
  store_step with h_ite_v6 as ⟨v6, s2, hinv2, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2
  case_done hinv2 hG with h_v6 in EoCases.__smtx_typeof.case_3 using

theorem case_4_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_4_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_4 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_4 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_4 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_4_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2eBinary.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_4
  simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.raw_int_u32_spec s 0#u32 (0) (by scalar_tac) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  step as ⟨e_v4, he_v4⟩
  store_step with Store.native_spec_zleq s1 e_v4 (by rw [he_v4]; rfl) h_v3 h_v1 hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  rw [← Bridge.native_zleq] at h_v4
  step as ⟨e_v5, he_v5⟩
  store_step with Store.native_spec_int_pow2 s2 e_v5 (by rw [he_v5]; rfl) h_v1 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  rw [← Bridge.native_int_pow2] at h_v5
  step as ⟨e_v6, he_v6⟩
  store_step with Store.native_spec_mod_total s3 e_v6 (by rw [he_v6]; rfl) h_v2 h_v5 hinv3 h64 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  rw [← Bridge.native_mod_total] at h_v6
  step as ⟨e_v7, he_v7⟩
  store_step with Store.native_spec_zeq s4 e_v7 (by rw [he_v7]; rfl) h_v2 h_v6 hinv4 h64 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  rw [← Bridge.native_zeq] at h_v7
  step as ⟨e_v8, he_v8⟩
  store_step with Store.native_spec_and s5 e_v8 (by rw [he_v8]; rfl) h_v4 h_v7 hinv5 h64 as ⟨v8, s6, hinv6, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  rw [← Bridge.native_and] at h_v8
  have h_ite_v12 := (show if_1_eo__24smtx_5ftypeof s6 v8 v1 ⦃ r s' => s'.Inv ∧ s6.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_1_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s6
    rcases Store.boolean_value_native h_v8 with ⟨hx_9, hbv_9⟩ | ⟨hx_9, hbv_9⟩
    · ite_branch hbv_9
      step as ⟨e_v9, he_v9⟩
      store_step with Store.native_spec_int_to_nat s6 e_v9 (by rw [he_v9]; rfl) h_v1 hinv6 h64 as ⟨v9, s7, hinv7, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
      rw [← Bridge.native_int_to_nat] at h_v9
      step as ⟨e_v10, he_v10⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eBitVec.construct s7 e_v10 (by rw [he_v10]; rfl) h_v9 hinv7 h64 as ⟨v10, s8, hinv8, h_v10⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
      ite_done hinv8 hG with (native_ite_true_rep _ hx_9 h_v10)
    · ite_branch hbv_9
      step as ⟨e_v11, he_v11⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s6 e_v11 (by rw [he_v11]; exact empty_args) hinv6 h64 as ⟨v11, s7, hinv7, h_v11⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
      ite_done hinv7 hG with (native_ite_false_rep _ hx_9 h_v11))
  store_step with h_ite_v12 as ⟨v12, s7, hinv7, h_v12⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv7 hG with h_v12 in EoCases.__smtx_typeof.case_4 using

theorem case_5_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_5_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_5 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_5 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_5 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_5_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2eite.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ ⟨v3, x_v3, h_v3⟩ else hinv hG in EoCases.__smtx_typeof.case_5
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v4, s1, hinv1, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v5, s2, hinv2, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  store_step with ih.eo__24smtx_5ftypeof s2 v3 _ hinv2 h64 (hG.rem hrem) h_v3 as ⟨v6, s3, hinv3, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with ih.eo__24smtx_5ftypeof_5fite s3 v4 v5 v6 _ _ _ hinv3 h64 (hG.rem hrem) h_v4 h_v5 h_v6 as ⟨v7, s4, hinv4, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  case_done hinv4 hG with h_v7 in EoCases.__smtx_typeof.case_5 using

theorem case_6_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_6_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_6 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_6 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_6 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_6_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2enot.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__smtx_typeof.case_6
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying h_a0 h_v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s1 e_v3 (by rw [he_v3]; exact empty_args) hinv1 h64 as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  step as ⟨e_v4, he_v4⟩
  store_step with Store.native_spec_Teq s2 e_v4 (by rw [he_v4]; rfl) h_v2 h_v3 hinv2 h64 as ⟨v4, s3, hinv3, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  have h_ite_v7 := (show if_2_eo__24smtx_5ftypeof s3 v4 ⦃ r s' => s'.Inv ∧ s3.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_2_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s3
    rcases Store.boolean_value_native h_v4 with ⟨hx_5, hbv_5⟩ | ⟨hx_5, hbv_5⟩
    · ite_branch hbv_5
      step as ⟨e_v5, he_v5⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s3 e_v5 (by rw [he_v5]; exact empty_args) hinv3 h64 as ⟨v5, s4, hinv4, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
      ite_done hinv4 hG with (native_ite_true_rep _ hx_5 h_v5)
    · ite_branch hbv_5
      step as ⟨e_v6, he_v6⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s3 e_v6 (by rw [he_v6]; exact empty_args) hinv3 h64 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
      ite_done hinv4 hG with (native_ite_false_rep _ hx_5 h_v6))
  store_step with h_ite_v7 as ⟨v7, s4, hinv4, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv4 hG with h_v7 in EoCases.__smtx_typeof.case_6 using

theorem case_7_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_7_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_7 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_7 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_7 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_7_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2eor.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_7
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s1 e_v4 (by rw [he_v4]; exact empty_args) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with Store.native_spec_Teq s2 e_v5 (by rw [he_v5]; rfl) h_v3 h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  have h_ite_v13 := (show if_4_eo__24smtx_5ftypeof s3 v5 v2 ⦃ r s' => s'.Inv ∧ s3.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_4_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s3
    rcases Store.boolean_value_native h_v5 with ⟨hx_6, hbv_6⟩ | ⟨hx_6, hbv_6⟩
    · ite_branch hbv_6
      store_step with ih.eo__24smtx_5ftypeof s3 v2 _ hinv3 h64 (hG.rem hrem) h_v2 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
      step as ⟨e_v7, he_v7⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s4 e_v7 (by rw [he_v7]; exact empty_args) hinv4 h64 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
      step as ⟨e_v8, he_v8⟩
      store_step with Store.native_spec_Teq s5 e_v8 (by rw [he_v8]; rfl) h_v6 h_v7 hinv5 h64 as ⟨v8, s6, hinv6, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
      have h_ite_v11 := (show if_3_eo__24smtx_5ftypeof s6 v8 ⦃ r s' => s'.Inv ∧ s6.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_3_eo__24smtx_5ftypeof
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s6
        rcases Store.boolean_value_native h_v8 with ⟨hx_9, hbv_9⟩ | ⟨hx_9, hbv_9⟩
        · ite_branch hbv_9
          step as ⟨e_v9, he_v9⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s6 e_v9 (by rw [he_v9]; exact empty_args) hinv6 h64 as ⟨v9, s7, hinv7, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
          ite_done hinv7 hG with (native_ite_true_rep _ hx_9 h_v9)
        · ite_branch hbv_9
          step as ⟨e_v10, he_v10⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s6 e_v10 (by rw [he_v10]; exact empty_args) hinv6 h64 as ⟨v10, s7, hinv7, h_v10⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
          ite_done hinv7 hG with (native_ite_false_rep _ hx_9 h_v10))
      store_step with h_ite_v11 as ⟨v11, s7, hinv7, h_v11⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
      ite_done hinv7 hG with (native_ite_true_rep _ hx_6 h_v11)
    · ite_branch hbv_6
      step as ⟨e_v12, he_v12⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s3 e_v12 (by rw [he_v12]; exact empty_args) hinv3 h64 as ⟨v12, s4, hinv4, h_v12⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
      ite_done hinv4 hG with (native_ite_false_rep _ hx_6 h_v12))
  store_step with h_ite_v13 as ⟨v13, s4, hinv4, h_v13⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  case_done hinv4 hG with h_v13 in EoCases.__smtx_typeof.case_7 using

theorem case_8_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_8_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_8 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_8 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_8 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_8_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2eand.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_8
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s1 e_v4 (by rw [he_v4]; exact empty_args) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with Store.native_spec_Teq s2 e_v5 (by rw [he_v5]; rfl) h_v3 h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  have h_ite_v13 := (show if_6_eo__24smtx_5ftypeof s3 v5 v2 ⦃ r s' => s'.Inv ∧ s3.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_6_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s3
    rcases Store.boolean_value_native h_v5 with ⟨hx_6, hbv_6⟩ | ⟨hx_6, hbv_6⟩
    · ite_branch hbv_6
      store_step with ih.eo__24smtx_5ftypeof s3 v2 _ hinv3 h64 (hG.rem hrem) h_v2 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
      step as ⟨e_v7, he_v7⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s4 e_v7 (by rw [he_v7]; exact empty_args) hinv4 h64 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
      step as ⟨e_v8, he_v8⟩
      store_step with Store.native_spec_Teq s5 e_v8 (by rw [he_v8]; rfl) h_v6 h_v7 hinv5 h64 as ⟨v8, s6, hinv6, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
      have h_ite_v11 := (show if_5_eo__24smtx_5ftypeof s6 v8 ⦃ r s' => s'.Inv ∧ s6.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_5_eo__24smtx_5ftypeof
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s6
        rcases Store.boolean_value_native h_v8 with ⟨hx_9, hbv_9⟩ | ⟨hx_9, hbv_9⟩
        · ite_branch hbv_9
          step as ⟨e_v9, he_v9⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s6 e_v9 (by rw [he_v9]; exact empty_args) hinv6 h64 as ⟨v9, s7, hinv7, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
          ite_done hinv7 hG with (native_ite_true_rep _ hx_9 h_v9)
        · ite_branch hbv_9
          step as ⟨e_v10, he_v10⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s6 e_v10 (by rw [he_v10]; exact empty_args) hinv6 h64 as ⟨v10, s7, hinv7, h_v10⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
          ite_done hinv7 hG with (native_ite_false_rep _ hx_9 h_v10))
      store_step with h_ite_v11 as ⟨v11, s7, hinv7, h_v11⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
      ite_done hinv7 hG with (native_ite_true_rep _ hx_6 h_v11)
    · ite_branch hbv_6
      step as ⟨e_v12, he_v12⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s3 e_v12 (by rw [he_v12]; exact empty_args) hinv3 h64 as ⟨v12, s4, hinv4, h_v12⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
      ite_done hinv4 hG with (native_ite_false_rep _ hx_6 h_v12))
  store_step with h_ite_v13 as ⟨v13, s4, hinv4, h_v13⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  case_done hinv4 hG with h_v13 in EoCases.__smtx_typeof.case_8 using

theorem case_9_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_9_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_9 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_9 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_9 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_9_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2e_3d_3e.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_9
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s1 e_v4 (by rw [he_v4]; exact empty_args) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with Store.native_spec_Teq s2 e_v5 (by rw [he_v5]; rfl) h_v3 h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  have h_ite_v13 := (show if_8_eo__24smtx_5ftypeof s3 v5 v2 ⦃ r s' => s'.Inv ∧ s3.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_8_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s3
    rcases Store.boolean_value_native h_v5 with ⟨hx_6, hbv_6⟩ | ⟨hx_6, hbv_6⟩
    · ite_branch hbv_6
      store_step with ih.eo__24smtx_5ftypeof s3 v2 _ hinv3 h64 (hG.rem hrem) h_v2 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
      step as ⟨e_v7, he_v7⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s4 e_v7 (by rw [he_v7]; exact empty_args) hinv4 h64 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
      step as ⟨e_v8, he_v8⟩
      store_step with Store.native_spec_Teq s5 e_v8 (by rw [he_v8]; rfl) h_v6 h_v7 hinv5 h64 as ⟨v8, s6, hinv6, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
      have h_ite_v11 := (show if_7_eo__24smtx_5ftypeof s6 v8 ⦃ r s' => s'.Inv ∧ s6.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_7_eo__24smtx_5ftypeof
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s6
        rcases Store.boolean_value_native h_v8 with ⟨hx_9, hbv_9⟩ | ⟨hx_9, hbv_9⟩
        · ite_branch hbv_9
          step as ⟨e_v9, he_v9⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s6 e_v9 (by rw [he_v9]; exact empty_args) hinv6 h64 as ⟨v9, s7, hinv7, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
          ite_done hinv7 hG with (native_ite_true_rep _ hx_9 h_v9)
        · ite_branch hbv_9
          step as ⟨e_v10, he_v10⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s6 e_v10 (by rw [he_v10]; exact empty_args) hinv6 h64 as ⟨v10, s7, hinv7, h_v10⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
          ite_done hinv7 hG with (native_ite_false_rep _ hx_9 h_v10))
      store_step with h_ite_v11 as ⟨v11, s7, hinv7, h_v11⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
      ite_done hinv7 hG with (native_ite_true_rep _ hx_6 h_v11)
    · ite_branch hbv_6
      step as ⟨e_v12, he_v12⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s3 e_v12 (by rw [he_v12]; exact empty_args) hinv3 h64 as ⟨v12, s4, hinv4, h_v12⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
      ite_done hinv4 hG with (native_ite_false_rep _ hx_6 h_v12))
  store_step with h_ite_v13 as ⟨v13, s4, hinv4, h_v13⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  case_done hinv4 hG with h_v13 in EoCases.__smtx_typeof.case_9 using

theorem case_10_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_10_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_10 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_10 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_10 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_10_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2exor.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_10
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s1 e_v4 (by rw [he_v4]; exact empty_args) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with Store.native_spec_Teq s2 e_v5 (by rw [he_v5]; rfl) h_v3 h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  have h_ite_v13 := (show if_10_eo__24smtx_5ftypeof s3 v5 v2 ⦃ r s' => s'.Inv ∧ s3.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_10_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s3
    rcases Store.boolean_value_native h_v5 with ⟨hx_6, hbv_6⟩ | ⟨hx_6, hbv_6⟩
    · ite_branch hbv_6
      store_step with ih.eo__24smtx_5ftypeof s3 v2 _ hinv3 h64 (hG.rem hrem) h_v2 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
      step as ⟨e_v7, he_v7⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s4 e_v7 (by rw [he_v7]; exact empty_args) hinv4 h64 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
      step as ⟨e_v8, he_v8⟩
      store_step with Store.native_spec_Teq s5 e_v8 (by rw [he_v8]; rfl) h_v6 h_v7 hinv5 h64 as ⟨v8, s6, hinv6, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
      have h_ite_v11 := (show if_9_eo__24smtx_5ftypeof s6 v8 ⦃ r s' => s'.Inv ∧ s6.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_9_eo__24smtx_5ftypeof
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s6
        rcases Store.boolean_value_native h_v8 with ⟨hx_9, hbv_9⟩ | ⟨hx_9, hbv_9⟩
        · ite_branch hbv_9
          step as ⟨e_v9, he_v9⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s6 e_v9 (by rw [he_v9]; exact empty_args) hinv6 h64 as ⟨v9, s7, hinv7, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
          ite_done hinv7 hG with (native_ite_true_rep _ hx_9 h_v9)
        · ite_branch hbv_9
          step as ⟨e_v10, he_v10⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s6 e_v10 (by rw [he_v10]; exact empty_args) hinv6 h64 as ⟨v10, s7, hinv7, h_v10⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
          ite_done hinv7 hG with (native_ite_false_rep _ hx_9 h_v10))
      store_step with h_ite_v11 as ⟨v11, s7, hinv7, h_v11⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
      ite_done hinv7 hG with (native_ite_true_rep _ hx_6 h_v11)
    · ite_branch hbv_6
      step as ⟨e_v12, he_v12⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s3 e_v12 (by rw [he_v12]; exact empty_args) hinv3 h64 as ⟨v12, s4, hinv4, h_v12⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
      ite_done hinv4 hG with (native_ite_false_rep _ hx_6 h_v12))
  store_step with h_ite_v13 as ⟨v13, s4, hinv4, h_v13⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  case_done hinv4 hG with h_v13 in EoCases.__smtx_typeof.case_10 using

theorem case_11_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_11_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_11 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_11 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_11 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_11_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2e_3d.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_11
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24smtx_5ftypeof_5f_3d s2 v3 v4 _ _ hinv2 h64 (hG.rem hrem) h_v3 h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__smtx_typeof.case_11 using

theorem case_12_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_12_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_12 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_12 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_12 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_12_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2ebind.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_12
  store_step with ih.eo__24smtx_5ftypeof s v2 _ hinv h64 hrem h_v2 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24smtx_5ftypeof_5fbindings s1 v1 v3 _ _ hinv1 h64 (hG.rem hrem) h_v1 h_v3 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  case_done hinv2 hG with h_v4 in EoCases.__smtx_typeof.case_12 using

theorem case_13_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_13_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_13 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_13 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_13 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_13_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2e_40purify.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__smtx_typeof.case_13
  case_again hinv hG with h_v1 in EoCases.__smtx_typeof.case_13 using

theorem case_14_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_14_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_14 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_14 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_14 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_14_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2e_2b.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_14
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2 s2 v3 v4 _ _ hinv2 h64 (hG.rem hrem) h_v3 h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__smtx_typeof.case_14 using

theorem case_15_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_15_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_15 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_15 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_15 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_15_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2e_2d.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_15
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2 s2 v3 v4 _ _ hinv2 h64 (hG.rem hrem) h_v3 h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__smtx_typeof.case_15 using

theorem case_16_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_16_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_16 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_16 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_16 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_16_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2e_2a.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_16
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2 s2 v3 v4 _ _ hinv2 h64 (hG.rem hrem) h_v3 h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__smtx_typeof.case_16 using

theorem case_17_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_17_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_17 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_17 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_17 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_17_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2e_3c.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_17
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s2 e_v5 (by rw [he_v5]; exact empty_args) hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  store_step with ih.eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2_5fret s3 v3 v4 v5 _ _ _ hinv3 h64 (hG.rem hrem) h_v3 h_v4 h_v5 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  case_done hinv4 hG with h_v6 in EoCases.__smtx_typeof.case_17 using

theorem case_18_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_18_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_18 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_18 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_18 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_18_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2e_3c_3d.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_18
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s2 e_v5 (by rw [he_v5]; exact empty_args) hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  store_step with ih.eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2_5fret s3 v3 v4 v5 _ _ _ hinv3 h64 (hG.rem hrem) h_v3 h_v4 h_v5 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  case_done hinv4 hG with h_v6 in EoCases.__smtx_typeof.case_18 using

theorem case_19_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_19_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_19 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_19 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_19 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_19_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2e_3e.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_19
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s2 e_v5 (by rw [he_v5]; exact empty_args) hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  store_step with ih.eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2_5fret s3 v3 v4 v5 _ _ _ hinv3 h64 (hG.rem hrem) h_v3 h_v4 h_v5 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  case_done hinv4 hG with h_v6 in EoCases.__smtx_typeof.case_19 using

theorem case_20_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_20_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_20 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_20 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_20 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_20_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2e_3e_3d.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_20
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s2 e_v5 (by rw [he_v5]; exact empty_args) hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  store_step with ih.eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2_5fret s3 v3 v4 v5 _ _ _ hinv3 h64 (hG.rem hrem) h_v3 h_v4 h_v5 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  case_done hinv4 hG with h_v6 in EoCases.__smtx_typeof.case_20 using

theorem case_21_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_21_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_21 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_21 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_21 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_21_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2eto_5freal.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__smtx_typeof.case_21
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying h_a0 h_v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eInt.construct s1 e_v3 (by rw [he_v3]; exact empty_args) hinv1 h64 as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  step as ⟨e_v4, he_v4⟩
  store_step with Store.native_spec_Teq s2 e_v4 (by rw [he_v4]; rfl) h_v2 h_v3 hinv2 h64 as ⟨v4, s3, hinv3, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  have h_ite_v7 := (show if_11_eo__24smtx_5ftypeof s3 v4 ⦃ r s' => s'.Inv ∧ s3.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_11_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s3
    rcases Store.boolean_value_native h_v4 with ⟨hx_5, hbv_5⟩ | ⟨hx_5, hbv_5⟩
    · ite_branch hbv_5
      step as ⟨e_v5, he_v5⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eReal.construct s3 e_v5 (by rw [he_v5]; exact empty_args) hinv3 h64 as ⟨v5, s4, hinv4, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
      ite_done hinv4 hG with (native_ite_true_rep _ hx_5 h_v5)
    · ite_branch hbv_5
      step as ⟨e_v6, he_v6⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s3 e_v6 (by rw [he_v6]; exact empty_args) hinv3 h64 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
      ite_done hinv4 hG with (native_ite_false_rep _ hx_5 h_v6))
  store_step with h_ite_v7 as ⟨v7, s4, hinv4, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv4 hG with h_v7 in EoCases.__smtx_typeof.case_21 using

theorem case_22_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_22_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_22 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_22 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_22 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_22_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2eto_5fint.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__smtx_typeof.case_22
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying h_a0 h_v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eReal.construct s1 e_v3 (by rw [he_v3]; exact empty_args) hinv1 h64 as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  step as ⟨e_v4, he_v4⟩
  store_step with Store.native_spec_Teq s2 e_v4 (by rw [he_v4]; rfl) h_v2 h_v3 hinv2 h64 as ⟨v4, s3, hinv3, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  have h_ite_v7 := (show if_12_eo__24smtx_5ftypeof s3 v4 ⦃ r s' => s'.Inv ∧ s3.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_12_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s3
    rcases Store.boolean_value_native h_v4 with ⟨hx_5, hbv_5⟩ | ⟨hx_5, hbv_5⟩
    · ite_branch hbv_5
      step as ⟨e_v5, he_v5⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eInt.construct s3 e_v5 (by rw [he_v5]; exact empty_args) hinv3 h64 as ⟨v5, s4, hinv4, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
      ite_done hinv4 hG with (native_ite_true_rep _ hx_5 h_v5)
    · ite_branch hbv_5
      step as ⟨e_v6, he_v6⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s3 e_v6 (by rw [he_v6]; exact empty_args) hinv3 h64 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
      ite_done hinv4 hG with (native_ite_false_rep _ hx_5 h_v6))
  store_step with h_ite_v7 as ⟨v7, s4, hinv4, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv4 hG with h_v7 in EoCases.__smtx_typeof.case_22 using

theorem case_23_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_23_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_23 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_23 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_23 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_23_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2eis_5fint.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__smtx_typeof.case_23
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying h_a0 h_v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eReal.construct s1 e_v3 (by rw [he_v3]; exact empty_args) hinv1 h64 as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  step as ⟨e_v4, he_v4⟩
  store_step with Store.native_spec_Teq s2 e_v4 (by rw [he_v4]; rfl) h_v2 h_v3 hinv2 h64 as ⟨v4, s3, hinv3, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  have h_ite_v7 := (show if_13_eo__24smtx_5ftypeof s3 v4 ⦃ r s' => s'.Inv ∧ s3.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_13_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s3
    rcases Store.boolean_value_native h_v4 with ⟨hx_5, hbv_5⟩ | ⟨hx_5, hbv_5⟩
    · ite_branch hbv_5
      step as ⟨e_v5, he_v5⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s3 e_v5 (by rw [he_v5]; exact empty_args) hinv3 h64 as ⟨v5, s4, hinv4, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
      ite_done hinv4 hG with (native_ite_true_rep _ hx_5 h_v5)
    · ite_branch hbv_5
      step as ⟨e_v6, he_v6⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s3 e_v6 (by rw [he_v6]; exact empty_args) hinv3 h64 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
      ite_done hinv4 hG with (native_ite_false_rep _ hx_5 h_v6))
  store_step with h_ite_v7 as ⟨v7, s4, hinv4, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv4 hG with h_v7 in EoCases.__smtx_typeof.case_23 using

theorem case_24_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_24_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_24 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_24 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_24 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_24_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2eabs.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__smtx_typeof.case_24
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying h_a0 h_v1
  store_step with ih.eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f1 s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  case_done hinv2 hG with h_v3 in EoCases.__smtx_typeof.case_24 using

theorem case_25_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_25_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_25 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_25 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_25 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_25_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2euneg.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__smtx_typeof.case_25
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying h_a0 h_v1
  store_step with ih.eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f1 s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  case_done hinv2 hG with h_v3 in EoCases.__smtx_typeof.case_25 using

theorem case_26_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_26_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_26 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_26 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_26 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_26_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2ediv.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_26
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eInt.construct s1 e_v4 (by rw [he_v4]; exact empty_args) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with Store.native_spec_Teq s2 e_v5 (by rw [he_v5]; rfl) h_v3 h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  have h_ite_v13 := (show if_15_eo__24smtx_5ftypeof s3 v5 v2 ⦃ r s' => s'.Inv ∧ s3.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_15_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s3
    rcases Store.boolean_value_native h_v5 with ⟨hx_6, hbv_6⟩ | ⟨hx_6, hbv_6⟩
    · ite_branch hbv_6
      store_step with ih.eo__24smtx_5ftypeof s3 v2 _ hinv3 h64 (hG.rem hrem) h_v2 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
      step as ⟨e_v7, he_v7⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eInt.construct s4 e_v7 (by rw [he_v7]; exact empty_args) hinv4 h64 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
      step as ⟨e_v8, he_v8⟩
      store_step with Store.native_spec_Teq s5 e_v8 (by rw [he_v8]; rfl) h_v6 h_v7 hinv5 h64 as ⟨v8, s6, hinv6, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
      have h_ite_v11 := (show if_14_eo__24smtx_5ftypeof s6 v8 ⦃ r s' => s'.Inv ∧ s6.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_14_eo__24smtx_5ftypeof
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s6
        rcases Store.boolean_value_native h_v8 with ⟨hx_9, hbv_9⟩ | ⟨hx_9, hbv_9⟩
        · ite_branch hbv_9
          step as ⟨e_v9, he_v9⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eInt.construct s6 e_v9 (by rw [he_v9]; exact empty_args) hinv6 h64 as ⟨v9, s7, hinv7, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
          ite_done hinv7 hG with (native_ite_true_rep _ hx_9 h_v9)
        · ite_branch hbv_9
          step as ⟨e_v10, he_v10⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s6 e_v10 (by rw [he_v10]; exact empty_args) hinv6 h64 as ⟨v10, s7, hinv7, h_v10⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
          ite_done hinv7 hG with (native_ite_false_rep _ hx_9 h_v10))
      store_step with h_ite_v11 as ⟨v11, s7, hinv7, h_v11⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
      ite_done hinv7 hG with (native_ite_true_rep _ hx_6 h_v11)
    · ite_branch hbv_6
      step as ⟨e_v12, he_v12⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s3 e_v12 (by rw [he_v12]; exact empty_args) hinv3 h64 as ⟨v12, s4, hinv4, h_v12⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
      ite_done hinv4 hG with (native_ite_false_rep _ hx_6 h_v12))
  store_step with h_ite_v13 as ⟨v13, s4, hinv4, h_v13⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  case_done hinv4 hG with h_v13 in EoCases.__smtx_typeof.case_26 using

theorem case_27_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_27_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_27 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_27 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_27 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_27_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2emod.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_27
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eInt.construct s1 e_v4 (by rw [he_v4]; exact empty_args) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with Store.native_spec_Teq s2 e_v5 (by rw [he_v5]; rfl) h_v3 h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  have h_ite_v13 := (show if_17_eo__24smtx_5ftypeof s3 v5 v2 ⦃ r s' => s'.Inv ∧ s3.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_17_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s3
    rcases Store.boolean_value_native h_v5 with ⟨hx_6, hbv_6⟩ | ⟨hx_6, hbv_6⟩
    · ite_branch hbv_6
      store_step with ih.eo__24smtx_5ftypeof s3 v2 _ hinv3 h64 (hG.rem hrem) h_v2 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
      step as ⟨e_v7, he_v7⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eInt.construct s4 e_v7 (by rw [he_v7]; exact empty_args) hinv4 h64 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
      step as ⟨e_v8, he_v8⟩
      store_step with Store.native_spec_Teq s5 e_v8 (by rw [he_v8]; rfl) h_v6 h_v7 hinv5 h64 as ⟨v8, s6, hinv6, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
      have h_ite_v11 := (show if_16_eo__24smtx_5ftypeof s6 v8 ⦃ r s' => s'.Inv ∧ s6.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_16_eo__24smtx_5ftypeof
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s6
        rcases Store.boolean_value_native h_v8 with ⟨hx_9, hbv_9⟩ | ⟨hx_9, hbv_9⟩
        · ite_branch hbv_9
          step as ⟨e_v9, he_v9⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eInt.construct s6 e_v9 (by rw [he_v9]; exact empty_args) hinv6 h64 as ⟨v9, s7, hinv7, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
          ite_done hinv7 hG with (native_ite_true_rep _ hx_9 h_v9)
        · ite_branch hbv_9
          step as ⟨e_v10, he_v10⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s6 e_v10 (by rw [he_v10]; exact empty_args) hinv6 h64 as ⟨v10, s7, hinv7, h_v10⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
          ite_done hinv7 hG with (native_ite_false_rep _ hx_9 h_v10))
      store_step with h_ite_v11 as ⟨v11, s7, hinv7, h_v11⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
      ite_done hinv7 hG with (native_ite_true_rep _ hx_6 h_v11)
    · ite_branch hbv_6
      step as ⟨e_v12, he_v12⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s3 e_v12 (by rw [he_v12]; exact empty_args) hinv3 h64 as ⟨v12, s4, hinv4, h_v12⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
      ite_done hinv4 hG with (native_ite_false_rep _ hx_6 h_v12))
  store_step with h_ite_v13 as ⟨v13, s4, hinv4, h_v13⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  case_done hinv4 hG with h_v13 in EoCases.__smtx_typeof.case_27 using

theorem case_28_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_28_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_28 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_28 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_28 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_28_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2edivisible.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_28
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eInt.construct s1 e_v4 (by rw [he_v4]; exact empty_args) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with Store.native_spec_Teq s2 e_v5 (by rw [he_v5]; rfl) h_v3 h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  have h_ite_v13 := (show if_19_eo__24smtx_5ftypeof s3 v5 v2 ⦃ r s' => s'.Inv ∧ s3.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_19_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s3
    rcases Store.boolean_value_native h_v5 with ⟨hx_6, hbv_6⟩ | ⟨hx_6, hbv_6⟩
    · ite_branch hbv_6
      store_step with ih.eo__24smtx_5ftypeof s3 v2 _ hinv3 h64 (hG.rem hrem) h_v2 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
      step as ⟨e_v7, he_v7⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eInt.construct s4 e_v7 (by rw [he_v7]; exact empty_args) hinv4 h64 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
      step as ⟨e_v8, he_v8⟩
      store_step with Store.native_spec_Teq s5 e_v8 (by rw [he_v8]; rfl) h_v6 h_v7 hinv5 h64 as ⟨v8, s6, hinv6, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
      have h_ite_v11 := (show if_18_eo__24smtx_5ftypeof s6 v8 ⦃ r s' => s'.Inv ∧ s6.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_18_eo__24smtx_5ftypeof
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s6
        rcases Store.boolean_value_native h_v8 with ⟨hx_9, hbv_9⟩ | ⟨hx_9, hbv_9⟩
        · ite_branch hbv_9
          step as ⟨e_v9, he_v9⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s6 e_v9 (by rw [he_v9]; exact empty_args) hinv6 h64 as ⟨v9, s7, hinv7, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
          ite_done hinv7 hG with (native_ite_true_rep _ hx_9 h_v9)
        · ite_branch hbv_9
          step as ⟨e_v10, he_v10⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s6 e_v10 (by rw [he_v10]; exact empty_args) hinv6 h64 as ⟨v10, s7, hinv7, h_v10⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
          ite_done hinv7 hG with (native_ite_false_rep _ hx_9 h_v10))
      store_step with h_ite_v11 as ⟨v11, s7, hinv7, h_v11⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
      ite_done hinv7 hG with (native_ite_true_rep _ hx_6 h_v11)
    · ite_branch hbv_6
      step as ⟨e_v12, he_v12⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s3 e_v12 (by rw [he_v12]; exact empty_args) hinv3 h64 as ⟨v12, s4, hinv4, h_v12⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
      ite_done hinv4 hG with (native_ite_false_rep _ hx_6 h_v12))
  store_step with h_ite_v13 as ⟨v13, s4, hinv4, h_v13⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  case_done hinv4 hG with h_v13 in EoCases.__smtx_typeof.case_28 using

theorem case_29_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_29_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_29 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_29 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_29 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_29_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2eint_2epow2.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__smtx_typeof.case_29
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying h_a0 h_v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eInt.construct s1 e_v3 (by rw [he_v3]; exact empty_args) hinv1 h64 as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  step as ⟨e_v4, he_v4⟩
  store_step with Store.native_spec_Teq s2 e_v4 (by rw [he_v4]; rfl) h_v2 h_v3 hinv2 h64 as ⟨v4, s3, hinv3, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  have h_ite_v7 := (show if_20_eo__24smtx_5ftypeof s3 v4 ⦃ r s' => s'.Inv ∧ s3.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_20_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s3
    rcases Store.boolean_value_native h_v4 with ⟨hx_5, hbv_5⟩ | ⟨hx_5, hbv_5⟩
    · ite_branch hbv_5
      step as ⟨e_v5, he_v5⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eInt.construct s3 e_v5 (by rw [he_v5]; exact empty_args) hinv3 h64 as ⟨v5, s4, hinv4, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
      ite_done hinv4 hG with (native_ite_true_rep _ hx_5 h_v5)
    · ite_branch hbv_5
      step as ⟨e_v6, he_v6⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s3 e_v6 (by rw [he_v6]; exact empty_args) hinv3 h64 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
      ite_done hinv4 hG with (native_ite_false_rep _ hx_5 h_v6))
  store_step with h_ite_v7 as ⟨v7, s4, hinv4, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv4 hG with h_v7 in EoCases.__smtx_typeof.case_29 using

theorem case_30_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_30_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_30 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_30 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_30 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_30_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2eint_2elog2.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__smtx_typeof.case_30
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying h_a0 h_v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eInt.construct s1 e_v3 (by rw [he_v3]; exact empty_args) hinv1 h64 as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  step as ⟨e_v4, he_v4⟩
  store_step with Store.native_spec_Teq s2 e_v4 (by rw [he_v4]; rfl) h_v2 h_v3 hinv2 h64 as ⟨v4, s3, hinv3, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  have h_ite_v7 := (show if_21_eo__24smtx_5ftypeof s3 v4 ⦃ r s' => s'.Inv ∧ s3.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_21_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s3
    rcases Store.boolean_value_native h_v4 with ⟨hx_5, hbv_5⟩ | ⟨hx_5, hbv_5⟩
    · ite_branch hbv_5
      step as ⟨e_v5, he_v5⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eInt.construct s3 e_v5 (by rw [he_v5]; exact empty_args) hinv3 h64 as ⟨v5, s4, hinv4, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
      ite_done hinv4 hG with (native_ite_true_rep _ hx_5 h_v5)
    · ite_branch hbv_5
      step as ⟨e_v6, he_v6⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s3 e_v6 (by rw [he_v6]; exact empty_args) hinv3 h64 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
      ite_done hinv4 hG with (native_ite_false_rep _ hx_5 h_v6))
  store_step with h_ite_v7 as ⟨v7, s4, hinv4, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv4 hG with h_v7 in EoCases.__smtx_typeof.case_30 using

theorem case_31_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_31_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_31 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_31 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_31 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_31_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2ediv_5ftotal.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_31
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eInt.construct s1 e_v4 (by rw [he_v4]; exact empty_args) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with Store.native_spec_Teq s2 e_v5 (by rw [he_v5]; rfl) h_v3 h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  have h_ite_v13 := (show if_23_eo__24smtx_5ftypeof s3 v5 v2 ⦃ r s' => s'.Inv ∧ s3.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_23_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s3
    rcases Store.boolean_value_native h_v5 with ⟨hx_6, hbv_6⟩ | ⟨hx_6, hbv_6⟩
    · ite_branch hbv_6
      store_step with ih.eo__24smtx_5ftypeof s3 v2 _ hinv3 h64 (hG.rem hrem) h_v2 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
      step as ⟨e_v7, he_v7⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eInt.construct s4 e_v7 (by rw [he_v7]; exact empty_args) hinv4 h64 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
      step as ⟨e_v8, he_v8⟩
      store_step with Store.native_spec_Teq s5 e_v8 (by rw [he_v8]; rfl) h_v6 h_v7 hinv5 h64 as ⟨v8, s6, hinv6, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
      have h_ite_v11 := (show if_22_eo__24smtx_5ftypeof s6 v8 ⦃ r s' => s'.Inv ∧ s6.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_22_eo__24smtx_5ftypeof
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s6
        rcases Store.boolean_value_native h_v8 with ⟨hx_9, hbv_9⟩ | ⟨hx_9, hbv_9⟩
        · ite_branch hbv_9
          step as ⟨e_v9, he_v9⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eInt.construct s6 e_v9 (by rw [he_v9]; exact empty_args) hinv6 h64 as ⟨v9, s7, hinv7, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
          ite_done hinv7 hG with (native_ite_true_rep _ hx_9 h_v9)
        · ite_branch hbv_9
          step as ⟨e_v10, he_v10⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s6 e_v10 (by rw [he_v10]; exact empty_args) hinv6 h64 as ⟨v10, s7, hinv7, h_v10⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
          ite_done hinv7 hG with (native_ite_false_rep _ hx_9 h_v10))
      store_step with h_ite_v11 as ⟨v11, s7, hinv7, h_v11⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
      ite_done hinv7 hG with (native_ite_true_rep _ hx_6 h_v11)
    · ite_branch hbv_6
      step as ⟨e_v12, he_v12⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s3 e_v12 (by rw [he_v12]; exact empty_args) hinv3 h64 as ⟨v12, s4, hinv4, h_v12⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
      ite_done hinv4 hG with (native_ite_false_rep _ hx_6 h_v12))
  store_step with h_ite_v13 as ⟨v13, s4, hinv4, h_v13⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  case_done hinv4 hG with h_v13 in EoCases.__smtx_typeof.case_31 using

theorem case_32_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_32_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_32 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_32 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_32 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_32_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2emod_5ftotal.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_32
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eInt.construct s1 e_v4 (by rw [he_v4]; exact empty_args) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with Store.native_spec_Teq s2 e_v5 (by rw [he_v5]; rfl) h_v3 h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  have h_ite_v13 := (show if_25_eo__24smtx_5ftypeof s3 v5 v2 ⦃ r s' => s'.Inv ∧ s3.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_25_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s3
    rcases Store.boolean_value_native h_v5 with ⟨hx_6, hbv_6⟩ | ⟨hx_6, hbv_6⟩
    · ite_branch hbv_6
      store_step with ih.eo__24smtx_5ftypeof s3 v2 _ hinv3 h64 (hG.rem hrem) h_v2 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
      step as ⟨e_v7, he_v7⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eInt.construct s4 e_v7 (by rw [he_v7]; exact empty_args) hinv4 h64 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
      step as ⟨e_v8, he_v8⟩
      store_step with Store.native_spec_Teq s5 e_v8 (by rw [he_v8]; rfl) h_v6 h_v7 hinv5 h64 as ⟨v8, s6, hinv6, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
      have h_ite_v11 := (show if_24_eo__24smtx_5ftypeof s6 v8 ⦃ r s' => s'.Inv ∧ s6.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_24_eo__24smtx_5ftypeof
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s6
        rcases Store.boolean_value_native h_v8 with ⟨hx_9, hbv_9⟩ | ⟨hx_9, hbv_9⟩
        · ite_branch hbv_9
          step as ⟨e_v9, he_v9⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eInt.construct s6 e_v9 (by rw [he_v9]; exact empty_args) hinv6 h64 as ⟨v9, s7, hinv7, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
          ite_done hinv7 hG with (native_ite_true_rep _ hx_9 h_v9)
        · ite_branch hbv_9
          step as ⟨e_v10, he_v10⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s6 e_v10 (by rw [he_v10]; exact empty_args) hinv6 h64 as ⟨v10, s7, hinv7, h_v10⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
          ite_done hinv7 hG with (native_ite_false_rep _ hx_9 h_v10))
      store_step with h_ite_v11 as ⟨v11, s7, hinv7, h_v11⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
      ite_done hinv7 hG with (native_ite_true_rep _ hx_6 h_v11)
    · ite_branch hbv_6
      step as ⟨e_v12, he_v12⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s3 e_v12 (by rw [he_v12]; exact empty_args) hinv3 h64 as ⟨v12, s4, hinv4, h_v12⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
      ite_done hinv4 hG with (native_ite_false_rep _ hx_6 h_v12))
  store_step with h_ite_v13 as ⟨v13, s4, hinv4, h_v13⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  case_done hinv4 hG with h_v13 in EoCases.__smtx_typeof.case_32 using

theorem case_33_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_33_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_33 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_33 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_33 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_33_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2eselect.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_33
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24smtx_5ftypeof_5fselect s2 v3 v4 _ _ hinv2 h64 (hG.rem hrem) h_v3 h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__smtx_typeof.case_33 using

theorem case_34_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_34_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_34 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_34 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_34 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_34_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2estore.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ ⟨v3, x_v3, h_v3⟩ else hinv hG in EoCases.__smtx_typeof.case_34
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v4, s1, hinv1, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v5, s2, hinv2, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  store_step with ih.eo__24smtx_5ftypeof s2 v3 _ hinv2 h64 (hG.rem hrem) h_v3 as ⟨v6, s3, hinv3, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with ih.eo__24smtx_5ftypeof_5fstore s3 v4 v5 v6 _ _ _ hinv3 h64 (hG.rem hrem) h_v4 h_v5 h_v6 as ⟨v7, s4, hinv4, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  case_done hinv4 hG with h_v7 in EoCases.__smtx_typeof.case_34 using

theorem case_35_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_35_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_35 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_35 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_35 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_35_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2emap_5fdiff.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_35
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24smtx_5ftypeof_5fmap_5fdiff s2 v3 v4 _ _ hinv2 h64 (hG.rem hrem) h_v3 h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__smtx_typeof.case_35 using

theorem case_36_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_36_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_36 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_36 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_36 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_36_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2econcat.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_36
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24smtx_5ftypeof_5fconcat s2 v3 v4 _ _ hinv2 h64 (hG.rem hrem) h_v3 h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__smtx_typeof.case_36 using

theorem case_37_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_37_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_37 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_37 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_37 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_37_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2eextract.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ ⟨v3, x_v3, h_v3⟩ else hinv hG in EoCases.__smtx_typeof.case_37
  store_step with ih.eo__24smtx_5ftypeof s v3 _ hinv h64 hrem h_v3 as ⟨v4, s1, hinv1, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24smtx_5ftypeof_5fextract s1 v1 v2 v4 _ _ _ hinv1 h64 (hG.rem hrem) h_v1 h_v2 h_v4 as ⟨v5, s2, hinv2, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv2 hG with h_v5 in EoCases.__smtx_typeof.case_37 using

theorem case_38_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_38_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_38 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_38 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_38 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_38_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2erepeat.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_38
  store_step with ih.eo__24smtx_5ftypeof s v2 _ hinv h64 hrem h_v2 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24smtx_5ftypeof_5frepeat s1 v1 v3 _ _ hinv1 h64 (hG.rem hrem) h_v1 h_v3 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  case_done hinv2 hG with h_v4 in EoCases.__smtx_typeof.case_38 using

theorem case_39_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_39_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_39 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_39 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_39 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_39_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2ebvnot.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__smtx_typeof.case_39
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying h_a0 h_v1
  store_step with ih.eo__24smtx_5ftypeof_5fbv_5fop_5f1 s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  case_done hinv2 hG with h_v3 in EoCases.__smtx_typeof.case_39 using

theorem case_40_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_40_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_40 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_40 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_40 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_40_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2ebvand.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_40
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24smtx_5ftypeof_5fbv_5fop_5f2 s2 v3 v4 _ _ hinv2 h64 (hG.rem hrem) h_v3 h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__smtx_typeof.case_40 using

theorem case_41_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_41_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_41 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_41 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_41 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_41_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2ebvor.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_41
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24smtx_5ftypeof_5fbv_5fop_5f2 s2 v3 v4 _ _ hinv2 h64 (hG.rem hrem) h_v3 h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__smtx_typeof.case_41 using

theorem case_42_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_42_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_42 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_42 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_42 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_42_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2ebvnand.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_42
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24smtx_5ftypeof_5fbv_5fop_5f2 s2 v3 v4 _ _ hinv2 h64 (hG.rem hrem) h_v3 h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__smtx_typeof.case_42 using

theorem case_43_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_43_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_43 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_43 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_43 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_43_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2ebvnor.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_43
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24smtx_5ftypeof_5fbv_5fop_5f2 s2 v3 v4 _ _ hinv2 h64 (hG.rem hrem) h_v3 h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__smtx_typeof.case_43 using

theorem case_44_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_44_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_44 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_44 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_44 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_44_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2ebvxor.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_44
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24smtx_5ftypeof_5fbv_5fop_5f2 s2 v3 v4 _ _ hinv2 h64 (hG.rem hrem) h_v3 h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__smtx_typeof.case_44 using

theorem case_45_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_45_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_45 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_45 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_45 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_45_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2ebvxnor.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_45
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24smtx_5ftypeof_5fbv_5fop_5f2 s2 v3 v4 _ _ hinv2 h64 (hG.rem hrem) h_v3 h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__smtx_typeof.case_45 using

theorem case_46_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_46_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_46 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_46 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_46 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_46_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2ebvcomp.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_46
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with Store.native_nat_zero_spec s2 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  step as ⟨e_v6, he_v6⟩
  store_step with Store.native_spec_nat_succ s3 e_v6 (by rw [he_v6]; rfl) h_v5 hinv3 h64 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eBitVec.construct s4 e_v7 (by rw [he_v7]; rfl) h_v6 hinv4 h64 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  store_step with ih.eo__24smtx_5ftypeof_5fbv_5fop_5f2_5fret s5 v3 v4 v7 _ _ _ hinv5 h64 (hG.rem hrem) h_v3 h_v4 h_v7 as ⟨v8, s6, hinv6, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  case_done hinv6 hG with h_v8 in EoCases.__smtx_typeof.case_46 using

theorem case_47_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_47_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_47 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_47 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_47 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_47_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2ebvneg.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__smtx_typeof.case_47
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying h_a0 h_v1
  store_step with ih.eo__24smtx_5ftypeof_5fbv_5fop_5f1 s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  case_done hinv2 hG with h_v3 in EoCases.__smtx_typeof.case_47 using

theorem case_48_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_48_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_48 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_48 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_48 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_48_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2ebvadd.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_48
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24smtx_5ftypeof_5fbv_5fop_5f2 s2 v3 v4 _ _ hinv2 h64 (hG.rem hrem) h_v3 h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__smtx_typeof.case_48 using

theorem case_49_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_49_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_49 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_49 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_49 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_49_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2ebvmul.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_49
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24smtx_5ftypeof_5fbv_5fop_5f2 s2 v3 v4 _ _ hinv2 h64 (hG.rem hrem) h_v3 h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__smtx_typeof.case_49 using

theorem case_50_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_50_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_50 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_50 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_50 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_50_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2ebvudiv.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_50
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24smtx_5ftypeof_5fbv_5fop_5f2 s2 v3 v4 _ _ hinv2 h64 (hG.rem hrem) h_v3 h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__smtx_typeof.case_50 using

theorem case_51_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_51_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_51 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_51 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_51 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_51_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2ebvurem.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_51
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24smtx_5ftypeof_5fbv_5fop_5f2 s2 v3 v4 _ _ hinv2 h64 (hG.rem hrem) h_v3 h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__smtx_typeof.case_51 using

theorem case_52_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_52_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_52 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_52 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_52 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_52_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2ebvsub.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_52
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24smtx_5ftypeof_5fbv_5fop_5f2 s2 v3 v4 _ _ hinv2 h64 (hG.rem hrem) h_v3 h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__smtx_typeof.case_52 using

theorem case_53_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_53_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_53 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_53 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_53 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_53_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2ebvsdiv.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_53
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24smtx_5ftypeof_5fbv_5fop_5f2 s2 v3 v4 _ _ hinv2 h64 (hG.rem hrem) h_v3 h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__smtx_typeof.case_53 using

theorem case_54_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_54_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_54 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_54 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_54 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_54_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2ebvsrem.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_54
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24smtx_5ftypeof_5fbv_5fop_5f2 s2 v3 v4 _ _ hinv2 h64 (hG.rem hrem) h_v3 h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__smtx_typeof.case_54 using

theorem case_55_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_55_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_55 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_55 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_55 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_55_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2ebvsmod.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_55
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24smtx_5ftypeof_5fbv_5fop_5f2 s2 v3 v4 _ _ hinv2 h64 (hG.rem hrem) h_v3 h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__smtx_typeof.case_55 using

theorem case_56_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_56_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_56 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_56 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_56 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_56_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2ebvult.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_56
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s2 e_v5 (by rw [he_v5]; exact empty_args) hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  store_step with ih.eo__24smtx_5ftypeof_5fbv_5fop_5f2_5fret s3 v3 v4 v5 _ _ _ hinv3 h64 (hG.rem hrem) h_v3 h_v4 h_v5 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  case_done hinv4 hG with h_v6 in EoCases.__smtx_typeof.case_56 using

theorem case_57_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_57_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_57 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_57 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_57 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_57_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2ebvule.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_57
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s2 e_v5 (by rw [he_v5]; exact empty_args) hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  store_step with ih.eo__24smtx_5ftypeof_5fbv_5fop_5f2_5fret s3 v3 v4 v5 _ _ _ hinv3 h64 (hG.rem hrem) h_v3 h_v4 h_v5 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  case_done hinv4 hG with h_v6 in EoCases.__smtx_typeof.case_57 using

theorem case_58_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_58_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_58 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_58 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_58 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_58_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2ebvugt.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_58
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s2 e_v5 (by rw [he_v5]; exact empty_args) hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  store_step with ih.eo__24smtx_5ftypeof_5fbv_5fop_5f2_5fret s3 v3 v4 v5 _ _ _ hinv3 h64 (hG.rem hrem) h_v3 h_v4 h_v5 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  case_done hinv4 hG with h_v6 in EoCases.__smtx_typeof.case_58 using

theorem case_59_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_59_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_59 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_59 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_59 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_59_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2ebvuge.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_59
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s2 e_v5 (by rw [he_v5]; exact empty_args) hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  store_step with ih.eo__24smtx_5ftypeof_5fbv_5fop_5f2_5fret s3 v3 v4 v5 _ _ _ hinv3 h64 (hG.rem hrem) h_v3 h_v4 h_v5 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  case_done hinv4 hG with h_v6 in EoCases.__smtx_typeof.case_59 using

theorem case_60_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_60_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_60 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_60 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_60 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_60_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2ebvslt.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_60
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s2 e_v5 (by rw [he_v5]; exact empty_args) hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  store_step with ih.eo__24smtx_5ftypeof_5fbv_5fop_5f2_5fret s3 v3 v4 v5 _ _ _ hinv3 h64 (hG.rem hrem) h_v3 h_v4 h_v5 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  case_done hinv4 hG with h_v6 in EoCases.__smtx_typeof.case_60 using

theorem case_61_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_61_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_61 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_61 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_61 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_61_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2ebvsle.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_61
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s2 e_v5 (by rw [he_v5]; exact empty_args) hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  store_step with ih.eo__24smtx_5ftypeof_5fbv_5fop_5f2_5fret s3 v3 v4 v5 _ _ _ hinv3 h64 (hG.rem hrem) h_v3 h_v4 h_v5 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  case_done hinv4 hG with h_v6 in EoCases.__smtx_typeof.case_61 using

theorem case_62_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_62_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_62 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_62 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_62 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_62_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2ebvsgt.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_62
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s2 e_v5 (by rw [he_v5]; exact empty_args) hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  store_step with ih.eo__24smtx_5ftypeof_5fbv_5fop_5f2_5fret s3 v3 v4 v5 _ _ _ hinv3 h64 (hG.rem hrem) h_v3 h_v4 h_v5 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  case_done hinv4 hG with h_v6 in EoCases.__smtx_typeof.case_62 using

theorem case_63_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_63_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_63 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_63 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_63 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_63_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2ebvsge.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_63
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s2 e_v5 (by rw [he_v5]; exact empty_args) hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  store_step with ih.eo__24smtx_5ftypeof_5fbv_5fop_5f2_5fret s3 v3 v4 v5 _ _ _ hinv3 h64 (hG.rem hrem) h_v3 h_v4 h_v5 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  case_done hinv4 hG with h_v6 in EoCases.__smtx_typeof.case_63 using

theorem case_64_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_64_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_64 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_64 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_64 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_64_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2ebvshl.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_64
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24smtx_5ftypeof_5fbv_5fop_5f2 s2 v3 v4 _ _ hinv2 h64 (hG.rem hrem) h_v3 h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__smtx_typeof.case_64 using

theorem case_65_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_65_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_65 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_65 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_65 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_65_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2ebvlshr.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_65
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24smtx_5ftypeof_5fbv_5fop_5f2 s2 v3 v4 _ _ hinv2 h64 (hG.rem hrem) h_v3 h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__smtx_typeof.case_65 using

theorem case_66_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_66_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_66 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_66 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_66 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_66_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2ebvashr.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_66
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24smtx_5ftypeof_5fbv_5fop_5f2 s2 v3 v4 _ _ hinv2 h64 (hG.rem hrem) h_v3 h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__smtx_typeof.case_66 using

theorem case_67_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_67_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_67 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_67 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_67 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_67_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2ezero_5fextend.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_67
  store_step with ih.eo__24smtx_5ftypeof s v2 _ hinv h64 hrem h_v2 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24smtx_5ftypeof_5fzero_5fextend s1 v1 v3 _ _ hinv1 h64 (hG.rem hrem) h_v1 h_v3 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  case_done hinv2 hG with h_v4 in EoCases.__smtx_typeof.case_67 using

theorem case_68_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_68_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_68 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_68 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_68 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_68_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2esign_5fextend.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_68
  store_step with ih.eo__24smtx_5ftypeof s v2 _ hinv h64 hrem h_v2 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24smtx_5ftypeof_5fsign_5fextend s1 v1 v3 _ _ hinv1 h64 (hG.rem hrem) h_v1 h_v3 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  case_done hinv2 hG with h_v4 in EoCases.__smtx_typeof.case_68 using

theorem case_69_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_69_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_69 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_69 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_69 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_69_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2erotate_5fleft.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_69
  store_step with ih.eo__24smtx_5ftypeof s v2 _ hinv h64 hrem h_v2 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24smtx_5ftypeof_5frotate_5fleft s1 v1 v3 _ _ hinv1 h64 (hG.rem hrem) h_v1 h_v3 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  case_done hinv2 hG with h_v4 in EoCases.__smtx_typeof.case_69 using

theorem case_70_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_70_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_70 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_70 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_70 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_70_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2erotate_5fright.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_70
  store_step with ih.eo__24smtx_5ftypeof s v2 _ hinv h64 hrem h_v2 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24smtx_5ftypeof_5frotate_5fright s1 v1 v3 _ _ hinv1 h64 (hG.rem hrem) h_v1 h_v3 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  case_done hinv2 hG with h_v4 in EoCases.__smtx_typeof.case_70 using

theorem case_71_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_71_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_71 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_71 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_71 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_71_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2ebvuaddo.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_71
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s2 e_v5 (by rw [he_v5]; exact empty_args) hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  store_step with ih.eo__24smtx_5ftypeof_5fbv_5fop_5f2_5fret s3 v3 v4 v5 _ _ _ hinv3 h64 (hG.rem hrem) h_v3 h_v4 h_v5 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  case_done hinv4 hG with h_v6 in EoCases.__smtx_typeof.case_71 using

theorem case_72_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_72_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_72 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_72 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_72 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_72_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2ebvnego.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__smtx_typeof.case_72
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying h_a0 h_v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s1 e_v3 (by rw [he_v3]; exact empty_args) hinv1 h64 as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24smtx_5ftypeof_5fbv_5fop_5f1_5fret s2 v2 v3 _ _ hinv2 h64 (hG.rem hrem) h_v2 h_v3 as ⟨v4, s3, hinv3, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  case_done hinv3 hG with h_v4 in EoCases.__smtx_typeof.case_72 using

theorem case_73_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_73_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_73 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_73 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_73 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_73_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2ebvsaddo.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_73
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s2 e_v5 (by rw [he_v5]; exact empty_args) hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  store_step with ih.eo__24smtx_5ftypeof_5fbv_5fop_5f2_5fret s3 v3 v4 v5 _ _ _ hinv3 h64 (hG.rem hrem) h_v3 h_v4 h_v5 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  case_done hinv4 hG with h_v6 in EoCases.__smtx_typeof.case_73 using

theorem case_74_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_74_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_74 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_74 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_74 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_74_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2ebvumulo.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_74
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s2 e_v5 (by rw [he_v5]; exact empty_args) hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  store_step with ih.eo__24smtx_5ftypeof_5fbv_5fop_5f2_5fret s3 v3 v4 v5 _ _ _ hinv3 h64 (hG.rem hrem) h_v3 h_v4 h_v5 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  case_done hinv4 hG with h_v6 in EoCases.__smtx_typeof.case_74 using

theorem case_75_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_75_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_75 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_75 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_75 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_75_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2ebvsmulo.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_75
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s2 e_v5 (by rw [he_v5]; exact empty_args) hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  store_step with ih.eo__24smtx_5ftypeof_5fbv_5fop_5f2_5fret s3 v3 v4 v5 _ _ _ hinv3 h64 (hG.rem hrem) h_v3 h_v4 h_v5 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  case_done hinv4 hG with h_v6 in EoCases.__smtx_typeof.case_75 using

theorem case_76_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_76_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_76 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_76 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_76 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_76_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2ebvusubo.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_76
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s2 e_v5 (by rw [he_v5]; exact empty_args) hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  store_step with ih.eo__24smtx_5ftypeof_5fbv_5fop_5f2_5fret s3 v3 v4 v5 _ _ _ hinv3 h64 (hG.rem hrem) h_v3 h_v4 h_v5 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  case_done hinv4 hG with h_v6 in EoCases.__smtx_typeof.case_76 using

theorem case_77_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_77_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_77 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_77 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_77 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_77_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2ebvssubo.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_77
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s2 e_v5 (by rw [he_v5]; exact empty_args) hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  store_step with ih.eo__24smtx_5ftypeof_5fbv_5fop_5f2_5fret s3 v3 v4 v5 _ _ _ hinv3 h64 (hG.rem hrem) h_v3 h_v4 h_v5 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  case_done hinv4 hG with h_v6 in EoCases.__smtx_typeof.case_77 using

theorem case_78_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_78_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_78 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_78 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_78 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_78_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2ebvsdivo.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_78
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s2 e_v5 (by rw [he_v5]; exact empty_args) hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  store_step with ih.eo__24smtx_5ftypeof_5fbv_5fop_5f2_5fret s3 v3 v4 v5 _ _ _ hinv3 h64 (hG.rem hrem) h_v3 h_v4 h_v5 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  case_done hinv4 hG with h_v6 in EoCases.__smtx_typeof.case_78 using

theorem case_79_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_79_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_79 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_79 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_79 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_79_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2eseq_2eempty.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__smtx_typeof.case_79
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eSeq.construct s e_v2 (by rw [he_v2]; rfl) h_v1 hinv h64 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying h_a0 h_v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eSeq.construct s1 e_v3 (by rw [he_v3]; rfl) h_v1 hinv1 h64 as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24smtx_5ftypeof_5fguard_5fwf s2 v2 v3 _ _ hinv2 h64 (hG.rem hrem) h_v2 h_v3 as ⟨v4, s3, hinv3, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  case_done hinv3 hG with h_v4 in EoCases.__smtx_typeof.case_79 using

theorem case_80_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_80_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_80 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_80 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_80 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_80_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2estr_2elen.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__smtx_typeof.case_80
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying h_a0 h_v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eInt.construct s1 e_v3 (by rw [he_v3]; exact empty_args) hinv1 h64 as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24smtx_5ftypeof_5fseq_5fop_5f1_5fret s2 v2 v3 _ _ hinv2 h64 (hG.rem hrem) h_v2 h_v3 as ⟨v4, s3, hinv3, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  case_done hinv3 hG with h_v4 in EoCases.__smtx_typeof.case_80 using

theorem case_81_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_81_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_81 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_81 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_81 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_81_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2estr_2e_2b_2b.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_81
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24smtx_5ftypeof_5fseq_5fop_5f2 s2 v3 v4 _ _ hinv2 h64 (hG.rem hrem) h_v3 h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__smtx_typeof.case_81 using

theorem case_82_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_82_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_82 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_82 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_82 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_82_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2estr_2esubstr.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ ⟨v3, x_v3, h_v3⟩ else hinv hG in EoCases.__smtx_typeof.case_82
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v4, s1, hinv1, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v5, s2, hinv2, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  store_step with ih.eo__24smtx_5ftypeof s2 v3 _ hinv2 h64 (hG.rem hrem) h_v3 as ⟨v6, s3, hinv3, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with ih.eo__24smtx_5ftypeof_5fstr_2esubstr s3 v4 v5 v6 _ _ _ hinv3 h64 (hG.rem hrem) h_v4 h_v5 h_v6 as ⟨v7, s4, hinv4, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  case_done hinv4 hG with h_v7 in EoCases.__smtx_typeof.case_82 using

theorem case_83_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_83_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_83 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_83 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_83 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_83_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2estr_2econtains.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_83
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s2 e_v5 (by rw [he_v5]; exact empty_args) hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  store_step with ih.eo__24smtx_5ftypeof_5fseq_5fop_5f2_5fret s3 v3 v4 v5 _ _ _ hinv3 h64 (hG.rem hrem) h_v3 h_v4 h_v5 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  case_done hinv4 hG with h_v6 in EoCases.__smtx_typeof.case_83 using

theorem case_84_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_84_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_84 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_84 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_84 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_84_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2estr_2ereplace.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ ⟨v3, x_v3, h_v3⟩ else hinv hG in EoCases.__smtx_typeof.case_84
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v4, s1, hinv1, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v5, s2, hinv2, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  store_step with ih.eo__24smtx_5ftypeof s2 v3 _ hinv2 h64 (hG.rem hrem) h_v3 as ⟨v6, s3, hinv3, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with ih.eo__24smtx_5ftypeof_5fseq_5fop_5f3 s3 v4 v5 v6 _ _ _ hinv3 h64 (hG.rem hrem) h_v4 h_v5 h_v6 as ⟨v7, s4, hinv4, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  case_done hinv4 hG with h_v7 in EoCases.__smtx_typeof.case_84 using

theorem case_85_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_85_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_85 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_85 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_85 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_85_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2estr_2eindexof.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ ⟨v3, x_v3, h_v3⟩ else hinv hG in EoCases.__smtx_typeof.case_85
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v4, s1, hinv1, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v5, s2, hinv2, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  store_step with ih.eo__24smtx_5ftypeof s2 v3 _ hinv2 h64 (hG.rem hrem) h_v3 as ⟨v6, s3, hinv3, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with ih.eo__24smtx_5ftypeof_5fstr_2eindexof s3 v4 v5 v6 _ _ _ hinv3 h64 (hG.rem hrem) h_v4 h_v5 h_v6 as ⟨v7, s4, hinv4, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  case_done hinv4 hG with h_v7 in EoCases.__smtx_typeof.case_85 using

theorem case_86_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_86_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_86 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_86 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_86 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_86_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2estr_2eat.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_86
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24smtx_5ftypeof_5fstr_2eat s2 v3 v4 _ _ hinv2 h64 (hG.rem hrem) h_v3 h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__smtx_typeof.case_86 using

theorem case_87_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_87_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_87 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_87 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_87 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_87_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2estr_2eprefixof.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_87
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s2 e_v5 (by rw [he_v5]; exact empty_args) hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  store_step with ih.eo__24smtx_5ftypeof_5fseq_5fop_5f2_5fret s3 v3 v4 v5 _ _ _ hinv3 h64 (hG.rem hrem) h_v3 h_v4 h_v5 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  case_done hinv4 hG with h_v6 in EoCases.__smtx_typeof.case_87 using

theorem case_88_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_88_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_88 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_88 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_88 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_88_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2estr_2esuffixof.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_88
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s2 e_v5 (by rw [he_v5]; exact empty_args) hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  store_step with ih.eo__24smtx_5ftypeof_5fseq_5fop_5f2_5fret s3 v3 v4 v5 _ _ _ hinv3 h64 (hG.rem hrem) h_v3 h_v4 h_v5 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  case_done hinv4 hG with h_v6 in EoCases.__smtx_typeof.case_88 using

theorem case_89_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_89_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_89 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_89 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_89 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_89_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2estr_2erev.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__smtx_typeof.case_89
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying h_a0 h_v1
  store_step with ih.eo__24smtx_5ftypeof_5fseq_5fop_5f1 s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  case_done hinv2 hG with h_v3 in EoCases.__smtx_typeof.case_89 using

theorem case_90_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_90_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_90 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_90 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_90 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_90_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2estr_2eupdate.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ ⟨v3, x_v3, h_v3⟩ else hinv hG in EoCases.__smtx_typeof.case_90
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v4, s1, hinv1, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v5, s2, hinv2, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  store_step with ih.eo__24smtx_5ftypeof s2 v3 _ hinv2 h64 (hG.rem hrem) h_v3 as ⟨v6, s3, hinv3, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with ih.eo__24smtx_5ftypeof_5fstr_2eupdate s3 v4 v5 v6 _ _ _ hinv3 h64 (hG.rem hrem) h_v4 h_v5 h_v6 as ⟨v7, s4, hinv4, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  case_done hinv4 hG with h_v7 in EoCases.__smtx_typeof.case_90 using

theorem case_91_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_91_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_91 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_91 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_91 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_91_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2estr_2eto_5flower.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__smtx_typeof.case_91
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying h_a0 h_v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eChar.construct s1 e_v3 (by rw [he_v3]; exact empty_args) hinv1 h64 as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eSeq.construct s2 e_v4 (by rw [he_v4]; rfl) h_v3 hinv2 h64 as ⟨v4, s3, hinv3, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with Store.native_spec_Teq s3 e_v5 (by rw [he_v5]; rfl) h_v2 h_v4 hinv3 h64 as ⟨v5, s4, hinv4, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  have h_ite_v9 := (show if_26_eo__24smtx_5ftypeof s4 v5 ⦃ r s' => s'.Inv ∧ s4.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_26_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s4
    rcases Store.boolean_value_native h_v5 with ⟨hx_6, hbv_6⟩ | ⟨hx_6, hbv_6⟩
    · ite_branch hbv_6
      step as ⟨e_v6, he_v6⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eChar.construct s4 e_v6 (by rw [he_v6]; exact empty_args) hinv4 h64 as ⟨v6, s5, hinv5, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
      step as ⟨e_v7, he_v7⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eSeq.construct s5 e_v7 (by rw [he_v7]; rfl) h_v6 hinv5 h64 as ⟨v7, s6, hinv6, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
      ite_done hinv6 hG with (native_ite_true_rep _ hx_6 h_v7)
    · ite_branch hbv_6
      step as ⟨e_v8, he_v8⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s4 e_v8 (by rw [he_v8]; exact empty_args) hinv4 h64 as ⟨v8, s5, hinv5, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
      ite_done hinv5 hG with (native_ite_false_rep _ hx_6 h_v8))
  store_step with h_ite_v9 as ⟨v9, s5, hinv5, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  case_done hinv5 hG with h_v9 in EoCases.__smtx_typeof.case_91 using

theorem case_92_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_92_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_92 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_92 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_92 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_92_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2estr_2eto_5fupper.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__smtx_typeof.case_92
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying h_a0 h_v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eChar.construct s1 e_v3 (by rw [he_v3]; exact empty_args) hinv1 h64 as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eSeq.construct s2 e_v4 (by rw [he_v4]; rfl) h_v3 hinv2 h64 as ⟨v4, s3, hinv3, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with Store.native_spec_Teq s3 e_v5 (by rw [he_v5]; rfl) h_v2 h_v4 hinv3 h64 as ⟨v5, s4, hinv4, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  have h_ite_v9 := (show if_27_eo__24smtx_5ftypeof s4 v5 ⦃ r s' => s'.Inv ∧ s4.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_27_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s4
    rcases Store.boolean_value_native h_v5 with ⟨hx_6, hbv_6⟩ | ⟨hx_6, hbv_6⟩
    · ite_branch hbv_6
      step as ⟨e_v6, he_v6⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eChar.construct s4 e_v6 (by rw [he_v6]; exact empty_args) hinv4 h64 as ⟨v6, s5, hinv5, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
      step as ⟨e_v7, he_v7⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eSeq.construct s5 e_v7 (by rw [he_v7]; rfl) h_v6 hinv5 h64 as ⟨v7, s6, hinv6, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
      ite_done hinv6 hG with (native_ite_true_rep _ hx_6 h_v7)
    · ite_branch hbv_6
      step as ⟨e_v8, he_v8⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s4 e_v8 (by rw [he_v8]; exact empty_args) hinv4 h64 as ⟨v8, s5, hinv5, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
      ite_done hinv5 hG with (native_ite_false_rep _ hx_6 h_v8))
  store_step with h_ite_v9 as ⟨v9, s5, hinv5, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  case_done hinv5 hG with h_v9 in EoCases.__smtx_typeof.case_92 using

theorem case_93_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_93_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_93 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_93 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_93 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_93_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2estr_2eto_5fcode.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__smtx_typeof.case_93
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying h_a0 h_v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eChar.construct s1 e_v3 (by rw [he_v3]; exact empty_args) hinv1 h64 as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eSeq.construct s2 e_v4 (by rw [he_v4]; rfl) h_v3 hinv2 h64 as ⟨v4, s3, hinv3, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with Store.native_spec_Teq s3 e_v5 (by rw [he_v5]; rfl) h_v2 h_v4 hinv3 h64 as ⟨v5, s4, hinv4, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  have h_ite_v8 := (show if_28_eo__24smtx_5ftypeof s4 v5 ⦃ r s' => s'.Inv ∧ s4.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_28_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s4
    rcases Store.boolean_value_native h_v5 with ⟨hx_6, hbv_6⟩ | ⟨hx_6, hbv_6⟩
    · ite_branch hbv_6
      step as ⟨e_v6, he_v6⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eInt.construct s4 e_v6 (by rw [he_v6]; exact empty_args) hinv4 h64 as ⟨v6, s5, hinv5, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
      ite_done hinv5 hG with (native_ite_true_rep _ hx_6 h_v6)
    · ite_branch hbv_6
      step as ⟨e_v7, he_v7⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s4 e_v7 (by rw [he_v7]; exact empty_args) hinv4 h64 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
      ite_done hinv5 hG with (native_ite_false_rep _ hx_6 h_v7))
  store_step with h_ite_v8 as ⟨v8, s5, hinv5, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  case_done hinv5 hG with h_v8 in EoCases.__smtx_typeof.case_93 using

theorem case_94_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_94_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_94 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_94 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_94 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_94_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2estr_2efrom_5fcode.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__smtx_typeof.case_94
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying h_a0 h_v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eInt.construct s1 e_v3 (by rw [he_v3]; exact empty_args) hinv1 h64 as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  step as ⟨e_v4, he_v4⟩
  store_step with Store.native_spec_Teq s2 e_v4 (by rw [he_v4]; rfl) h_v2 h_v3 hinv2 h64 as ⟨v4, s3, hinv3, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  have h_ite_v8 := (show if_29_eo__24smtx_5ftypeof s3 v4 ⦃ r s' => s'.Inv ∧ s3.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_29_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s3
    rcases Store.boolean_value_native h_v4 with ⟨hx_5, hbv_5⟩ | ⟨hx_5, hbv_5⟩
    · ite_branch hbv_5
      step as ⟨e_v5, he_v5⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eChar.construct s3 e_v5 (by rw [he_v5]; exact empty_args) hinv3 h64 as ⟨v5, s4, hinv4, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
      step as ⟨e_v6, he_v6⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eSeq.construct s4 e_v6 (by rw [he_v6]; rfl) h_v5 hinv4 h64 as ⟨v6, s5, hinv5, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
      ite_done hinv5 hG with (native_ite_true_rep _ hx_5 h_v6)
    · ite_branch hbv_5
      step as ⟨e_v7, he_v7⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s3 e_v7 (by rw [he_v7]; exact empty_args) hinv3 h64 as ⟨v7, s4, hinv4, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
      ite_done hinv4 hG with (native_ite_false_rep _ hx_5 h_v7))
  store_step with h_ite_v8 as ⟨v8, s4, hinv4, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv4 hG with h_v8 in EoCases.__smtx_typeof.case_94 using

theorem case_95_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_95_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_95 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_95 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_95 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_95_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2estr_2eis_5fdigit.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__smtx_typeof.case_95
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying h_a0 h_v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eChar.construct s1 e_v3 (by rw [he_v3]; exact empty_args) hinv1 h64 as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eSeq.construct s2 e_v4 (by rw [he_v4]; rfl) h_v3 hinv2 h64 as ⟨v4, s3, hinv3, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with Store.native_spec_Teq s3 e_v5 (by rw [he_v5]; rfl) h_v2 h_v4 hinv3 h64 as ⟨v5, s4, hinv4, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  have h_ite_v8 := (show if_30_eo__24smtx_5ftypeof s4 v5 ⦃ r s' => s'.Inv ∧ s4.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_30_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s4
    rcases Store.boolean_value_native h_v5 with ⟨hx_6, hbv_6⟩ | ⟨hx_6, hbv_6⟩
    · ite_branch hbv_6
      step as ⟨e_v6, he_v6⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s4 e_v6 (by rw [he_v6]; exact empty_args) hinv4 h64 as ⟨v6, s5, hinv5, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
      ite_done hinv5 hG with (native_ite_true_rep _ hx_6 h_v6)
    · ite_branch hbv_6
      step as ⟨e_v7, he_v7⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s4 e_v7 (by rw [he_v7]; exact empty_args) hinv4 h64 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
      ite_done hinv5 hG with (native_ite_false_rep _ hx_6 h_v7))
  store_step with h_ite_v8 as ⟨v8, s5, hinv5, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  case_done hinv5 hG with h_v8 in EoCases.__smtx_typeof.case_95 using

theorem case_96_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_96_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_96 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_96 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_96 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_96_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2estr_2eto_5fint.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__smtx_typeof.case_96
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying h_a0 h_v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eChar.construct s1 e_v3 (by rw [he_v3]; exact empty_args) hinv1 h64 as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eSeq.construct s2 e_v4 (by rw [he_v4]; rfl) h_v3 hinv2 h64 as ⟨v4, s3, hinv3, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with Store.native_spec_Teq s3 e_v5 (by rw [he_v5]; rfl) h_v2 h_v4 hinv3 h64 as ⟨v5, s4, hinv4, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  have h_ite_v8 := (show if_31_eo__24smtx_5ftypeof s4 v5 ⦃ r s' => s'.Inv ∧ s4.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_31_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s4
    rcases Store.boolean_value_native h_v5 with ⟨hx_6, hbv_6⟩ | ⟨hx_6, hbv_6⟩
    · ite_branch hbv_6
      step as ⟨e_v6, he_v6⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eInt.construct s4 e_v6 (by rw [he_v6]; exact empty_args) hinv4 h64 as ⟨v6, s5, hinv5, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
      ite_done hinv5 hG with (native_ite_true_rep _ hx_6 h_v6)
    · ite_branch hbv_6
      step as ⟨e_v7, he_v7⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s4 e_v7 (by rw [he_v7]; exact empty_args) hinv4 h64 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
      ite_done hinv5 hG with (native_ite_false_rep _ hx_6 h_v7))
  store_step with h_ite_v8 as ⟨v8, s5, hinv5, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  case_done hinv5 hG with h_v8 in EoCases.__smtx_typeof.case_96 using

theorem case_97_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_97_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_97 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_97 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_97 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_97_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2estr_2efrom_5fint.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__smtx_typeof.case_97
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying h_a0 h_v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eInt.construct s1 e_v3 (by rw [he_v3]; exact empty_args) hinv1 h64 as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  step as ⟨e_v4, he_v4⟩
  store_step with Store.native_spec_Teq s2 e_v4 (by rw [he_v4]; rfl) h_v2 h_v3 hinv2 h64 as ⟨v4, s3, hinv3, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  have h_ite_v8 := (show if_32_eo__24smtx_5ftypeof s3 v4 ⦃ r s' => s'.Inv ∧ s3.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_32_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s3
    rcases Store.boolean_value_native h_v4 with ⟨hx_5, hbv_5⟩ | ⟨hx_5, hbv_5⟩
    · ite_branch hbv_5
      step as ⟨e_v5, he_v5⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eChar.construct s3 e_v5 (by rw [he_v5]; exact empty_args) hinv3 h64 as ⟨v5, s4, hinv4, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
      step as ⟨e_v6, he_v6⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eSeq.construct s4 e_v6 (by rw [he_v6]; rfl) h_v5 hinv4 h64 as ⟨v6, s5, hinv5, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
      ite_done hinv5 hG with (native_ite_true_rep _ hx_5 h_v6)
    · ite_branch hbv_5
      step as ⟨e_v7, he_v7⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s3 e_v7 (by rw [he_v7]; exact empty_args) hinv3 h64 as ⟨v7, s4, hinv4, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
      ite_done hinv4 hG with (native_ite_false_rep _ hx_5 h_v7))
  store_step with h_ite_v8 as ⟨v8, s4, hinv4, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv4 hG with h_v8 in EoCases.__smtx_typeof.case_97 using

theorem case_98_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_98_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_98 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_98 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_98 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_98_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2estr_2e_3c.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_98
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eChar.construct s1 e_v4 (by rw [he_v4]; exact empty_args) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eSeq.construct s2 e_v5 (by rw [he_v5]; rfl) h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  step as ⟨e_v6, he_v6⟩
  store_step with Store.native_spec_Teq s3 e_v6 (by rw [he_v6]; rfl) h_v3 h_v5 hinv3 h64 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  have h_ite_v15 := (show if_34_eo__24smtx_5ftypeof s4 v6 v2 ⦃ r s' => s'.Inv ∧ s4.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_34_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s4
    rcases Store.boolean_value_native h_v6 with ⟨hx_7, hbv_7⟩ | ⟨hx_7, hbv_7⟩
    · ite_branch hbv_7
      store_step with ih.eo__24smtx_5ftypeof s4 v2 _ hinv4 h64 (hG.rem hrem) h_v2 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
      step as ⟨e_v8, he_v8⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eChar.construct s5 e_v8 (by rw [he_v8]; exact empty_args) hinv5 h64 as ⟨v8, s6, hinv6, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
      step as ⟨e_v9, he_v9⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eSeq.construct s6 e_v9 (by rw [he_v9]; rfl) h_v8 hinv6 h64 as ⟨v9, s7, hinv7, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
      step as ⟨e_v10, he_v10⟩
      store_step with Store.native_spec_Teq s7 e_v10 (by rw [he_v10]; rfl) h_v7 h_v9 hinv7 h64 as ⟨v10, s8, hinv8, h_v10⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
      have h_ite_v13 := (show if_33_eo__24smtx_5ftypeof s8 v10 ⦃ r s' => s'.Inv ∧ s8.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_33_eo__24smtx_5ftypeof
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s8
        rcases Store.boolean_value_native h_v10 with ⟨hx_11, hbv_11⟩ | ⟨hx_11, hbv_11⟩
        · ite_branch hbv_11
          step as ⟨e_v11, he_v11⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s8 e_v11 (by rw [he_v11]; exact empty_args) hinv8 h64 as ⟨v11, s9, hinv9, h_v11⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
          ite_done hinv9 hG with (native_ite_true_rep _ hx_11 h_v11)
        · ite_branch hbv_11
          step as ⟨e_v12, he_v12⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s8 e_v12 (by rw [he_v12]; exact empty_args) hinv8 h64 as ⟨v12, s9, hinv9, h_v12⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
          ite_done hinv9 hG with (native_ite_false_rep _ hx_11 h_v12))
      store_step with h_ite_v13 as ⟨v13, s9, hinv9, h_v13⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
      ite_done hinv9 hG with (native_ite_true_rep _ hx_7 h_v13)
    · ite_branch hbv_7
      step as ⟨e_v14, he_v14⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s4 e_v14 (by rw [he_v14]; exact empty_args) hinv4 h64 as ⟨v14, s5, hinv5, h_v14⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
      ite_done hinv5 hG with (native_ite_false_rep _ hx_7 h_v14))
  store_step with h_ite_v15 as ⟨v15, s5, hinv5, h_v15⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  case_done hinv5 hG with h_v15 in EoCases.__smtx_typeof.case_98 using

theorem case_99_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_99_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_99 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_99 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_99 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_99_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2estr_2e_3c_3d.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_99
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eChar.construct s1 e_v4 (by rw [he_v4]; exact empty_args) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eSeq.construct s2 e_v5 (by rw [he_v5]; rfl) h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  step as ⟨e_v6, he_v6⟩
  store_step with Store.native_spec_Teq s3 e_v6 (by rw [he_v6]; rfl) h_v3 h_v5 hinv3 h64 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  have h_ite_v15 := (show if_36_eo__24smtx_5ftypeof s4 v6 v2 ⦃ r s' => s'.Inv ∧ s4.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_36_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s4
    rcases Store.boolean_value_native h_v6 with ⟨hx_7, hbv_7⟩ | ⟨hx_7, hbv_7⟩
    · ite_branch hbv_7
      store_step with ih.eo__24smtx_5ftypeof s4 v2 _ hinv4 h64 (hG.rem hrem) h_v2 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
      step as ⟨e_v8, he_v8⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eChar.construct s5 e_v8 (by rw [he_v8]; exact empty_args) hinv5 h64 as ⟨v8, s6, hinv6, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
      step as ⟨e_v9, he_v9⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eSeq.construct s6 e_v9 (by rw [he_v9]; rfl) h_v8 hinv6 h64 as ⟨v9, s7, hinv7, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
      step as ⟨e_v10, he_v10⟩
      store_step with Store.native_spec_Teq s7 e_v10 (by rw [he_v10]; rfl) h_v7 h_v9 hinv7 h64 as ⟨v10, s8, hinv8, h_v10⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
      have h_ite_v13 := (show if_35_eo__24smtx_5ftypeof s8 v10 ⦃ r s' => s'.Inv ∧ s8.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_35_eo__24smtx_5ftypeof
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s8
        rcases Store.boolean_value_native h_v10 with ⟨hx_11, hbv_11⟩ | ⟨hx_11, hbv_11⟩
        · ite_branch hbv_11
          step as ⟨e_v11, he_v11⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s8 e_v11 (by rw [he_v11]; exact empty_args) hinv8 h64 as ⟨v11, s9, hinv9, h_v11⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
          ite_done hinv9 hG with (native_ite_true_rep _ hx_11 h_v11)
        · ite_branch hbv_11
          step as ⟨e_v12, he_v12⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s8 e_v12 (by rw [he_v12]; exact empty_args) hinv8 h64 as ⟨v12, s9, hinv9, h_v12⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
          ite_done hinv9 hG with (native_ite_false_rep _ hx_11 h_v12))
      store_step with h_ite_v13 as ⟨v13, s9, hinv9, h_v13⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
      ite_done hinv9 hG with (native_ite_true_rep _ hx_7 h_v13)
    · ite_branch hbv_7
      step as ⟨e_v14, he_v14⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s4 e_v14 (by rw [he_v14]; exact empty_args) hinv4 h64 as ⟨v14, s5, hinv5, h_v14⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
      ite_done hinv5 hG with (native_ite_false_rep _ hx_7 h_v14))
  store_step with h_ite_v15 as ⟨v15, s5, hinv5, h_v15⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  case_done hinv5 hG with h_v15 in EoCases.__smtx_typeof.case_99 using

theorem case_100_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_100_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_100 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_100 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_100 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_100_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2estr_2ereplace_5fall.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ ⟨v3, x_v3, h_v3⟩ else hinv hG in EoCases.__smtx_typeof.case_100
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v4, s1, hinv1, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v5, s2, hinv2, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  store_step with ih.eo__24smtx_5ftypeof s2 v3 _ hinv2 h64 (hG.rem hrem) h_v3 as ⟨v6, s3, hinv3, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with ih.eo__24smtx_5ftypeof_5fseq_5fop_5f3 s3 v4 v5 v6 _ _ _ hinv3 h64 (hG.rem hrem) h_v4 h_v5 h_v6 as ⟨v7, s4, hinv4, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  case_done hinv4 hG with h_v7 in EoCases.__smtx_typeof.case_100 using

theorem case_101_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_101_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_101 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_101 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_101 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_101_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2estr_2ereplace_5fre.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ ⟨v3, x_v3, h_v3⟩ else hinv hG in EoCases.__smtx_typeof.case_101
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v4, s1, hinv1, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eChar.construct s1 e_v5 (by rw [he_v5]; exact empty_args) hinv1 h64 as ⟨v5, s2, hinv2, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eSeq.construct s2 e_v6 (by rw [he_v6]; rfl) h_v5 hinv2 h64 as ⟨v6, s3, hinv3, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  step as ⟨e_v7, he_v7⟩
  store_step with Store.native_spec_Teq s3 e_v7 (by rw [he_v7]; rfl) h_v4 h_v6 hinv3 h64 as ⟨v7, s4, hinv4, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  have h_ite_v22 := (show if_39_eo__24smtx_5ftypeof s4 v7 v2 v3 ⦃ r s' => s'.Inv ∧ s4.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_39_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s4
    rcases Store.boolean_value_native h_v7 with ⟨hx_8, hbv_8⟩ | ⟨hx_8, hbv_8⟩
    · ite_branch hbv_8
      store_step with ih.eo__24smtx_5ftypeof s4 v2 _ hinv4 h64 (hG.rem hrem) h_v2 as ⟨v8, s5, hinv5, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
      step as ⟨e_v9, he_v9⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eRegLan.construct s5 e_v9 (by rw [he_v9]; exact empty_args) hinv5 h64 as ⟨v9, s6, hinv6, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
      step as ⟨e_v10, he_v10⟩
      store_step with Store.native_spec_Teq s6 e_v10 (by rw [he_v10]; rfl) h_v8 h_v9 hinv6 h64 as ⟨v10, s7, hinv7, h_v10⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
      have h_ite_v20 := (show if_38_eo__24smtx_5ftypeof s7 v10 v3 ⦃ r s' => s'.Inv ∧ s7.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_38_eo__24smtx_5ftypeof
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s7
        rcases Store.boolean_value_native h_v10 with ⟨hx_11, hbv_11⟩ | ⟨hx_11, hbv_11⟩
        · ite_branch hbv_11
          store_step with ih.eo__24smtx_5ftypeof s7 v3 _ hinv7 h64 (hG.rem hrem) h_v3 as ⟨v11, s8, hinv8, h_v11⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
          step as ⟨e_v12, he_v12⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eChar.construct s8 e_v12 (by rw [he_v12]; exact empty_args) hinv8 h64 as ⟨v12, s9, hinv9, h_v12⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11
          step as ⟨e_v13, he_v13⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eSeq.construct s9 e_v13 (by rw [he_v13]; rfl) h_v12 hinv9 h64 as ⟨v13, s10, hinv10, h_v13⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
          step as ⟨e_v14, he_v14⟩
          store_step with Store.native_spec_Teq s10 e_v14 (by rw [he_v14]; rfl) h_v11 h_v13 hinv10 h64 as ⟨v14, s11, hinv11, h_v14⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13
          have h_ite_v18 := (show if_37_eo__24smtx_5ftypeof s11 v14 ⦃ r s' => s'.Inv ∧ s11.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
            unfold if_37_eo__24smtx_5ftypeof
            have hrem := (hG.rem hrem)
            have hG := Store.Grows.refl s11
            rcases Store.boolean_value_native h_v14 with ⟨hx_15, hbv_15⟩ | ⟨hx_15, hbv_15⟩
            · ite_branch hbv_15
              step as ⟨e_v15, he_v15⟩
              store_step with CtorSpec.eo__24emb_5ftsm_2eChar.construct s11 e_v15 (by rw [he_v15]; exact empty_args) hinv11 h64 as ⟨v15, s12, hinv12, h_v15⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14
              step as ⟨e_v16, he_v16⟩
              store_step with CtorSpec.eo__24emb_5ftsm_2eSeq.construct s12 e_v16 (by rw [he_v16]; rfl) h_v15 hinv12 h64 as ⟨v16, s13, hinv13, h_v16⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15
              ite_done hinv13 hG with (native_ite_true_rep _ hx_15 h_v16)
            · ite_branch hbv_15
              step as ⟨e_v17, he_v17⟩
              store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s11 e_v17 (by rw [he_v17]; exact empty_args) hinv11 h64 as ⟨v17, s12, hinv12, h_v17⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14
              ite_done hinv12 hG with (native_ite_false_rep _ hx_15 h_v17))
          store_step with h_ite_v18 as ⟨v18, s12, hinv12, h_v18⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14
          ite_done hinv12 hG with (native_ite_true_rep _ hx_11 h_v18)
        · ite_branch hbv_11
          step as ⟨e_v19, he_v19⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s7 e_v19 (by rw [he_v19]; exact empty_args) hinv7 h64 as ⟨v19, s8, hinv8, h_v19⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
          ite_done hinv8 hG with (native_ite_false_rep _ hx_11 h_v19))
      store_step with h_ite_v20 as ⟨v20, s8, hinv8, h_v20⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
      ite_done hinv8 hG with (native_ite_true_rep _ hx_8 h_v20)
    · ite_branch hbv_8
      step as ⟨e_v21, he_v21⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s4 e_v21 (by rw [he_v21]; exact empty_args) hinv4 h64 as ⟨v21, s5, hinv5, h_v21⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
      ite_done hinv5 hG with (native_ite_false_rep _ hx_8 h_v21))
  store_step with h_ite_v22 as ⟨v22, s5, hinv5, h_v22⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  case_done hinv5 hG with h_v22 in EoCases.__smtx_typeof.case_101 using

theorem case_102_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_102_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_102 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_102 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_102 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_102_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2estr_2ereplace_5fre_5fall.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ ⟨v3, x_v3, h_v3⟩ else hinv hG in EoCases.__smtx_typeof.case_102
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v4, s1, hinv1, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eChar.construct s1 e_v5 (by rw [he_v5]; exact empty_args) hinv1 h64 as ⟨v5, s2, hinv2, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eSeq.construct s2 e_v6 (by rw [he_v6]; rfl) h_v5 hinv2 h64 as ⟨v6, s3, hinv3, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  step as ⟨e_v7, he_v7⟩
  store_step with Store.native_spec_Teq s3 e_v7 (by rw [he_v7]; rfl) h_v4 h_v6 hinv3 h64 as ⟨v7, s4, hinv4, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  have h_ite_v22 := (show if_42_eo__24smtx_5ftypeof s4 v7 v2 v3 ⦃ r s' => s'.Inv ∧ s4.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_42_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s4
    rcases Store.boolean_value_native h_v7 with ⟨hx_8, hbv_8⟩ | ⟨hx_8, hbv_8⟩
    · ite_branch hbv_8
      store_step with ih.eo__24smtx_5ftypeof s4 v2 _ hinv4 h64 (hG.rem hrem) h_v2 as ⟨v8, s5, hinv5, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
      step as ⟨e_v9, he_v9⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eRegLan.construct s5 e_v9 (by rw [he_v9]; exact empty_args) hinv5 h64 as ⟨v9, s6, hinv6, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
      step as ⟨e_v10, he_v10⟩
      store_step with Store.native_spec_Teq s6 e_v10 (by rw [he_v10]; rfl) h_v8 h_v9 hinv6 h64 as ⟨v10, s7, hinv7, h_v10⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
      have h_ite_v20 := (show if_41_eo__24smtx_5ftypeof s7 v10 v3 ⦃ r s' => s'.Inv ∧ s7.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_41_eo__24smtx_5ftypeof
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s7
        rcases Store.boolean_value_native h_v10 with ⟨hx_11, hbv_11⟩ | ⟨hx_11, hbv_11⟩
        · ite_branch hbv_11
          store_step with ih.eo__24smtx_5ftypeof s7 v3 _ hinv7 h64 (hG.rem hrem) h_v3 as ⟨v11, s8, hinv8, h_v11⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
          step as ⟨e_v12, he_v12⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eChar.construct s8 e_v12 (by rw [he_v12]; exact empty_args) hinv8 h64 as ⟨v12, s9, hinv9, h_v12⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11
          step as ⟨e_v13, he_v13⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eSeq.construct s9 e_v13 (by rw [he_v13]; rfl) h_v12 hinv9 h64 as ⟨v13, s10, hinv10, h_v13⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
          step as ⟨e_v14, he_v14⟩
          store_step with Store.native_spec_Teq s10 e_v14 (by rw [he_v14]; rfl) h_v11 h_v13 hinv10 h64 as ⟨v14, s11, hinv11, h_v14⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13
          have h_ite_v18 := (show if_40_eo__24smtx_5ftypeof s11 v14 ⦃ r s' => s'.Inv ∧ s11.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
            unfold if_40_eo__24smtx_5ftypeof
            have hrem := (hG.rem hrem)
            have hG := Store.Grows.refl s11
            rcases Store.boolean_value_native h_v14 with ⟨hx_15, hbv_15⟩ | ⟨hx_15, hbv_15⟩
            · ite_branch hbv_15
              step as ⟨e_v15, he_v15⟩
              store_step with CtorSpec.eo__24emb_5ftsm_2eChar.construct s11 e_v15 (by rw [he_v15]; exact empty_args) hinv11 h64 as ⟨v15, s12, hinv12, h_v15⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14
              step as ⟨e_v16, he_v16⟩
              store_step with CtorSpec.eo__24emb_5ftsm_2eSeq.construct s12 e_v16 (by rw [he_v16]; rfl) h_v15 hinv12 h64 as ⟨v16, s13, hinv13, h_v16⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15
              ite_done hinv13 hG with (native_ite_true_rep _ hx_15 h_v16)
            · ite_branch hbv_15
              step as ⟨e_v17, he_v17⟩
              store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s11 e_v17 (by rw [he_v17]; exact empty_args) hinv11 h64 as ⟨v17, s12, hinv12, h_v17⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14
              ite_done hinv12 hG with (native_ite_false_rep _ hx_15 h_v17))
          store_step with h_ite_v18 as ⟨v18, s12, hinv12, h_v18⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14
          ite_done hinv12 hG with (native_ite_true_rep _ hx_11 h_v18)
        · ite_branch hbv_11
          step as ⟨e_v19, he_v19⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s7 e_v19 (by rw [he_v19]; exact empty_args) hinv7 h64 as ⟨v19, s8, hinv8, h_v19⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
          ite_done hinv8 hG with (native_ite_false_rep _ hx_11 h_v19))
      store_step with h_ite_v20 as ⟨v20, s8, hinv8, h_v20⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
      ite_done hinv8 hG with (native_ite_true_rep _ hx_8 h_v20)
    · ite_branch hbv_8
      step as ⟨e_v21, he_v21⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s4 e_v21 (by rw [he_v21]; exact empty_args) hinv4 h64 as ⟨v21, s5, hinv5, h_v21⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
      ite_done hinv5 hG with (native_ite_false_rep _ hx_8 h_v21))
  store_step with h_ite_v22 as ⟨v22, s5, hinv5, h_v22⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  case_done hinv5 hG with h_v22 in EoCases.__smtx_typeof.case_102 using

theorem case_103_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_103_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_103 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_103 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_103 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_103_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2estr_2eindexof_5fre.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ ⟨v3, x_v3, h_v3⟩ else hinv hG in EoCases.__smtx_typeof.case_103
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v4, s1, hinv1, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eChar.construct s1 e_v5 (by rw [he_v5]; exact empty_args) hinv1 h64 as ⟨v5, s2, hinv2, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eSeq.construct s2 e_v6 (by rw [he_v6]; rfl) h_v5 hinv2 h64 as ⟨v6, s3, hinv3, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  step as ⟨e_v7, he_v7⟩
  store_step with Store.native_spec_Teq s3 e_v7 (by rw [he_v7]; rfl) h_v4 h_v6 hinv3 h64 as ⟨v7, s4, hinv4, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  have h_ite_v20 := (show if_45_eo__24smtx_5ftypeof s4 v7 v2 v3 ⦃ r s' => s'.Inv ∧ s4.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_45_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s4
    rcases Store.boolean_value_native h_v7 with ⟨hx_8, hbv_8⟩ | ⟨hx_8, hbv_8⟩
    · ite_branch hbv_8
      store_step with ih.eo__24smtx_5ftypeof s4 v2 _ hinv4 h64 (hG.rem hrem) h_v2 as ⟨v8, s5, hinv5, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
      step as ⟨e_v9, he_v9⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eRegLan.construct s5 e_v9 (by rw [he_v9]; exact empty_args) hinv5 h64 as ⟨v9, s6, hinv6, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
      step as ⟨e_v10, he_v10⟩
      store_step with Store.native_spec_Teq s6 e_v10 (by rw [he_v10]; rfl) h_v8 h_v9 hinv6 h64 as ⟨v10, s7, hinv7, h_v10⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
      have h_ite_v18 := (show if_44_eo__24smtx_5ftypeof s7 v10 v3 ⦃ r s' => s'.Inv ∧ s7.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_44_eo__24smtx_5ftypeof
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s7
        rcases Store.boolean_value_native h_v10 with ⟨hx_11, hbv_11⟩ | ⟨hx_11, hbv_11⟩
        · ite_branch hbv_11
          store_step with ih.eo__24smtx_5ftypeof s7 v3 _ hinv7 h64 (hG.rem hrem) h_v3 as ⟨v11, s8, hinv8, h_v11⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
          step as ⟨e_v12, he_v12⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eInt.construct s8 e_v12 (by rw [he_v12]; exact empty_args) hinv8 h64 as ⟨v12, s9, hinv9, h_v12⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11
          step as ⟨e_v13, he_v13⟩
          store_step with Store.native_spec_Teq s9 e_v13 (by rw [he_v13]; rfl) h_v11 h_v12 hinv9 h64 as ⟨v13, s10, hinv10, h_v13⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
          have h_ite_v16 := (show if_43_eo__24smtx_5ftypeof s10 v13 ⦃ r s' => s'.Inv ∧ s10.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
            unfold if_43_eo__24smtx_5ftypeof
            have hrem := (hG.rem hrem)
            have hG := Store.Grows.refl s10
            rcases Store.boolean_value_native h_v13 with ⟨hx_14, hbv_14⟩ | ⟨hx_14, hbv_14⟩
            · ite_branch hbv_14
              step as ⟨e_v14, he_v14⟩
              store_step with CtorSpec.eo__24emb_5ftsm_2eInt.construct s10 e_v14 (by rw [he_v14]; exact empty_args) hinv10 h64 as ⟨v14, s11, hinv11, h_v14⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13
              ite_done hinv11 hG with (native_ite_true_rep _ hx_14 h_v14)
            · ite_branch hbv_14
              step as ⟨e_v15, he_v15⟩
              store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s10 e_v15 (by rw [he_v15]; exact empty_args) hinv10 h64 as ⟨v15, s11, hinv11, h_v15⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13
              ite_done hinv11 hG with (native_ite_false_rep _ hx_14 h_v15))
          store_step with h_ite_v16 as ⟨v16, s11, hinv11, h_v16⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13
          ite_done hinv11 hG with (native_ite_true_rep _ hx_11 h_v16)
        · ite_branch hbv_11
          step as ⟨e_v17, he_v17⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s7 e_v17 (by rw [he_v17]; exact empty_args) hinv7 h64 as ⟨v17, s8, hinv8, h_v17⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
          ite_done hinv8 hG with (native_ite_false_rep _ hx_11 h_v17))
      store_step with h_ite_v18 as ⟨v18, s8, hinv8, h_v18⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
      ite_done hinv8 hG with (native_ite_true_rep _ hx_8 h_v18)
    · ite_branch hbv_8
      step as ⟨e_v19, he_v19⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s4 e_v19 (by rw [he_v19]; exact empty_args) hinv4 h64 as ⟨v19, s5, hinv5, h_v19⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
      ite_done hinv5 hG with (native_ite_false_rep _ hx_8 h_v19))
  store_step with h_ite_v20 as ⟨v20, s5, hinv5, h_v20⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  case_done hinv5 hG with h_v20 in EoCases.__smtx_typeof.case_103 using

theorem case_104_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_104_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_104 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_104 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_104 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_104_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fsm_2ere_2eallchar.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__smtx_typeof.case_104
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eRegLan.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__smtx_typeof.case_104 using

theorem case_105_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_105_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_105 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_105 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_105 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_105_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fsm_2ere_2enone.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__smtx_typeof.case_105
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eRegLan.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__smtx_typeof.case_105 using

theorem case_106_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_106_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_106 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_106 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_106 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_106_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fsm_2ere_2eall.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__smtx_typeof.case_106
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eRegLan.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__smtx_typeof.case_106 using

theorem case_107_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_107_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_107 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_107 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_107 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_107_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2estr_2eto_5fre.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__smtx_typeof.case_107
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying h_a0 h_v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eChar.construct s1 e_v3 (by rw [he_v3]; exact empty_args) hinv1 h64 as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eSeq.construct s2 e_v4 (by rw [he_v4]; rfl) h_v3 hinv2 h64 as ⟨v4, s3, hinv3, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with Store.native_spec_Teq s3 e_v5 (by rw [he_v5]; rfl) h_v2 h_v4 hinv3 h64 as ⟨v5, s4, hinv4, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  have h_ite_v8 := (show if_46_eo__24smtx_5ftypeof s4 v5 ⦃ r s' => s'.Inv ∧ s4.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_46_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s4
    rcases Store.boolean_value_native h_v5 with ⟨hx_6, hbv_6⟩ | ⟨hx_6, hbv_6⟩
    · ite_branch hbv_6
      step as ⟨e_v6, he_v6⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eRegLan.construct s4 e_v6 (by rw [he_v6]; exact empty_args) hinv4 h64 as ⟨v6, s5, hinv5, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
      ite_done hinv5 hG with (native_ite_true_rep _ hx_6 h_v6)
    · ite_branch hbv_6
      step as ⟨e_v7, he_v7⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s4 e_v7 (by rw [he_v7]; exact empty_args) hinv4 h64 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
      ite_done hinv5 hG with (native_ite_false_rep _ hx_6 h_v7))
  store_step with h_ite_v8 as ⟨v8, s5, hinv5, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  case_done hinv5 hG with h_v8 in EoCases.__smtx_typeof.case_107 using

theorem case_108_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_108_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_108 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_108 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_108 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_108_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2ere_2e_2a.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__smtx_typeof.case_108
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying h_a0 h_v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eRegLan.construct s1 e_v3 (by rw [he_v3]; exact empty_args) hinv1 h64 as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  step as ⟨e_v4, he_v4⟩
  store_step with Store.native_spec_Teq s2 e_v4 (by rw [he_v4]; rfl) h_v2 h_v3 hinv2 h64 as ⟨v4, s3, hinv3, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  have h_ite_v7 := (show if_47_eo__24smtx_5ftypeof s3 v4 ⦃ r s' => s'.Inv ∧ s3.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_47_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s3
    rcases Store.boolean_value_native h_v4 with ⟨hx_5, hbv_5⟩ | ⟨hx_5, hbv_5⟩
    · ite_branch hbv_5
      step as ⟨e_v5, he_v5⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eRegLan.construct s3 e_v5 (by rw [he_v5]; exact empty_args) hinv3 h64 as ⟨v5, s4, hinv4, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
      ite_done hinv4 hG with (native_ite_true_rep _ hx_5 h_v5)
    · ite_branch hbv_5
      step as ⟨e_v6, he_v6⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s3 e_v6 (by rw [he_v6]; exact empty_args) hinv3 h64 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
      ite_done hinv4 hG with (native_ite_false_rep _ hx_5 h_v6))
  store_step with h_ite_v7 as ⟨v7, s4, hinv4, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv4 hG with h_v7 in EoCases.__smtx_typeof.case_108 using

theorem case_109_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_109_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_109 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_109 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_109 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_109_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2ere_2e_2b.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__smtx_typeof.case_109
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying h_a0 h_v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eRegLan.construct s1 e_v3 (by rw [he_v3]; exact empty_args) hinv1 h64 as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  step as ⟨e_v4, he_v4⟩
  store_step with Store.native_spec_Teq s2 e_v4 (by rw [he_v4]; rfl) h_v2 h_v3 hinv2 h64 as ⟨v4, s3, hinv3, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  have h_ite_v7 := (show if_48_eo__24smtx_5ftypeof s3 v4 ⦃ r s' => s'.Inv ∧ s3.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_48_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s3
    rcases Store.boolean_value_native h_v4 with ⟨hx_5, hbv_5⟩ | ⟨hx_5, hbv_5⟩
    · ite_branch hbv_5
      step as ⟨e_v5, he_v5⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eRegLan.construct s3 e_v5 (by rw [he_v5]; exact empty_args) hinv3 h64 as ⟨v5, s4, hinv4, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
      ite_done hinv4 hG with (native_ite_true_rep _ hx_5 h_v5)
    · ite_branch hbv_5
      step as ⟨e_v6, he_v6⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s3 e_v6 (by rw [he_v6]; exact empty_args) hinv3 h64 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
      ite_done hinv4 hG with (native_ite_false_rep _ hx_5 h_v6))
  store_step with h_ite_v7 as ⟨v7, s4, hinv4, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv4 hG with h_v7 in EoCases.__smtx_typeof.case_109 using

theorem case_110_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_110_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_110 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_110 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_110 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_110_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2ere_2e_5e.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_110
  store_step with ih.eo__24smtx_5ftypeof s v2 _ hinv h64 hrem h_v2 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24smtx_5ftypeof_5fre_2e_5e s1 v1 v3 _ _ hinv1 h64 (hG.rem hrem) h_v1 h_v3 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  case_done hinv2 hG with h_v4 in EoCases.__smtx_typeof.case_110 using

theorem case_111_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_111_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_111 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_111 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_111 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_111_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2ere_2eopt.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__smtx_typeof.case_111
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying h_a0 h_v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eRegLan.construct s1 e_v3 (by rw [he_v3]; exact empty_args) hinv1 h64 as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  step as ⟨e_v4, he_v4⟩
  store_step with Store.native_spec_Teq s2 e_v4 (by rw [he_v4]; rfl) h_v2 h_v3 hinv2 h64 as ⟨v4, s3, hinv3, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  have h_ite_v7 := (show if_49_eo__24smtx_5ftypeof s3 v4 ⦃ r s' => s'.Inv ∧ s3.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_49_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s3
    rcases Store.boolean_value_native h_v4 with ⟨hx_5, hbv_5⟩ | ⟨hx_5, hbv_5⟩
    · ite_branch hbv_5
      step as ⟨e_v5, he_v5⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eRegLan.construct s3 e_v5 (by rw [he_v5]; exact empty_args) hinv3 h64 as ⟨v5, s4, hinv4, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
      ite_done hinv4 hG with (native_ite_true_rep _ hx_5 h_v5)
    · ite_branch hbv_5
      step as ⟨e_v6, he_v6⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s3 e_v6 (by rw [he_v6]; exact empty_args) hinv3 h64 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
      ite_done hinv4 hG with (native_ite_false_rep _ hx_5 h_v6))
  store_step with h_ite_v7 as ⟨v7, s4, hinv4, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv4 hG with h_v7 in EoCases.__smtx_typeof.case_111 using

theorem case_112_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_112_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_112 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_112 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_112 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_112_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2ere_2ecomp.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__smtx_typeof.case_112
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying h_a0 h_v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eRegLan.construct s1 e_v3 (by rw [he_v3]; exact empty_args) hinv1 h64 as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  step as ⟨e_v4, he_v4⟩
  store_step with Store.native_spec_Teq s2 e_v4 (by rw [he_v4]; rfl) h_v2 h_v3 hinv2 h64 as ⟨v4, s3, hinv3, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  have h_ite_v7 := (show if_50_eo__24smtx_5ftypeof s3 v4 ⦃ r s' => s'.Inv ∧ s3.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_50_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s3
    rcases Store.boolean_value_native h_v4 with ⟨hx_5, hbv_5⟩ | ⟨hx_5, hbv_5⟩
    · ite_branch hbv_5
      step as ⟨e_v5, he_v5⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eRegLan.construct s3 e_v5 (by rw [he_v5]; exact empty_args) hinv3 h64 as ⟨v5, s4, hinv4, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
      ite_done hinv4 hG with (native_ite_true_rep _ hx_5 h_v5)
    · ite_branch hbv_5
      step as ⟨e_v6, he_v6⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s3 e_v6 (by rw [he_v6]; exact empty_args) hinv3 h64 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
      ite_done hinv4 hG with (native_ite_false_rep _ hx_5 h_v6))
  store_step with h_ite_v7 as ⟨v7, s4, hinv4, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv4 hG with h_v7 in EoCases.__smtx_typeof.case_112 using

theorem case_113_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_113_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_113 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_113 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_113 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_113_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2ere_2erange.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_113
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eChar.construct s1 e_v4 (by rw [he_v4]; exact empty_args) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eSeq.construct s2 e_v5 (by rw [he_v5]; rfl) h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  step as ⟨e_v6, he_v6⟩
  store_step with Store.native_spec_Teq s3 e_v6 (by rw [he_v6]; rfl) h_v3 h_v5 hinv3 h64 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  have h_ite_v15 := (show if_52_eo__24smtx_5ftypeof s4 v6 v2 ⦃ r s' => s'.Inv ∧ s4.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_52_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s4
    rcases Store.boolean_value_native h_v6 with ⟨hx_7, hbv_7⟩ | ⟨hx_7, hbv_7⟩
    · ite_branch hbv_7
      store_step with ih.eo__24smtx_5ftypeof s4 v2 _ hinv4 h64 (hG.rem hrem) h_v2 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
      step as ⟨e_v8, he_v8⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eChar.construct s5 e_v8 (by rw [he_v8]; exact empty_args) hinv5 h64 as ⟨v8, s6, hinv6, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
      step as ⟨e_v9, he_v9⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eSeq.construct s6 e_v9 (by rw [he_v9]; rfl) h_v8 hinv6 h64 as ⟨v9, s7, hinv7, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
      step as ⟨e_v10, he_v10⟩
      store_step with Store.native_spec_Teq s7 e_v10 (by rw [he_v10]; rfl) h_v7 h_v9 hinv7 h64 as ⟨v10, s8, hinv8, h_v10⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
      have h_ite_v13 := (show if_51_eo__24smtx_5ftypeof s8 v10 ⦃ r s' => s'.Inv ∧ s8.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_51_eo__24smtx_5ftypeof
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s8
        rcases Store.boolean_value_native h_v10 with ⟨hx_11, hbv_11⟩ | ⟨hx_11, hbv_11⟩
        · ite_branch hbv_11
          step as ⟨e_v11, he_v11⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eRegLan.construct s8 e_v11 (by rw [he_v11]; exact empty_args) hinv8 h64 as ⟨v11, s9, hinv9, h_v11⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
          ite_done hinv9 hG with (native_ite_true_rep _ hx_11 h_v11)
        · ite_branch hbv_11
          step as ⟨e_v12, he_v12⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s8 e_v12 (by rw [he_v12]; exact empty_args) hinv8 h64 as ⟨v12, s9, hinv9, h_v12⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
          ite_done hinv9 hG with (native_ite_false_rep _ hx_11 h_v12))
      store_step with h_ite_v13 as ⟨v13, s9, hinv9, h_v13⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
      ite_done hinv9 hG with (native_ite_true_rep _ hx_7 h_v13)
    · ite_branch hbv_7
      step as ⟨e_v14, he_v14⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s4 e_v14 (by rw [he_v14]; exact empty_args) hinv4 h64 as ⟨v14, s5, hinv5, h_v14⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
      ite_done hinv5 hG with (native_ite_false_rep _ hx_7 h_v14))
  store_step with h_ite_v15 as ⟨v15, s5, hinv5, h_v15⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  case_done hinv5 hG with h_v15 in EoCases.__smtx_typeof.case_113 using

theorem case_114_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_114_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_114 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_114 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_114 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_114_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2ere_2e_2b_2b.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_114
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eRegLan.construct s1 e_v4 (by rw [he_v4]; exact empty_args) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with Store.native_spec_Teq s2 e_v5 (by rw [he_v5]; rfl) h_v3 h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  have h_ite_v13 := (show if_54_eo__24smtx_5ftypeof s3 v5 v2 ⦃ r s' => s'.Inv ∧ s3.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_54_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s3
    rcases Store.boolean_value_native h_v5 with ⟨hx_6, hbv_6⟩ | ⟨hx_6, hbv_6⟩
    · ite_branch hbv_6
      store_step with ih.eo__24smtx_5ftypeof s3 v2 _ hinv3 h64 (hG.rem hrem) h_v2 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
      step as ⟨e_v7, he_v7⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eRegLan.construct s4 e_v7 (by rw [he_v7]; exact empty_args) hinv4 h64 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
      step as ⟨e_v8, he_v8⟩
      store_step with Store.native_spec_Teq s5 e_v8 (by rw [he_v8]; rfl) h_v6 h_v7 hinv5 h64 as ⟨v8, s6, hinv6, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
      have h_ite_v11 := (show if_53_eo__24smtx_5ftypeof s6 v8 ⦃ r s' => s'.Inv ∧ s6.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_53_eo__24smtx_5ftypeof
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s6
        rcases Store.boolean_value_native h_v8 with ⟨hx_9, hbv_9⟩ | ⟨hx_9, hbv_9⟩
        · ite_branch hbv_9
          step as ⟨e_v9, he_v9⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eRegLan.construct s6 e_v9 (by rw [he_v9]; exact empty_args) hinv6 h64 as ⟨v9, s7, hinv7, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
          ite_done hinv7 hG with (native_ite_true_rep _ hx_9 h_v9)
        · ite_branch hbv_9
          step as ⟨e_v10, he_v10⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s6 e_v10 (by rw [he_v10]; exact empty_args) hinv6 h64 as ⟨v10, s7, hinv7, h_v10⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
          ite_done hinv7 hG with (native_ite_false_rep _ hx_9 h_v10))
      store_step with h_ite_v11 as ⟨v11, s7, hinv7, h_v11⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
      ite_done hinv7 hG with (native_ite_true_rep _ hx_6 h_v11)
    · ite_branch hbv_6
      step as ⟨e_v12, he_v12⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s3 e_v12 (by rw [he_v12]; exact empty_args) hinv3 h64 as ⟨v12, s4, hinv4, h_v12⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
      ite_done hinv4 hG with (native_ite_false_rep _ hx_6 h_v12))
  store_step with h_ite_v13 as ⟨v13, s4, hinv4, h_v13⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  case_done hinv4 hG with h_v13 in EoCases.__smtx_typeof.case_114 using

theorem case_115_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_115_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_115 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_115 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_115 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_115_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2ere_2einter.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_115
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eRegLan.construct s1 e_v4 (by rw [he_v4]; exact empty_args) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with Store.native_spec_Teq s2 e_v5 (by rw [he_v5]; rfl) h_v3 h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  have h_ite_v13 := (show if_56_eo__24smtx_5ftypeof s3 v5 v2 ⦃ r s' => s'.Inv ∧ s3.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_56_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s3
    rcases Store.boolean_value_native h_v5 with ⟨hx_6, hbv_6⟩ | ⟨hx_6, hbv_6⟩
    · ite_branch hbv_6
      store_step with ih.eo__24smtx_5ftypeof s3 v2 _ hinv3 h64 (hG.rem hrem) h_v2 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
      step as ⟨e_v7, he_v7⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eRegLan.construct s4 e_v7 (by rw [he_v7]; exact empty_args) hinv4 h64 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
      step as ⟨e_v8, he_v8⟩
      store_step with Store.native_spec_Teq s5 e_v8 (by rw [he_v8]; rfl) h_v6 h_v7 hinv5 h64 as ⟨v8, s6, hinv6, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
      have h_ite_v11 := (show if_55_eo__24smtx_5ftypeof s6 v8 ⦃ r s' => s'.Inv ∧ s6.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_55_eo__24smtx_5ftypeof
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s6
        rcases Store.boolean_value_native h_v8 with ⟨hx_9, hbv_9⟩ | ⟨hx_9, hbv_9⟩
        · ite_branch hbv_9
          step as ⟨e_v9, he_v9⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eRegLan.construct s6 e_v9 (by rw [he_v9]; exact empty_args) hinv6 h64 as ⟨v9, s7, hinv7, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
          ite_done hinv7 hG with (native_ite_true_rep _ hx_9 h_v9)
        · ite_branch hbv_9
          step as ⟨e_v10, he_v10⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s6 e_v10 (by rw [he_v10]; exact empty_args) hinv6 h64 as ⟨v10, s7, hinv7, h_v10⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
          ite_done hinv7 hG with (native_ite_false_rep _ hx_9 h_v10))
      store_step with h_ite_v11 as ⟨v11, s7, hinv7, h_v11⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
      ite_done hinv7 hG with (native_ite_true_rep _ hx_6 h_v11)
    · ite_branch hbv_6
      step as ⟨e_v12, he_v12⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s3 e_v12 (by rw [he_v12]; exact empty_args) hinv3 h64 as ⟨v12, s4, hinv4, h_v12⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
      ite_done hinv4 hG with (native_ite_false_rep _ hx_6 h_v12))
  store_step with h_ite_v13 as ⟨v13, s4, hinv4, h_v13⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  case_done hinv4 hG with h_v13 in EoCases.__smtx_typeof.case_115 using

theorem case_116_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_116_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_116 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_116 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_116 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_116_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2ere_2eunion.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_116
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eRegLan.construct s1 e_v4 (by rw [he_v4]; exact empty_args) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with Store.native_spec_Teq s2 e_v5 (by rw [he_v5]; rfl) h_v3 h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  have h_ite_v13 := (show if_58_eo__24smtx_5ftypeof s3 v5 v2 ⦃ r s' => s'.Inv ∧ s3.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_58_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s3
    rcases Store.boolean_value_native h_v5 with ⟨hx_6, hbv_6⟩ | ⟨hx_6, hbv_6⟩
    · ite_branch hbv_6
      store_step with ih.eo__24smtx_5ftypeof s3 v2 _ hinv3 h64 (hG.rem hrem) h_v2 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
      step as ⟨e_v7, he_v7⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eRegLan.construct s4 e_v7 (by rw [he_v7]; exact empty_args) hinv4 h64 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
      step as ⟨e_v8, he_v8⟩
      store_step with Store.native_spec_Teq s5 e_v8 (by rw [he_v8]; rfl) h_v6 h_v7 hinv5 h64 as ⟨v8, s6, hinv6, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
      have h_ite_v11 := (show if_57_eo__24smtx_5ftypeof s6 v8 ⦃ r s' => s'.Inv ∧ s6.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_57_eo__24smtx_5ftypeof
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s6
        rcases Store.boolean_value_native h_v8 with ⟨hx_9, hbv_9⟩ | ⟨hx_9, hbv_9⟩
        · ite_branch hbv_9
          step as ⟨e_v9, he_v9⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eRegLan.construct s6 e_v9 (by rw [he_v9]; exact empty_args) hinv6 h64 as ⟨v9, s7, hinv7, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
          ite_done hinv7 hG with (native_ite_true_rep _ hx_9 h_v9)
        · ite_branch hbv_9
          step as ⟨e_v10, he_v10⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s6 e_v10 (by rw [he_v10]; exact empty_args) hinv6 h64 as ⟨v10, s7, hinv7, h_v10⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
          ite_done hinv7 hG with (native_ite_false_rep _ hx_9 h_v10))
      store_step with h_ite_v11 as ⟨v11, s7, hinv7, h_v11⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
      ite_done hinv7 hG with (native_ite_true_rep _ hx_6 h_v11)
    · ite_branch hbv_6
      step as ⟨e_v12, he_v12⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s3 e_v12 (by rw [he_v12]; exact empty_args) hinv3 h64 as ⟨v12, s4, hinv4, h_v12⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
      ite_done hinv4 hG with (native_ite_false_rep _ hx_6 h_v12))
  store_step with h_ite_v13 as ⟨v13, s4, hinv4, h_v13⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  case_done hinv4 hG with h_v13 in EoCases.__smtx_typeof.case_116 using

theorem case_117_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_117_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_117 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_117 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_117 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_117_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2ere_2ediff.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_117
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eRegLan.construct s1 e_v4 (by rw [he_v4]; exact empty_args) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with Store.native_spec_Teq s2 e_v5 (by rw [he_v5]; rfl) h_v3 h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  have h_ite_v13 := (show if_60_eo__24smtx_5ftypeof s3 v5 v2 ⦃ r s' => s'.Inv ∧ s3.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_60_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s3
    rcases Store.boolean_value_native h_v5 with ⟨hx_6, hbv_6⟩ | ⟨hx_6, hbv_6⟩
    · ite_branch hbv_6
      store_step with ih.eo__24smtx_5ftypeof s3 v2 _ hinv3 h64 (hG.rem hrem) h_v2 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
      step as ⟨e_v7, he_v7⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eRegLan.construct s4 e_v7 (by rw [he_v7]; exact empty_args) hinv4 h64 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
      step as ⟨e_v8, he_v8⟩
      store_step with Store.native_spec_Teq s5 e_v8 (by rw [he_v8]; rfl) h_v6 h_v7 hinv5 h64 as ⟨v8, s6, hinv6, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
      have h_ite_v11 := (show if_59_eo__24smtx_5ftypeof s6 v8 ⦃ r s' => s'.Inv ∧ s6.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_59_eo__24smtx_5ftypeof
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s6
        rcases Store.boolean_value_native h_v8 with ⟨hx_9, hbv_9⟩ | ⟨hx_9, hbv_9⟩
        · ite_branch hbv_9
          step as ⟨e_v9, he_v9⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eRegLan.construct s6 e_v9 (by rw [he_v9]; exact empty_args) hinv6 h64 as ⟨v9, s7, hinv7, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
          ite_done hinv7 hG with (native_ite_true_rep _ hx_9 h_v9)
        · ite_branch hbv_9
          step as ⟨e_v10, he_v10⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s6 e_v10 (by rw [he_v10]; exact empty_args) hinv6 h64 as ⟨v10, s7, hinv7, h_v10⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
          ite_done hinv7 hG with (native_ite_false_rep _ hx_9 h_v10))
      store_step with h_ite_v11 as ⟨v11, s7, hinv7, h_v11⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
      ite_done hinv7 hG with (native_ite_true_rep _ hx_6 h_v11)
    · ite_branch hbv_6
      step as ⟨e_v12, he_v12⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s3 e_v12 (by rw [he_v12]; exact empty_args) hinv3 h64 as ⟨v12, s4, hinv4, h_v12⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
      ite_done hinv4 hG with (native_ite_false_rep _ hx_6 h_v12))
  store_step with h_ite_v13 as ⟨v13, s4, hinv4, h_v13⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  case_done hinv4 hG with h_v13 in EoCases.__smtx_typeof.case_117 using

theorem case_118_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_118_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_118 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_118 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_118 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_118_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2ere_2eloop.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ ⟨v3, x_v3, h_v3⟩ else hinv hG in EoCases.__smtx_typeof.case_118
  store_step with ih.eo__24smtx_5ftypeof s v3 _ hinv h64 hrem h_v3 as ⟨v4, s1, hinv1, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24smtx_5ftypeof_5fre_2eloop s1 v1 v2 v4 _ _ _ hinv1 h64 (hG.rem hrem) h_v1 h_v2 h_v4 as ⟨v5, s2, hinv2, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv2 hG with h_v5 in EoCases.__smtx_typeof.case_118 using

theorem case_119_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_119_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_119 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_119 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_119 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_119_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2estr_2ein_5fre.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_119
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eChar.construct s1 e_v4 (by rw [he_v4]; exact empty_args) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eSeq.construct s2 e_v5 (by rw [he_v5]; rfl) h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  step as ⟨e_v6, he_v6⟩
  store_step with Store.native_spec_Teq s3 e_v6 (by rw [he_v6]; rfl) h_v3 h_v5 hinv3 h64 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  have h_ite_v14 := (show if_62_eo__24smtx_5ftypeof s4 v6 v2 ⦃ r s' => s'.Inv ∧ s4.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_62_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s4
    rcases Store.boolean_value_native h_v6 with ⟨hx_7, hbv_7⟩ | ⟨hx_7, hbv_7⟩
    · ite_branch hbv_7
      store_step with ih.eo__24smtx_5ftypeof s4 v2 _ hinv4 h64 (hG.rem hrem) h_v2 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
      step as ⟨e_v8, he_v8⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eRegLan.construct s5 e_v8 (by rw [he_v8]; exact empty_args) hinv5 h64 as ⟨v8, s6, hinv6, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
      step as ⟨e_v9, he_v9⟩
      store_step with Store.native_spec_Teq s6 e_v9 (by rw [he_v9]; rfl) h_v7 h_v8 hinv6 h64 as ⟨v9, s7, hinv7, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
      have h_ite_v12 := (show if_61_eo__24smtx_5ftypeof s7 v9 ⦃ r s' => s'.Inv ∧ s7.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_61_eo__24smtx_5ftypeof
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s7
        rcases Store.boolean_value_native h_v9 with ⟨hx_10, hbv_10⟩ | ⟨hx_10, hbv_10⟩
        · ite_branch hbv_10
          step as ⟨e_v10, he_v10⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s7 e_v10 (by rw [he_v10]; exact empty_args) hinv7 h64 as ⟨v10, s8, hinv8, h_v10⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
          ite_done hinv8 hG with (native_ite_true_rep _ hx_10 h_v10)
        · ite_branch hbv_10
          step as ⟨e_v11, he_v11⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s7 e_v11 (by rw [he_v11]; exact empty_args) hinv7 h64 as ⟨v11, s8, hinv8, h_v11⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
          ite_done hinv8 hG with (native_ite_false_rep _ hx_10 h_v11))
      store_step with h_ite_v12 as ⟨v12, s8, hinv8, h_v12⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
      ite_done hinv8 hG with (native_ite_true_rep _ hx_7 h_v12)
    · ite_branch hbv_7
      step as ⟨e_v13, he_v13⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s4 e_v13 (by rw [he_v13]; exact empty_args) hinv4 h64 as ⟨v13, s5, hinv5, h_v13⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
      ite_done hinv5 hG with (native_ite_false_rep _ hx_7 h_v13))
  store_step with h_ite_v14 as ⟨v14, s5, hinv5, h_v14⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  case_done hinv5 hG with h_v14 in EoCases.__smtx_typeof.case_119 using

theorem case_120_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_120_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_120 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_120 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_120 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_120_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2eseq_2eunit.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__smtx_typeof.case_120
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying h_a0 h_v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eSeq.construct s1 e_v3 (by rw [he_v3]; rfl) h_v2 hinv1 h64 as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24smtx_5ftypeof s2 v1 _ hinv2 h64 (hG.rem hrem) h_v1 as ⟨v4, s3, hinv3, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eSeq.construct s3 e_v5 (by rw [he_v5]; rfl) h_v4 hinv3 h64 as ⟨v5, s4, hinv4, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  store_step with ih.eo__24smtx_5ftypeof_5fguard_5fwf s4 v3 v5 _ _ hinv4 h64 (hG.rem hrem) h_v3 h_v5 as ⟨v6, s5, hinv5, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  case_done hinv5 hG with h_v6 in EoCases.__smtx_typeof.case_120 using

theorem case_121_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_121_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_121 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_121 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_121 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_121_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2eseq_2enth.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_121
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24smtx_5ftypeof_5fseq_2enth s2 v3 v4 _ _ hinv2 h64 (hG.rem hrem) h_v3 h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__smtx_typeof.case_121 using

theorem case_122_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_122_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_122 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_122 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_122 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_122_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2estr_2eindexof_5fre_5fsplit.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ ⟨v3, x_v3, h_v3⟩ else hinv hG in EoCases.__smtx_typeof.case_122
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v4, s1, hinv1, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eChar.construct s1 e_v5 (by rw [he_v5]; exact empty_args) hinv1 h64 as ⟨v5, s2, hinv2, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eSeq.construct s2 e_v6 (by rw [he_v6]; rfl) h_v5 hinv2 h64 as ⟨v6, s3, hinv3, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  step as ⟨e_v7, he_v7⟩
  store_step with Store.native_spec_Teq s3 e_v7 (by rw [he_v7]; rfl) h_v4 h_v6 hinv3 h64 as ⟨v7, s4, hinv4, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  have h_ite_v20 := (show if_65_eo__24smtx_5ftypeof s4 v7 v2 v3 ⦃ r s' => s'.Inv ∧ s4.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_65_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s4
    rcases Store.boolean_value_native h_v7 with ⟨hx_8, hbv_8⟩ | ⟨hx_8, hbv_8⟩
    · ite_branch hbv_8
      store_step with ih.eo__24smtx_5ftypeof s4 v2 _ hinv4 h64 (hG.rem hrem) h_v2 as ⟨v8, s5, hinv5, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
      step as ⟨e_v9, he_v9⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eRegLan.construct s5 e_v9 (by rw [he_v9]; exact empty_args) hinv5 h64 as ⟨v9, s6, hinv6, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
      step as ⟨e_v10, he_v10⟩
      store_step with Store.native_spec_Teq s6 e_v10 (by rw [he_v10]; rfl) h_v8 h_v9 hinv6 h64 as ⟨v10, s7, hinv7, h_v10⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
      have h_ite_v18 := (show if_64_eo__24smtx_5ftypeof s7 v10 v3 ⦃ r s' => s'.Inv ∧ s7.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_64_eo__24smtx_5ftypeof
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s7
        rcases Store.boolean_value_native h_v10 with ⟨hx_11, hbv_11⟩ | ⟨hx_11, hbv_11⟩
        · ite_branch hbv_11
          store_step with ih.eo__24smtx_5ftypeof s7 v3 _ hinv7 h64 (hG.rem hrem) h_v3 as ⟨v11, s8, hinv8, h_v11⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
          step as ⟨e_v12, he_v12⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eRegLan.construct s8 e_v12 (by rw [he_v12]; exact empty_args) hinv8 h64 as ⟨v12, s9, hinv9, h_v12⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11
          step as ⟨e_v13, he_v13⟩
          store_step with Store.native_spec_Teq s9 e_v13 (by rw [he_v13]; rfl) h_v11 h_v12 hinv9 h64 as ⟨v13, s10, hinv10, h_v13⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
          have h_ite_v16 := (show if_63_eo__24smtx_5ftypeof s10 v13 ⦃ r s' => s'.Inv ∧ s10.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
            unfold if_63_eo__24smtx_5ftypeof
            have hrem := (hG.rem hrem)
            have hG := Store.Grows.refl s10
            rcases Store.boolean_value_native h_v13 with ⟨hx_14, hbv_14⟩ | ⟨hx_14, hbv_14⟩
            · ite_branch hbv_14
              step as ⟨e_v14, he_v14⟩
              store_step with CtorSpec.eo__24emb_5ftsm_2eInt.construct s10 e_v14 (by rw [he_v14]; exact empty_args) hinv10 h64 as ⟨v14, s11, hinv11, h_v14⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13
              ite_done hinv11 hG with (native_ite_true_rep _ hx_14 h_v14)
            · ite_branch hbv_14
              step as ⟨e_v15, he_v15⟩
              store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s10 e_v15 (by rw [he_v15]; exact empty_args) hinv10 h64 as ⟨v15, s11, hinv11, h_v15⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13
              ite_done hinv11 hG with (native_ite_false_rep _ hx_14 h_v15))
          store_step with h_ite_v16 as ⟨v16, s11, hinv11, h_v16⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13
          ite_done hinv11 hG with (native_ite_true_rep _ hx_11 h_v16)
        · ite_branch hbv_11
          step as ⟨e_v17, he_v17⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s7 e_v17 (by rw [he_v17]; exact empty_args) hinv7 h64 as ⟨v17, s8, hinv8, h_v17⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
          ite_done hinv8 hG with (native_ite_false_rep _ hx_11 h_v17))
      store_step with h_ite_v18 as ⟨v18, s8, hinv8, h_v18⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
      ite_done hinv8 hG with (native_ite_true_rep _ hx_8 h_v18)
    · ite_branch hbv_8
      step as ⟨e_v19, he_v19⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s4 e_v19 (by rw [he_v19]; exact empty_args) hinv4 h64 as ⟨v19, s5, hinv5, h_v19⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
      ite_done hinv5 hG with (native_ite_false_rep _ hx_8 h_v19))
  store_step with h_ite_v20 as ⟨v20, s5, hinv5, h_v20⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  case_done hinv5 hG with h_v20 in EoCases.__smtx_typeof.case_122 using

theorem case_123_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_123_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_123 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_123 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_123 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_123_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2eseq_5fdiff.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_123
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24smtx_5ftypeof_5fseq_5fdiff s2 v3 v4 _ _ hinv2 h64 (hG.rem hrem) h_v3 h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__smtx_typeof.case_123 using

theorem case_124_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_124_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_124 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_124 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_124 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_124_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2e_40strings_5foccur_5findex.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ ⟨v3, x_v3, h_v3⟩ else hinv hG in EoCases.__smtx_typeof.case_124
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v4, s1, hinv1, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v5, s2, hinv2, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  store_step with ih.eo__24smtx_5ftypeof s2 v3 _ hinv2 h64 (hG.rem hrem) h_v3 as ⟨v6, s3, hinv3, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with ih.eo__24smtx_5ftypeof_5fstr_2eindexof s3 v4 v5 v6 _ _ _ hinv3 h64 (hG.rem hrem) h_v4 h_v5 h_v6 as ⟨v7, s4, hinv4, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  case_done hinv4 hG with h_v7 in EoCases.__smtx_typeof.case_124 using

theorem case_125_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_125_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_125 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_125 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_125 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_125_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2e_40strings_5foccur_5findex_5fre.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ ⟨v3, x_v3, h_v3⟩ else hinv hG in EoCases.__smtx_typeof.case_125
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v4, s1, hinv1, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eChar.construct s1 e_v5 (by rw [he_v5]; exact empty_args) hinv1 h64 as ⟨v5, s2, hinv2, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eSeq.construct s2 e_v6 (by rw [he_v6]; rfl) h_v5 hinv2 h64 as ⟨v6, s3, hinv3, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  step as ⟨e_v7, he_v7⟩
  store_step with Store.native_spec_Teq s3 e_v7 (by rw [he_v7]; rfl) h_v4 h_v6 hinv3 h64 as ⟨v7, s4, hinv4, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  have h_ite_v20 := (show if_68_eo__24smtx_5ftypeof s4 v7 v2 v3 ⦃ r s' => s'.Inv ∧ s4.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_68_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s4
    rcases Store.boolean_value_native h_v7 with ⟨hx_8, hbv_8⟩ | ⟨hx_8, hbv_8⟩
    · ite_branch hbv_8
      store_step with ih.eo__24smtx_5ftypeof s4 v2 _ hinv4 h64 (hG.rem hrem) h_v2 as ⟨v8, s5, hinv5, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
      step as ⟨e_v9, he_v9⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eRegLan.construct s5 e_v9 (by rw [he_v9]; exact empty_args) hinv5 h64 as ⟨v9, s6, hinv6, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
      step as ⟨e_v10, he_v10⟩
      store_step with Store.native_spec_Teq s6 e_v10 (by rw [he_v10]; rfl) h_v8 h_v9 hinv6 h64 as ⟨v10, s7, hinv7, h_v10⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
      have h_ite_v18 := (show if_67_eo__24smtx_5ftypeof s7 v10 v3 ⦃ r s' => s'.Inv ∧ s7.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_67_eo__24smtx_5ftypeof
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s7
        rcases Store.boolean_value_native h_v10 with ⟨hx_11, hbv_11⟩ | ⟨hx_11, hbv_11⟩
        · ite_branch hbv_11
          store_step with ih.eo__24smtx_5ftypeof s7 v3 _ hinv7 h64 (hG.rem hrem) h_v3 as ⟨v11, s8, hinv8, h_v11⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
          step as ⟨e_v12, he_v12⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eInt.construct s8 e_v12 (by rw [he_v12]; exact empty_args) hinv8 h64 as ⟨v12, s9, hinv9, h_v12⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11
          step as ⟨e_v13, he_v13⟩
          store_step with Store.native_spec_Teq s9 e_v13 (by rw [he_v13]; rfl) h_v11 h_v12 hinv9 h64 as ⟨v13, s10, hinv10, h_v13⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
          have h_ite_v16 := (show if_66_eo__24smtx_5ftypeof s10 v13 ⦃ r s' => s'.Inv ∧ s10.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
            unfold if_66_eo__24smtx_5ftypeof
            have hrem := (hG.rem hrem)
            have hG := Store.Grows.refl s10
            rcases Store.boolean_value_native h_v13 with ⟨hx_14, hbv_14⟩ | ⟨hx_14, hbv_14⟩
            · ite_branch hbv_14
              step as ⟨e_v14, he_v14⟩
              store_step with CtorSpec.eo__24emb_5ftsm_2eInt.construct s10 e_v14 (by rw [he_v14]; exact empty_args) hinv10 h64 as ⟨v14, s11, hinv11, h_v14⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13
              ite_done hinv11 hG with (native_ite_true_rep _ hx_14 h_v14)
            · ite_branch hbv_14
              step as ⟨e_v15, he_v15⟩
              store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s10 e_v15 (by rw [he_v15]; exact empty_args) hinv10 h64 as ⟨v15, s11, hinv11, h_v15⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13
              ite_done hinv11 hG with (native_ite_false_rep _ hx_14 h_v15))
          store_step with h_ite_v16 as ⟨v16, s11, hinv11, h_v16⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13
          ite_done hinv11 hG with (native_ite_true_rep _ hx_11 h_v16)
        · ite_branch hbv_11
          step as ⟨e_v17, he_v17⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s7 e_v17 (by rw [he_v17]; exact empty_args) hinv7 h64 as ⟨v17, s8, hinv8, h_v17⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
          ite_done hinv8 hG with (native_ite_false_rep _ hx_11 h_v17))
      store_step with h_ite_v18 as ⟨v18, s8, hinv8, h_v18⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
      ite_done hinv8 hG with (native_ite_true_rep _ hx_8 h_v18)
    · ite_branch hbv_8
      step as ⟨e_v19, he_v19⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s4 e_v19 (by rw [he_v19]; exact empty_args) hinv4 h64 as ⟨v19, s5, hinv5, h_v19⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
      ite_done hinv5 hG with (native_ite_false_rep _ hx_8 h_v19))
  store_step with h_ite_v20 as ⟨v20, s5, hinv5, h_v20⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  case_done hinv5 hG with h_v20 in EoCases.__smtx_typeof.case_125 using

theorem case_126_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_126_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_126 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_126 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_126 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_126_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2echoice.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ ⟨v3, x_v3, h_v3⟩ else hinv hG in EoCases.__smtx_typeof.case_126
  store_step with ih.eo__24smtx_5ftypeof s v3 _ hinv h64 hrem h_v3 as ⟨v4, s1, hinv1, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s1 e_v5 (by rw [he_v5]; exact empty_args) hinv1 h64 as ⟨v5, s2, hinv2, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  step as ⟨e_v6, he_v6⟩
  store_step with Store.native_spec_Teq s2 e_v6 (by rw [he_v6]; rfl) h_v4 h_v5 hinv2 h64 as ⟨v6, s3, hinv3, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  have h_ite_v9 := (show if_69_eo__24smtx_5ftypeof s3 v6 v2 ⦃ r s' => s'.Inv ∧ s3.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_69_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s3
    rcases Store.boolean_value_native h_v6 with ⟨hx_7, hbv_7⟩ | ⟨hx_7, hbv_7⟩
    · ite_branch hbv_7
      store_step with ih.eo__24smtx_5ftypeof_5fguard_5fwf s3 v2 v2 _ _ hinv3 h64 (hG.rem hrem) h_v2 h_v2 as ⟨v7, s4, hinv4, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
      ite_done hinv4 hG with (native_ite_true_rep _ hx_7 h_v7)
    · ite_branch hbv_7
      step as ⟨e_v8, he_v8⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s3 e_v8 (by rw [he_v8]; exact empty_args) hinv3 h64 as ⟨v8, s4, hinv4, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
      ite_done hinv4 hG with (native_ite_false_rep _ hx_7 h_v8))
  store_step with h_ite_v9 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  case_done hinv4 hG with h_v9 in EoCases.__smtx_typeof.case_126 using

theorem case_127_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_127_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_127 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_127 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_127 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_127_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2eset_2eempty.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__smtx_typeof.case_127
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eSet.construct s e_v2 (by rw [he_v2]; rfl) h_v1 hinv h64 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying h_a0 h_v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eSet.construct s1 e_v3 (by rw [he_v3]; rfl) h_v1 hinv1 h64 as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24smtx_5ftypeof_5fguard_5fwf s2 v2 v3 _ _ hinv2 h64 (hG.rem hrem) h_v2 h_v3 as ⟨v4, s3, hinv3, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  case_done hinv3 hG with h_v4 in EoCases.__smtx_typeof.case_127 using

theorem case_128_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_128_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_128 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_128 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_128 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_128_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2eset_2esingleton.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__smtx_typeof.case_128
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying h_a0 h_v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eSet.construct s1 e_v3 (by rw [he_v3]; rfl) h_v2 hinv1 h64 as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24smtx_5ftypeof s2 v1 _ hinv2 h64 (hG.rem hrem) h_v1 as ⟨v4, s3, hinv3, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eSet.construct s3 e_v5 (by rw [he_v5]; rfl) h_v4 hinv3 h64 as ⟨v5, s4, hinv4, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  store_step with ih.eo__24smtx_5ftypeof_5fguard_5fwf s4 v3 v5 _ _ hinv4 h64 (hG.rem hrem) h_v3 h_v5 as ⟨v6, s5, hinv5, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  case_done hinv5 hG with h_v6 in EoCases.__smtx_typeof.case_128 using

theorem case_129_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_129_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_129 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_129 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_129 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_129_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2eset_2eunion.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_129
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24smtx_5ftypeof_5fsets_5fop_5f2 s2 v3 v4 _ _ hinv2 h64 (hG.rem hrem) h_v3 h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__smtx_typeof.case_129 using

theorem case_130_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_130_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_130 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_130 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_130 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_130_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2eset_2einter.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_130
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24smtx_5ftypeof_5fsets_5fop_5f2 s2 v3 v4 _ _ hinv2 h64 (hG.rem hrem) h_v3 h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__smtx_typeof.case_130 using

theorem case_131_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_131_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_131 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_131 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_131 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_131_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2eset_2eminus.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_131
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24smtx_5ftypeof_5fsets_5fop_5f2 s2 v3 v4 _ _ hinv2 h64 (hG.rem hrem) h_v3 h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__smtx_typeof.case_131 using

theorem case_132_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_132_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_132 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_132 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_132 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_132_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2eset_2emember.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_132
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24smtx_5ftypeof_5fset_2emember s2 v3 v4 _ _ hinv2 h64 (hG.rem hrem) h_v3 h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__smtx_typeof.case_132 using

theorem case_133_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_133_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_133 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_133 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_133 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_133_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2eset_2esubset.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_133
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s2 e_v5 (by rw [he_v5]; exact empty_args) hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  store_step with ih.eo__24smtx_5ftypeof_5fsets_5fop_5f2_5fret s3 v3 v4 v5 _ _ _ hinv3 h64 (hG.rem hrem) h_v3 h_v4 h_v5 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  case_done hinv4 hG with h_v6 in EoCases.__smtx_typeof.case_133 using

theorem case_134_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_134_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_134 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_134 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_134 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_134_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2e_2f.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_134
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eReal.construct s2 e_v5 (by rw [he_v5]; exact empty_args) hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  store_step with ih.eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2_5fret s3 v3 v4 v5 _ _ _ hinv3 h64 (hG.rem hrem) h_v3 h_v4 h_v5 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  case_done hinv4 hG with h_v6 in EoCases.__smtx_typeof.case_134 using

theorem case_135_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_135_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_135 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_135 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_135 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_135_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2e_2f_5ftotal.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_135
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eReal.construct s2 e_v5 (by rw [he_v5]; exact empty_args) hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  store_step with ih.eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2_5fret s3 v3 v4 v5 _ _ _ hinv3 h64 (hG.rem hrem) h_v3 h_v4 h_v5 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  case_done hinv4 hG with h_v6 in EoCases.__smtx_typeof.case_135 using

theorem case_136_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_136_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_136 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_136 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_136 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_136_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2eforall.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ ⟨v3, x_v3, h_v3⟩ else hinv hG in EoCases.__smtx_typeof.case_136
  store_step with ih.eo__24smtx_5ftypeof s v3 _ hinv h64 hrem h_v3 as ⟨v4, s1, hinv1, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s1 e_v5 (by rw [he_v5]; exact empty_args) hinv1 h64 as ⟨v5, s2, hinv2, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  step as ⟨e_v6, he_v6⟩
  store_step with Store.native_spec_Teq s2 e_v6 (by rw [he_v6]; rfl) h_v4 h_v5 hinv2 h64 as ⟨v6, s3, hinv3, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  have h_ite_v10 := (show if_70_eo__24smtx_5ftypeof s3 v6 v2 ⦃ r s' => s'.Inv ∧ s3.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_70_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s3
    rcases Store.boolean_value_native h_v6 with ⟨hx_7, hbv_7⟩ | ⟨hx_7, hbv_7⟩
    · ite_branch hbv_7
      step as ⟨e_v7, he_v7⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s3 e_v7 (by rw [he_v7]; exact empty_args) hinv3 h64 as ⟨v7, s4, hinv4, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
      store_step with ih.eo__24smtx_5ftypeof_5fguard_5fwf s4 v2 v7 _ _ hinv4 h64 (hG.rem hrem) h_v2 h_v7 as ⟨v8, s5, hinv5, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
      ite_done hinv5 hG with (native_ite_true_rep _ hx_7 h_v8)
    · ite_branch hbv_7
      step as ⟨e_v9, he_v9⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s3 e_v9 (by rw [he_v9]; exact empty_args) hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
      ite_done hinv4 hG with (native_ite_false_rep _ hx_7 h_v9))
  store_step with h_ite_v10 as ⟨v10, s4, hinv4, h_v10⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  case_done hinv4 hG with h_v10 in EoCases.__smtx_typeof.case_136 using

theorem case_137_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_137_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_137 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_137 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_137 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_137_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2eexists.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ ⟨v3, x_v3, h_v3⟩ else hinv hG in EoCases.__smtx_typeof.case_137
  store_step with ih.eo__24smtx_5ftypeof s v3 _ hinv h64 hrem h_v3 as ⟨v4, s1, hinv1, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s1 e_v5 (by rw [he_v5]; exact empty_args) hinv1 h64 as ⟨v5, s2, hinv2, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  step as ⟨e_v6, he_v6⟩
  store_step with Store.native_spec_Teq s2 e_v6 (by rw [he_v6]; rfl) h_v4 h_v5 hinv2 h64 as ⟨v6, s3, hinv3, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  have h_ite_v10 := (show if_71_eo__24smtx_5ftypeof s3 v6 v2 ⦃ r s' => s'.Inv ∧ s3.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_71_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s3
    rcases Store.boolean_value_native h_v6 with ⟨hx_7, hbv_7⟩ | ⟨hx_7, hbv_7⟩
    · ite_branch hbv_7
      step as ⟨e_v7, he_v7⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s3 e_v7 (by rw [he_v7]; exact empty_args) hinv3 h64 as ⟨v7, s4, hinv4, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
      store_step with ih.eo__24smtx_5ftypeof_5fguard_5fwf s4 v2 v7 _ _ hinv4 h64 (hG.rem hrem) h_v2 h_v7 as ⟨v8, s5, hinv5, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
      ite_done hinv5 hG with (native_ite_true_rep _ hx_7 h_v8)
    · ite_branch hbv_7
      step as ⟨e_v9, he_v9⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s3 e_v9 (by rw [he_v9]; exact empty_args) hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
      ite_done hinv4 hG with (native_ite_false_rep _ hx_7 h_v9))
  store_step with h_ite_v10 as ⟨v10, s4, hinv4, h_v10⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  case_done hinv4 hG with h_v10 in EoCases.__smtx_typeof.case_137 using

theorem case_138_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_138_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_138 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_138 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_138 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_138_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2eint_5fto_5fbv.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_138
  store_step with ih.eo__24smtx_5ftypeof s v2 _ hinv h64 hrem h_v2 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24smtx_5ftypeof_5fint_5fto_5fbv s1 v1 v3 _ _ hinv1 h64 (hG.rem hrem) h_v1 h_v3 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  case_done hinv2 hG with h_v4 in EoCases.__smtx_typeof.case_138 using

theorem case_139_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_139_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_139 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_139 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_139 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_139_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2eubv_5fto_5fint.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__smtx_typeof.case_139
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying h_a0 h_v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eInt.construct s1 e_v3 (by rw [he_v3]; exact empty_args) hinv1 h64 as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24smtx_5ftypeof_5fbv_5fop_5f1_5fret s2 v2 v3 _ _ hinv2 h64 (hG.rem hrem) h_v2 h_v3 as ⟨v4, s3, hinv3, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  case_done hinv3 hG with h_v4 in EoCases.__smtx_typeof.case_139 using

theorem case_140_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_140_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_140 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_140 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_140 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_140_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2esbv_5fto_5fint.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__smtx_typeof.case_140
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying h_a0 h_v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eInt.construct s1 e_v3 (by rw [he_v3]; exact empty_args) hinv1 h64 as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24smtx_5ftypeof_5fbv_5fop_5f1_5fret s2 v2 v3 _ _ hinv2 h64 (hG.rem hrem) h_v2 h_v3 as ⟨v4, s3, hinv3, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  case_done hinv3 hG with h_v4 in EoCases.__smtx_typeof.case_140 using

theorem case_141_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_141_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_141 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_141 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_141 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_141_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2eDtCons.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ ⟨v3, x_v3, h_v3⟩ else hinv hG in EoCases.__smtx_typeof.case_141
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eDatatype.construct s e_v4 (by rw [he_v4]; rfl) h_v1 h_v2 hinv h64 as ⟨v4, s1, hinv1, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eDatatype.construct s1 e_v5 (by rw [he_v5]; rfl) h_v1 h_v2 hinv1 h64 as ⟨v5, s2, hinv2, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  store_step with ih.eo__24smtx_5fdd_5flookup s2 v1 v2 _ _ hinv2 h64 (hG.rem hrem) h_v1 h_v2 as ⟨v6, s3, hinv3, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with ih.eo__24smtx_5fdt_5fresolve s3 v6 v2 _ _ hinv3 h64 (hG.rem hrem) h_v6 h_v2 as ⟨v7, s4, hinv4, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  store_step with ih.eo__24smtx_5ftypeof_5fdt_5fcons_5frec s4 v5 v7 v3 _ _ _ hinv4 h64 (hG.rem hrem) h_v5 h_v7 h_v3 as ⟨v8, s5, hinv5, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24smtx_5ftypeof_5fguard_5fwf s5 v4 v8 _ _ hinv5 h64 (hG.rem hrem) h_v4 h_v8 as ⟨v9, s6, hinv6, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv6 hG with h_v9 in EoCases.__smtx_typeof.case_141 using

theorem case_142_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_142_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_142 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_142 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_142 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_142_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2eApply.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_142
  pat_destruct CtorSpec.eo__24emb_5fsm_2eDtSel.destruct h_v1 as ⟨v4, x_v4, h_v4⟩ ⟨v5, x_v5, h_v5⟩ ⟨v6, x_v6, h_v6⟩ ⟨v7, x_v7, h_v7⟩ else hinv hG in EoCases.__smtx_typeof.case_142
  store_step with ih.eo__24smtx_5fret_5ftypeof_5fsel s v4 v5 v6 v7 _ _ _ _ hinv h64 hrem h_v4 h_v5 h_v6 h_v7 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eDatatype.construct s1 e_v9 (by rw [he_v9]; rfl) h_v4 h_v5 hinv1 h64 as ⟨v9, s2, hinv2, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  store_step with ih.eo__24smtx_5fret_5ftypeof_5fsel s2 v4 v5 v6 v7 _ _ _ _ hinv2 h64 (hG.rem hrem) h_v4 h_v5 h_v6 h_v7 as ⟨v10, s3, hinv3, h_v10⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  step as ⟨e_v11, he_v11⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eFunType.construct s3 e_v11 (by rw [he_v11]; rfl) h_v9 h_v10 hinv3 h64 as ⟨v11, s4, hinv4, h_v11⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
  store_step with ih.eo__24smtx_5ftypeof s4 v2 _ hinv4 h64 (hG.rem hrem) h_v2 as ⟨v12, s5, hinv5, h_v12⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11
  store_step with ih.eo__24smtx_5ftypeof_5fapply s5 v11 v12 _ _ hinv5 h64 (hG.rem hrem) h_v11 h_v12 as ⟨v13, s6, hinv6, h_v13⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
  store_step with ih.eo__24smtx_5ftypeof_5fguard_5fwf s6 v8 v13 _ _ hinv6 h64 (hG.rem hrem) h_v8 h_v13 as ⟨v14, s7, hinv7, h_v14⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13
  case_done hinv7 hG with h_v14 in EoCases.__smtx_typeof.case_142 using

theorem case_143_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_143_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_143 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_143 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_143 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_143_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2eApply.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_143
  pat_destruct CtorSpec.eo__24emb_5fsm_2eDtTester.destruct h_v1 as ⟨v4, x_v4, h_v4⟩ ⟨v5, x_v5, h_v5⟩ ⟨v6, x_v6, h_v6⟩ else hinv hG in EoCases.__smtx_typeof.case_143
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eDatatype.construct s e_v7 (by rw [he_v7]; rfl) h_v4 h_v5 hinv h64 as ⟨v7, s1, hinv1, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24smtx_5fdd_5flookup s1 v4 v5 _ _ hinv1 h64 (hG.rem hrem) h_v4 h_v5 as ⟨v8, s2, hinv2, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24smtx_5fdt_5fresolve s2 v8 v5 _ _ hinv2 h64 (hG.rem hrem) h_v8 h_v5 as ⟨v9, s3, hinv3, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  store_step with ih.eo__24smtx_5ftypeof_5fdt_5fcons_5frec s3 v7 v9 v6 _ _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v9 h_v6 as ⟨v10, s4, hinv4, h_v10⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  step as ⟨e_v11, he_v11⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eDatatype.construct s4 e_v11 (by rw [he_v11]; rfl) h_v4 h_v5 hinv4 h64 as ⟨v11, s5, hinv5, h_v11⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s5 e_v12 (by rw [he_v12]; exact empty_args) hinv5 h64 as ⟨v12, s6, hinv6, h_v12⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eFunType.construct s6 e_v13 (by rw [he_v13]; rfl) h_v11 h_v12 hinv6 h64 as ⟨v13, s7, hinv7, h_v13⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
  store_step with ih.eo__24smtx_5ftypeof s7 v2 _ hinv7 h64 (hG.rem hrem) h_v2 as ⟨v14, s8, hinv8, h_v14⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13
  store_step with ih.eo__24smtx_5ftypeof_5fapply s8 v13 v14 _ _ hinv8 h64 (hG.rem hrem) h_v13 h_v14 as ⟨v15, s9, hinv9, h_v15⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14
  store_step with ih.eo__24smtx_5ftypeof_5fguard s9 v10 v15 _ _ hinv9 h64 (hG.rem hrem) h_v10 h_v15 as ⟨v16, s10, hinv10, h_v16⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15
  case_done hinv10 hG with h_v16 in EoCases.__smtx_typeof.case_143 using

theorem case_144_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_144_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_144 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_144 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_144 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_144_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2eApply.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_144
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24smtx_5ftypeof_5fapply s2 v3 v4 _ _ hinv2 h64 (hG.rem hrem) h_v3 h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__smtx_typeof.case_144 using

theorem case_145_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_145_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_145 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_145 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_145 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_145_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2eVar.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_145
  store_step with ih.eo__24smtx_5ftypeof_5fguard_5fwf s v2 v2 _ _ hinv h64 hrem h_v2 h_v2 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  case_done hinv1 hG with h_v3 in EoCases.__smtx_typeof.case_145 using

theorem case_146_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_146_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_146 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_146 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_146 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_146_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2eUConst.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof.case_146
  store_step with ih.eo__24smtx_5ftypeof_5fguard_5fwf s v2 v2 _ _ hinv h64 hrem h_v2 h_v2 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  case_done hinv1 hG with h_v3 in EoCases.__smtx_typeof.case_146 using

theorem case_147_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_147_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof.case_147 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_typeof.case_147 x_a0 = some (__smtx_typeof y0)
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_147 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_147_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  case_done hinv1 hG with h_v0 in EoCases.__smtx_typeof.case_147 using

theorem cases_0_0_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_0_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, (∀ d, firstSome [EoCases.__smtx_typeof.case_0 x_a0, EoCases.__smtx_typeof.case_1 x_a0, EoCases.__smtx_typeof.case_2 x_a0, EoCases.__smtx_typeof.case_3 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          ∀ d, firstSome [EoCases.__smtx_typeof.case_0 x_a0, EoCases.__smtx_typeof.case_1 x_a0, EoCases.__smtx_typeof.case_2 x_a0, EoCases.__smtx_typeof.case_3 x_a0] d = __smtx_typeof y0
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_0 x_a0 = none ∧ EoCases.__smtx_typeof.case_1 x_a0 = none ∧ EoCases.__smtx_typeof.case_2 x_a0 = none ∧ EoCases.__smtx_typeof.case_3 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_0_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  group_round_step with case_0_eo__24smtx_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_0 x_a0, EoCases.__smtx_typeof.case_1 x_a0, EoCases.__smtx_typeof.case_2 x_a0, EoCases.__smtx_typeof.case_3 x_a0] = [] ++ [EoCases.__smtx_typeof.case_0 x_a0] ++ [EoCases.__smtx_typeof.case_1 x_a0, EoCases.__smtx_typeof.case_2 x_a0, EoCases.__smtx_typeof.case_3 x_a0] from rfl)
    otherwise ⟨hl_0⟩ using
  group_round_step with case_1_eo__24smtx_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_0 x_a0, EoCases.__smtx_typeof.case_1 x_a0, EoCases.__smtx_typeof.case_2 x_a0, EoCases.__smtx_typeof.case_3 x_a0] = [EoCases.__smtx_typeof.case_0 x_a0] ++ [EoCases.__smtx_typeof.case_1 x_a0] ++ [EoCases.__smtx_typeof.case_2 x_a0, EoCases.__smtx_typeof.case_3 x_a0] from rfl)
    otherwise ⟨hl_1⟩ using hl_0
  group_round_step with case_2_eo__24smtx_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_0 x_a0, EoCases.__smtx_typeof.case_1 x_a0, EoCases.__smtx_typeof.case_2 x_a0, EoCases.__smtx_typeof.case_3 x_a0] = [EoCases.__smtx_typeof.case_0 x_a0, EoCases.__smtx_typeof.case_1 x_a0] ++ [EoCases.__smtx_typeof.case_2 x_a0] ++ [EoCases.__smtx_typeof.case_3 x_a0] from rfl)
    otherwise ⟨hl_2⟩ using hl_0 hl_1
  group_round_step with case_3_eo__24smtx_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_0 x_a0, EoCases.__smtx_typeof.case_1 x_a0, EoCases.__smtx_typeof.case_2 x_a0, EoCases.__smtx_typeof.case_3 x_a0] = [EoCases.__smtx_typeof.case_0 x_a0, EoCases.__smtx_typeof.case_1 x_a0, EoCases.__smtx_typeof.case_2 x_a0] ++ [EoCases.__smtx_typeof.case_3 x_a0] ++ [] from rfl)
    otherwise ⟨hl_3⟩ using hl_0 hl_1 hl_2
  group_none hinv4 hG with ⟨hl_0, hl_1, hl_2, hl_3⟩

theorem cases_0_1_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_1_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, (∀ d, firstSome [EoCases.__smtx_typeof.case_4 x_a0, EoCases.__smtx_typeof.case_5 x_a0, EoCases.__smtx_typeof.case_6 x_a0, EoCases.__smtx_typeof.case_7 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          ∀ d, firstSome [EoCases.__smtx_typeof.case_4 x_a0, EoCases.__smtx_typeof.case_5 x_a0, EoCases.__smtx_typeof.case_6 x_a0, EoCases.__smtx_typeof.case_7 x_a0] d = __smtx_typeof y0
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_4 x_a0 = none ∧ EoCases.__smtx_typeof.case_5 x_a0 = none ∧ EoCases.__smtx_typeof.case_6 x_a0 = none ∧ EoCases.__smtx_typeof.case_7 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_1_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  group_round_step with case_4_eo__24smtx_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_4 x_a0, EoCases.__smtx_typeof.case_5 x_a0, EoCases.__smtx_typeof.case_6 x_a0, EoCases.__smtx_typeof.case_7 x_a0] = [] ++ [EoCases.__smtx_typeof.case_4 x_a0] ++ [EoCases.__smtx_typeof.case_5 x_a0, EoCases.__smtx_typeof.case_6 x_a0, EoCases.__smtx_typeof.case_7 x_a0] from rfl)
    otherwise ⟨hl_4⟩ using
  group_round_step with case_5_eo__24smtx_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_4 x_a0, EoCases.__smtx_typeof.case_5 x_a0, EoCases.__smtx_typeof.case_6 x_a0, EoCases.__smtx_typeof.case_7 x_a0] = [EoCases.__smtx_typeof.case_4 x_a0] ++ [EoCases.__smtx_typeof.case_5 x_a0] ++ [EoCases.__smtx_typeof.case_6 x_a0, EoCases.__smtx_typeof.case_7 x_a0] from rfl)
    otherwise ⟨hl_5⟩ using hl_4
  group_round_step with case_6_eo__24smtx_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_4 x_a0, EoCases.__smtx_typeof.case_5 x_a0, EoCases.__smtx_typeof.case_6 x_a0, EoCases.__smtx_typeof.case_7 x_a0] = [EoCases.__smtx_typeof.case_4 x_a0, EoCases.__smtx_typeof.case_5 x_a0] ++ [EoCases.__smtx_typeof.case_6 x_a0] ++ [EoCases.__smtx_typeof.case_7 x_a0] from rfl)
    otherwise ⟨hl_6⟩ using hl_4 hl_5
  group_round_step with case_7_eo__24smtx_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_4 x_a0, EoCases.__smtx_typeof.case_5 x_a0, EoCases.__smtx_typeof.case_6 x_a0, EoCases.__smtx_typeof.case_7 x_a0] = [EoCases.__smtx_typeof.case_4 x_a0, EoCases.__smtx_typeof.case_5 x_a0, EoCases.__smtx_typeof.case_6 x_a0] ++ [EoCases.__smtx_typeof.case_7 x_a0] ++ [] from rfl)
    otherwise ⟨hl_7⟩ using hl_4 hl_5 hl_6
  group_none hinv4 hG with ⟨hl_4, hl_5, hl_6, hl_7⟩

theorem cases_0_2_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_2_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, (∀ d, firstSome [EoCases.__smtx_typeof.case_8 x_a0, EoCases.__smtx_typeof.case_9 x_a0, EoCases.__smtx_typeof.case_10 x_a0, EoCases.__smtx_typeof.case_11 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          ∀ d, firstSome [EoCases.__smtx_typeof.case_8 x_a0, EoCases.__smtx_typeof.case_9 x_a0, EoCases.__smtx_typeof.case_10 x_a0, EoCases.__smtx_typeof.case_11 x_a0] d = __smtx_typeof y0
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_8 x_a0 = none ∧ EoCases.__smtx_typeof.case_9 x_a0 = none ∧ EoCases.__smtx_typeof.case_10 x_a0 = none ∧ EoCases.__smtx_typeof.case_11 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_2_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  group_round_step with case_8_eo__24smtx_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_8 x_a0, EoCases.__smtx_typeof.case_9 x_a0, EoCases.__smtx_typeof.case_10 x_a0, EoCases.__smtx_typeof.case_11 x_a0] = [] ++ [EoCases.__smtx_typeof.case_8 x_a0] ++ [EoCases.__smtx_typeof.case_9 x_a0, EoCases.__smtx_typeof.case_10 x_a0, EoCases.__smtx_typeof.case_11 x_a0] from rfl)
    otherwise ⟨hl_8⟩ using
  group_round_step with case_9_eo__24smtx_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_8 x_a0, EoCases.__smtx_typeof.case_9 x_a0, EoCases.__smtx_typeof.case_10 x_a0, EoCases.__smtx_typeof.case_11 x_a0] = [EoCases.__smtx_typeof.case_8 x_a0] ++ [EoCases.__smtx_typeof.case_9 x_a0] ++ [EoCases.__smtx_typeof.case_10 x_a0, EoCases.__smtx_typeof.case_11 x_a0] from rfl)
    otherwise ⟨hl_9⟩ using hl_8
  group_round_step with case_10_eo__24smtx_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_8 x_a0, EoCases.__smtx_typeof.case_9 x_a0, EoCases.__smtx_typeof.case_10 x_a0, EoCases.__smtx_typeof.case_11 x_a0] = [EoCases.__smtx_typeof.case_8 x_a0, EoCases.__smtx_typeof.case_9 x_a0] ++ [EoCases.__smtx_typeof.case_10 x_a0] ++ [EoCases.__smtx_typeof.case_11 x_a0] from rfl)
    otherwise ⟨hl_10⟩ using hl_8 hl_9
  group_round_step with case_11_eo__24smtx_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_8 x_a0, EoCases.__smtx_typeof.case_9 x_a0, EoCases.__smtx_typeof.case_10 x_a0, EoCases.__smtx_typeof.case_11 x_a0] = [EoCases.__smtx_typeof.case_8 x_a0, EoCases.__smtx_typeof.case_9 x_a0, EoCases.__smtx_typeof.case_10 x_a0] ++ [EoCases.__smtx_typeof.case_11 x_a0] ++ [] from rfl)
    otherwise ⟨hl_11⟩ using hl_8 hl_9 hl_10
  group_none hinv4 hG with ⟨hl_8, hl_9, hl_10, hl_11⟩

theorem cases_0_3_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_3_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, (∀ d, firstSome [EoCases.__smtx_typeof.case_12 x_a0, EoCases.__smtx_typeof.case_13 x_a0, EoCases.__smtx_typeof.case_14 x_a0, EoCases.__smtx_typeof.case_15 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          ∀ d, firstSome [EoCases.__smtx_typeof.case_12 x_a0, EoCases.__smtx_typeof.case_13 x_a0, EoCases.__smtx_typeof.case_14 x_a0, EoCases.__smtx_typeof.case_15 x_a0] d = __smtx_typeof y0
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_12 x_a0 = none ∧ EoCases.__smtx_typeof.case_13 x_a0 = none ∧ EoCases.__smtx_typeof.case_14 x_a0 = none ∧ EoCases.__smtx_typeof.case_15 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_3_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  group_round_step with case_12_eo__24smtx_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_12 x_a0, EoCases.__smtx_typeof.case_13 x_a0, EoCases.__smtx_typeof.case_14 x_a0, EoCases.__smtx_typeof.case_15 x_a0] = [] ++ [EoCases.__smtx_typeof.case_12 x_a0] ++ [EoCases.__smtx_typeof.case_13 x_a0, EoCases.__smtx_typeof.case_14 x_a0, EoCases.__smtx_typeof.case_15 x_a0] from rfl)
    otherwise ⟨hl_12⟩ using
  group_round_step with case_13_eo__24smtx_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_12 x_a0, EoCases.__smtx_typeof.case_13 x_a0, EoCases.__smtx_typeof.case_14 x_a0, EoCases.__smtx_typeof.case_15 x_a0] = [EoCases.__smtx_typeof.case_12 x_a0] ++ [EoCases.__smtx_typeof.case_13 x_a0] ++ [EoCases.__smtx_typeof.case_14 x_a0, EoCases.__smtx_typeof.case_15 x_a0] from rfl)
    otherwise ⟨hl_13⟩ using hl_12
  group_round_step with case_14_eo__24smtx_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_12 x_a0, EoCases.__smtx_typeof.case_13 x_a0, EoCases.__smtx_typeof.case_14 x_a0, EoCases.__smtx_typeof.case_15 x_a0] = [EoCases.__smtx_typeof.case_12 x_a0, EoCases.__smtx_typeof.case_13 x_a0] ++ [EoCases.__smtx_typeof.case_14 x_a0] ++ [EoCases.__smtx_typeof.case_15 x_a0] from rfl)
    otherwise ⟨hl_14⟩ using hl_12 hl_13
  group_round_step with case_15_eo__24smtx_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_12 x_a0, EoCases.__smtx_typeof.case_13 x_a0, EoCases.__smtx_typeof.case_14 x_a0, EoCases.__smtx_typeof.case_15 x_a0] = [EoCases.__smtx_typeof.case_12 x_a0, EoCases.__smtx_typeof.case_13 x_a0, EoCases.__smtx_typeof.case_14 x_a0] ++ [EoCases.__smtx_typeof.case_15 x_a0] ++ [] from rfl)
    otherwise ⟨hl_15⟩ using hl_12 hl_13 hl_14
  group_none hinv4 hG with ⟨hl_12, hl_13, hl_14, hl_15⟩

theorem cases_0_4_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_4_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, (∀ d, firstSome [EoCases.__smtx_typeof.case_16 x_a0, EoCases.__smtx_typeof.case_17 x_a0, EoCases.__smtx_typeof.case_18 x_a0, EoCases.__smtx_typeof.case_19 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          ∀ d, firstSome [EoCases.__smtx_typeof.case_16 x_a0, EoCases.__smtx_typeof.case_17 x_a0, EoCases.__smtx_typeof.case_18 x_a0, EoCases.__smtx_typeof.case_19 x_a0] d = __smtx_typeof y0
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_16 x_a0 = none ∧ EoCases.__smtx_typeof.case_17 x_a0 = none ∧ EoCases.__smtx_typeof.case_18 x_a0 = none ∧ EoCases.__smtx_typeof.case_19 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_4_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  group_round_step with case_16_eo__24smtx_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_16 x_a0, EoCases.__smtx_typeof.case_17 x_a0, EoCases.__smtx_typeof.case_18 x_a0, EoCases.__smtx_typeof.case_19 x_a0] = [] ++ [EoCases.__smtx_typeof.case_16 x_a0] ++ [EoCases.__smtx_typeof.case_17 x_a0, EoCases.__smtx_typeof.case_18 x_a0, EoCases.__smtx_typeof.case_19 x_a0] from rfl)
    otherwise ⟨hl_16⟩ using
  group_round_step with case_17_eo__24smtx_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_16 x_a0, EoCases.__smtx_typeof.case_17 x_a0, EoCases.__smtx_typeof.case_18 x_a0, EoCases.__smtx_typeof.case_19 x_a0] = [EoCases.__smtx_typeof.case_16 x_a0] ++ [EoCases.__smtx_typeof.case_17 x_a0] ++ [EoCases.__smtx_typeof.case_18 x_a0, EoCases.__smtx_typeof.case_19 x_a0] from rfl)
    otherwise ⟨hl_17⟩ using hl_16
  group_round_step with case_18_eo__24smtx_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_16 x_a0, EoCases.__smtx_typeof.case_17 x_a0, EoCases.__smtx_typeof.case_18 x_a0, EoCases.__smtx_typeof.case_19 x_a0] = [EoCases.__smtx_typeof.case_16 x_a0, EoCases.__smtx_typeof.case_17 x_a0] ++ [EoCases.__smtx_typeof.case_18 x_a0] ++ [EoCases.__smtx_typeof.case_19 x_a0] from rfl)
    otherwise ⟨hl_18⟩ using hl_16 hl_17
  group_round_step with case_19_eo__24smtx_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_16 x_a0, EoCases.__smtx_typeof.case_17 x_a0, EoCases.__smtx_typeof.case_18 x_a0, EoCases.__smtx_typeof.case_19 x_a0] = [EoCases.__smtx_typeof.case_16 x_a0, EoCases.__smtx_typeof.case_17 x_a0, EoCases.__smtx_typeof.case_18 x_a0] ++ [EoCases.__smtx_typeof.case_19 x_a0] ++ [] from rfl)
    otherwise ⟨hl_19⟩ using hl_16 hl_17 hl_18
  group_none hinv4 hG with ⟨hl_16, hl_17, hl_18, hl_19⟩

theorem cases_0_5_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_5_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, (∀ d, firstSome [EoCases.__smtx_typeof.case_20 x_a0, EoCases.__smtx_typeof.case_21 x_a0, EoCases.__smtx_typeof.case_22 x_a0, EoCases.__smtx_typeof.case_23 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          ∀ d, firstSome [EoCases.__smtx_typeof.case_20 x_a0, EoCases.__smtx_typeof.case_21 x_a0, EoCases.__smtx_typeof.case_22 x_a0, EoCases.__smtx_typeof.case_23 x_a0] d = __smtx_typeof y0
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_20 x_a0 = none ∧ EoCases.__smtx_typeof.case_21 x_a0 = none ∧ EoCases.__smtx_typeof.case_22 x_a0 = none ∧ EoCases.__smtx_typeof.case_23 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_5_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  group_round_step with case_20_eo__24smtx_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_20 x_a0, EoCases.__smtx_typeof.case_21 x_a0, EoCases.__smtx_typeof.case_22 x_a0, EoCases.__smtx_typeof.case_23 x_a0] = [] ++ [EoCases.__smtx_typeof.case_20 x_a0] ++ [EoCases.__smtx_typeof.case_21 x_a0, EoCases.__smtx_typeof.case_22 x_a0, EoCases.__smtx_typeof.case_23 x_a0] from rfl)
    otherwise ⟨hl_20⟩ using
  group_round_step with case_21_eo__24smtx_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_20 x_a0, EoCases.__smtx_typeof.case_21 x_a0, EoCases.__smtx_typeof.case_22 x_a0, EoCases.__smtx_typeof.case_23 x_a0] = [EoCases.__smtx_typeof.case_20 x_a0] ++ [EoCases.__smtx_typeof.case_21 x_a0] ++ [EoCases.__smtx_typeof.case_22 x_a0, EoCases.__smtx_typeof.case_23 x_a0] from rfl)
    otherwise ⟨hl_21⟩ using hl_20
  group_round_step with case_22_eo__24smtx_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_20 x_a0, EoCases.__smtx_typeof.case_21 x_a0, EoCases.__smtx_typeof.case_22 x_a0, EoCases.__smtx_typeof.case_23 x_a0] = [EoCases.__smtx_typeof.case_20 x_a0, EoCases.__smtx_typeof.case_21 x_a0] ++ [EoCases.__smtx_typeof.case_22 x_a0] ++ [EoCases.__smtx_typeof.case_23 x_a0] from rfl)
    otherwise ⟨hl_22⟩ using hl_20 hl_21
  group_round_step with case_23_eo__24smtx_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_20 x_a0, EoCases.__smtx_typeof.case_21 x_a0, EoCases.__smtx_typeof.case_22 x_a0, EoCases.__smtx_typeof.case_23 x_a0] = [EoCases.__smtx_typeof.case_20 x_a0, EoCases.__smtx_typeof.case_21 x_a0, EoCases.__smtx_typeof.case_22 x_a0] ++ [EoCases.__smtx_typeof.case_23 x_a0] ++ [] from rfl)
    otherwise ⟨hl_23⟩ using hl_20 hl_21 hl_22
  group_none hinv4 hG with ⟨hl_20, hl_21, hl_22, hl_23⟩

theorem cases_0_6_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_6_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, (∀ d, firstSome [EoCases.__smtx_typeof.case_24 x_a0, EoCases.__smtx_typeof.case_25 x_a0, EoCases.__smtx_typeof.case_26 x_a0, EoCases.__smtx_typeof.case_27 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          ∀ d, firstSome [EoCases.__smtx_typeof.case_24 x_a0, EoCases.__smtx_typeof.case_25 x_a0, EoCases.__smtx_typeof.case_26 x_a0, EoCases.__smtx_typeof.case_27 x_a0] d = __smtx_typeof y0
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_24 x_a0 = none ∧ EoCases.__smtx_typeof.case_25 x_a0 = none ∧ EoCases.__smtx_typeof.case_26 x_a0 = none ∧ EoCases.__smtx_typeof.case_27 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_6_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  group_round_step with case_24_eo__24smtx_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_24 x_a0, EoCases.__smtx_typeof.case_25 x_a0, EoCases.__smtx_typeof.case_26 x_a0, EoCases.__smtx_typeof.case_27 x_a0] = [] ++ [EoCases.__smtx_typeof.case_24 x_a0] ++ [EoCases.__smtx_typeof.case_25 x_a0, EoCases.__smtx_typeof.case_26 x_a0, EoCases.__smtx_typeof.case_27 x_a0] from rfl)
    otherwise ⟨hl_24⟩ using
  group_round_step with case_25_eo__24smtx_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_24 x_a0, EoCases.__smtx_typeof.case_25 x_a0, EoCases.__smtx_typeof.case_26 x_a0, EoCases.__smtx_typeof.case_27 x_a0] = [EoCases.__smtx_typeof.case_24 x_a0] ++ [EoCases.__smtx_typeof.case_25 x_a0] ++ [EoCases.__smtx_typeof.case_26 x_a0, EoCases.__smtx_typeof.case_27 x_a0] from rfl)
    otherwise ⟨hl_25⟩ using hl_24
  group_round_step with case_26_eo__24smtx_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_24 x_a0, EoCases.__smtx_typeof.case_25 x_a0, EoCases.__smtx_typeof.case_26 x_a0, EoCases.__smtx_typeof.case_27 x_a0] = [EoCases.__smtx_typeof.case_24 x_a0, EoCases.__smtx_typeof.case_25 x_a0] ++ [EoCases.__smtx_typeof.case_26 x_a0] ++ [EoCases.__smtx_typeof.case_27 x_a0] from rfl)
    otherwise ⟨hl_26⟩ using hl_24 hl_25
  group_round_step with case_27_eo__24smtx_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_24 x_a0, EoCases.__smtx_typeof.case_25 x_a0, EoCases.__smtx_typeof.case_26 x_a0, EoCases.__smtx_typeof.case_27 x_a0] = [EoCases.__smtx_typeof.case_24 x_a0, EoCases.__smtx_typeof.case_25 x_a0, EoCases.__smtx_typeof.case_26 x_a0] ++ [EoCases.__smtx_typeof.case_27 x_a0] ++ [] from rfl)
    otherwise ⟨hl_27⟩ using hl_24 hl_25 hl_26
  group_none hinv4 hG with ⟨hl_24, hl_25, hl_26, hl_27⟩

theorem cases_0_7_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_7_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, (∀ d, firstSome [EoCases.__smtx_typeof.case_28 x_a0, EoCases.__smtx_typeof.case_29 x_a0, EoCases.__smtx_typeof.case_30 x_a0, EoCases.__smtx_typeof.case_31 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          ∀ d, firstSome [EoCases.__smtx_typeof.case_28 x_a0, EoCases.__smtx_typeof.case_29 x_a0, EoCases.__smtx_typeof.case_30 x_a0, EoCases.__smtx_typeof.case_31 x_a0] d = __smtx_typeof y0
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_28 x_a0 = none ∧ EoCases.__smtx_typeof.case_29 x_a0 = none ∧ EoCases.__smtx_typeof.case_30 x_a0 = none ∧ EoCases.__smtx_typeof.case_31 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_7_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  group_round_step with case_28_eo__24smtx_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_28 x_a0, EoCases.__smtx_typeof.case_29 x_a0, EoCases.__smtx_typeof.case_30 x_a0, EoCases.__smtx_typeof.case_31 x_a0] = [] ++ [EoCases.__smtx_typeof.case_28 x_a0] ++ [EoCases.__smtx_typeof.case_29 x_a0, EoCases.__smtx_typeof.case_30 x_a0, EoCases.__smtx_typeof.case_31 x_a0] from rfl)
    otherwise ⟨hl_28⟩ using
  group_round_step with case_29_eo__24smtx_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_28 x_a0, EoCases.__smtx_typeof.case_29 x_a0, EoCases.__smtx_typeof.case_30 x_a0, EoCases.__smtx_typeof.case_31 x_a0] = [EoCases.__smtx_typeof.case_28 x_a0] ++ [EoCases.__smtx_typeof.case_29 x_a0] ++ [EoCases.__smtx_typeof.case_30 x_a0, EoCases.__smtx_typeof.case_31 x_a0] from rfl)
    otherwise ⟨hl_29⟩ using hl_28
  group_round_step with case_30_eo__24smtx_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_28 x_a0, EoCases.__smtx_typeof.case_29 x_a0, EoCases.__smtx_typeof.case_30 x_a0, EoCases.__smtx_typeof.case_31 x_a0] = [EoCases.__smtx_typeof.case_28 x_a0, EoCases.__smtx_typeof.case_29 x_a0] ++ [EoCases.__smtx_typeof.case_30 x_a0] ++ [EoCases.__smtx_typeof.case_31 x_a0] from rfl)
    otherwise ⟨hl_30⟩ using hl_28 hl_29
  group_round_step with case_31_eo__24smtx_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_28 x_a0, EoCases.__smtx_typeof.case_29 x_a0, EoCases.__smtx_typeof.case_30 x_a0, EoCases.__smtx_typeof.case_31 x_a0] = [EoCases.__smtx_typeof.case_28 x_a0, EoCases.__smtx_typeof.case_29 x_a0, EoCases.__smtx_typeof.case_30 x_a0] ++ [EoCases.__smtx_typeof.case_31 x_a0] ++ [] from rfl)
    otherwise ⟨hl_31⟩ using hl_28 hl_29 hl_30
  group_none hinv4 hG with ⟨hl_28, hl_29, hl_30, hl_31⟩

theorem cases_0_8_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_8_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, (∀ d, firstSome [EoCases.__smtx_typeof.case_32 x_a0, EoCases.__smtx_typeof.case_33 x_a0, EoCases.__smtx_typeof.case_34 x_a0, EoCases.__smtx_typeof.case_35 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          ∀ d, firstSome [EoCases.__smtx_typeof.case_32 x_a0, EoCases.__smtx_typeof.case_33 x_a0, EoCases.__smtx_typeof.case_34 x_a0, EoCases.__smtx_typeof.case_35 x_a0] d = __smtx_typeof y0
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_32 x_a0 = none ∧ EoCases.__smtx_typeof.case_33 x_a0 = none ∧ EoCases.__smtx_typeof.case_34 x_a0 = none ∧ EoCases.__smtx_typeof.case_35 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_8_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  group_round_step with case_32_eo__24smtx_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_32 x_a0, EoCases.__smtx_typeof.case_33 x_a0, EoCases.__smtx_typeof.case_34 x_a0, EoCases.__smtx_typeof.case_35 x_a0] = [] ++ [EoCases.__smtx_typeof.case_32 x_a0] ++ [EoCases.__smtx_typeof.case_33 x_a0, EoCases.__smtx_typeof.case_34 x_a0, EoCases.__smtx_typeof.case_35 x_a0] from rfl)
    otherwise ⟨hl_32⟩ using
  group_round_step with case_33_eo__24smtx_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_32 x_a0, EoCases.__smtx_typeof.case_33 x_a0, EoCases.__smtx_typeof.case_34 x_a0, EoCases.__smtx_typeof.case_35 x_a0] = [EoCases.__smtx_typeof.case_32 x_a0] ++ [EoCases.__smtx_typeof.case_33 x_a0] ++ [EoCases.__smtx_typeof.case_34 x_a0, EoCases.__smtx_typeof.case_35 x_a0] from rfl)
    otherwise ⟨hl_33⟩ using hl_32
  group_round_step with case_34_eo__24smtx_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_32 x_a0, EoCases.__smtx_typeof.case_33 x_a0, EoCases.__smtx_typeof.case_34 x_a0, EoCases.__smtx_typeof.case_35 x_a0] = [EoCases.__smtx_typeof.case_32 x_a0, EoCases.__smtx_typeof.case_33 x_a0] ++ [EoCases.__smtx_typeof.case_34 x_a0] ++ [EoCases.__smtx_typeof.case_35 x_a0] from rfl)
    otherwise ⟨hl_34⟩ using hl_32 hl_33
  group_round_step with case_35_eo__24smtx_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_32 x_a0, EoCases.__smtx_typeof.case_33 x_a0, EoCases.__smtx_typeof.case_34 x_a0, EoCases.__smtx_typeof.case_35 x_a0] = [EoCases.__smtx_typeof.case_32 x_a0, EoCases.__smtx_typeof.case_33 x_a0, EoCases.__smtx_typeof.case_34 x_a0] ++ [EoCases.__smtx_typeof.case_35 x_a0] ++ [] from rfl)
    otherwise ⟨hl_35⟩ using hl_32 hl_33 hl_34
  group_none hinv4 hG with ⟨hl_32, hl_33, hl_34, hl_35⟩

theorem cases_0_9_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_9_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, (∀ d, firstSome [EoCases.__smtx_typeof.case_36 x_a0, EoCases.__smtx_typeof.case_37 x_a0, EoCases.__smtx_typeof.case_38 x_a0, EoCases.__smtx_typeof.case_39 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          ∀ d, firstSome [EoCases.__smtx_typeof.case_36 x_a0, EoCases.__smtx_typeof.case_37 x_a0, EoCases.__smtx_typeof.case_38 x_a0, EoCases.__smtx_typeof.case_39 x_a0] d = __smtx_typeof y0
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_36 x_a0 = none ∧ EoCases.__smtx_typeof.case_37 x_a0 = none ∧ EoCases.__smtx_typeof.case_38 x_a0 = none ∧ EoCases.__smtx_typeof.case_39 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_9_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  group_round_step with case_36_eo__24smtx_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_36 x_a0, EoCases.__smtx_typeof.case_37 x_a0, EoCases.__smtx_typeof.case_38 x_a0, EoCases.__smtx_typeof.case_39 x_a0] = [] ++ [EoCases.__smtx_typeof.case_36 x_a0] ++ [EoCases.__smtx_typeof.case_37 x_a0, EoCases.__smtx_typeof.case_38 x_a0, EoCases.__smtx_typeof.case_39 x_a0] from rfl)
    otherwise ⟨hl_36⟩ using
  group_round_step with case_37_eo__24smtx_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_36 x_a0, EoCases.__smtx_typeof.case_37 x_a0, EoCases.__smtx_typeof.case_38 x_a0, EoCases.__smtx_typeof.case_39 x_a0] = [EoCases.__smtx_typeof.case_36 x_a0] ++ [EoCases.__smtx_typeof.case_37 x_a0] ++ [EoCases.__smtx_typeof.case_38 x_a0, EoCases.__smtx_typeof.case_39 x_a0] from rfl)
    otherwise ⟨hl_37⟩ using hl_36
  group_round_step with case_38_eo__24smtx_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_36 x_a0, EoCases.__smtx_typeof.case_37 x_a0, EoCases.__smtx_typeof.case_38 x_a0, EoCases.__smtx_typeof.case_39 x_a0] = [EoCases.__smtx_typeof.case_36 x_a0, EoCases.__smtx_typeof.case_37 x_a0] ++ [EoCases.__smtx_typeof.case_38 x_a0] ++ [EoCases.__smtx_typeof.case_39 x_a0] from rfl)
    otherwise ⟨hl_38⟩ using hl_36 hl_37
  group_round_step with case_39_eo__24smtx_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_36 x_a0, EoCases.__smtx_typeof.case_37 x_a0, EoCases.__smtx_typeof.case_38 x_a0, EoCases.__smtx_typeof.case_39 x_a0] = [EoCases.__smtx_typeof.case_36 x_a0, EoCases.__smtx_typeof.case_37 x_a0, EoCases.__smtx_typeof.case_38 x_a0] ++ [EoCases.__smtx_typeof.case_39 x_a0] ++ [] from rfl)
    otherwise ⟨hl_39⟩ using hl_36 hl_37 hl_38
  group_none hinv4 hG with ⟨hl_36, hl_37, hl_38, hl_39⟩

theorem cases_0_10_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_10_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, (∀ d, firstSome [EoCases.__smtx_typeof.case_40 x_a0, EoCases.__smtx_typeof.case_41 x_a0, EoCases.__smtx_typeof.case_42 x_a0, EoCases.__smtx_typeof.case_43 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          ∀ d, firstSome [EoCases.__smtx_typeof.case_40 x_a0, EoCases.__smtx_typeof.case_41 x_a0, EoCases.__smtx_typeof.case_42 x_a0, EoCases.__smtx_typeof.case_43 x_a0] d = __smtx_typeof y0
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_40 x_a0 = none ∧ EoCases.__smtx_typeof.case_41 x_a0 = none ∧ EoCases.__smtx_typeof.case_42 x_a0 = none ∧ EoCases.__smtx_typeof.case_43 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_10_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  group_round_step with case_40_eo__24smtx_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_40 x_a0, EoCases.__smtx_typeof.case_41 x_a0, EoCases.__smtx_typeof.case_42 x_a0, EoCases.__smtx_typeof.case_43 x_a0] = [] ++ [EoCases.__smtx_typeof.case_40 x_a0] ++ [EoCases.__smtx_typeof.case_41 x_a0, EoCases.__smtx_typeof.case_42 x_a0, EoCases.__smtx_typeof.case_43 x_a0] from rfl)
    otherwise ⟨hl_40⟩ using
  group_round_step with case_41_eo__24smtx_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_40 x_a0, EoCases.__smtx_typeof.case_41 x_a0, EoCases.__smtx_typeof.case_42 x_a0, EoCases.__smtx_typeof.case_43 x_a0] = [EoCases.__smtx_typeof.case_40 x_a0] ++ [EoCases.__smtx_typeof.case_41 x_a0] ++ [EoCases.__smtx_typeof.case_42 x_a0, EoCases.__smtx_typeof.case_43 x_a0] from rfl)
    otherwise ⟨hl_41⟩ using hl_40
  group_round_step with case_42_eo__24smtx_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_40 x_a0, EoCases.__smtx_typeof.case_41 x_a0, EoCases.__smtx_typeof.case_42 x_a0, EoCases.__smtx_typeof.case_43 x_a0] = [EoCases.__smtx_typeof.case_40 x_a0, EoCases.__smtx_typeof.case_41 x_a0] ++ [EoCases.__smtx_typeof.case_42 x_a0] ++ [EoCases.__smtx_typeof.case_43 x_a0] from rfl)
    otherwise ⟨hl_42⟩ using hl_40 hl_41
  group_round_step with case_43_eo__24smtx_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_40 x_a0, EoCases.__smtx_typeof.case_41 x_a0, EoCases.__smtx_typeof.case_42 x_a0, EoCases.__smtx_typeof.case_43 x_a0] = [EoCases.__smtx_typeof.case_40 x_a0, EoCases.__smtx_typeof.case_41 x_a0, EoCases.__smtx_typeof.case_42 x_a0] ++ [EoCases.__smtx_typeof.case_43 x_a0] ++ [] from rfl)
    otherwise ⟨hl_43⟩ using hl_40 hl_41 hl_42
  group_none hinv4 hG with ⟨hl_40, hl_41, hl_42, hl_43⟩

theorem cases_0_11_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_11_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, (∀ d, firstSome [EoCases.__smtx_typeof.case_44 x_a0, EoCases.__smtx_typeof.case_45 x_a0, EoCases.__smtx_typeof.case_46 x_a0, EoCases.__smtx_typeof.case_47 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          ∀ d, firstSome [EoCases.__smtx_typeof.case_44 x_a0, EoCases.__smtx_typeof.case_45 x_a0, EoCases.__smtx_typeof.case_46 x_a0, EoCases.__smtx_typeof.case_47 x_a0] d = __smtx_typeof y0
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_44 x_a0 = none ∧ EoCases.__smtx_typeof.case_45 x_a0 = none ∧ EoCases.__smtx_typeof.case_46 x_a0 = none ∧ EoCases.__smtx_typeof.case_47 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_11_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  group_round_step with case_44_eo__24smtx_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_44 x_a0, EoCases.__smtx_typeof.case_45 x_a0, EoCases.__smtx_typeof.case_46 x_a0, EoCases.__smtx_typeof.case_47 x_a0] = [] ++ [EoCases.__smtx_typeof.case_44 x_a0] ++ [EoCases.__smtx_typeof.case_45 x_a0, EoCases.__smtx_typeof.case_46 x_a0, EoCases.__smtx_typeof.case_47 x_a0] from rfl)
    otherwise ⟨hl_44⟩ using
  group_round_step with case_45_eo__24smtx_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_44 x_a0, EoCases.__smtx_typeof.case_45 x_a0, EoCases.__smtx_typeof.case_46 x_a0, EoCases.__smtx_typeof.case_47 x_a0] = [EoCases.__smtx_typeof.case_44 x_a0] ++ [EoCases.__smtx_typeof.case_45 x_a0] ++ [EoCases.__smtx_typeof.case_46 x_a0, EoCases.__smtx_typeof.case_47 x_a0] from rfl)
    otherwise ⟨hl_45⟩ using hl_44
  group_round_step with case_46_eo__24smtx_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_44 x_a0, EoCases.__smtx_typeof.case_45 x_a0, EoCases.__smtx_typeof.case_46 x_a0, EoCases.__smtx_typeof.case_47 x_a0] = [EoCases.__smtx_typeof.case_44 x_a0, EoCases.__smtx_typeof.case_45 x_a0] ++ [EoCases.__smtx_typeof.case_46 x_a0] ++ [EoCases.__smtx_typeof.case_47 x_a0] from rfl)
    otherwise ⟨hl_46⟩ using hl_44 hl_45
  group_round_step with case_47_eo__24smtx_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_44 x_a0, EoCases.__smtx_typeof.case_45 x_a0, EoCases.__smtx_typeof.case_46 x_a0, EoCases.__smtx_typeof.case_47 x_a0] = [EoCases.__smtx_typeof.case_44 x_a0, EoCases.__smtx_typeof.case_45 x_a0, EoCases.__smtx_typeof.case_46 x_a0] ++ [EoCases.__smtx_typeof.case_47 x_a0] ++ [] from rfl)
    otherwise ⟨hl_47⟩ using hl_44 hl_45 hl_46
  group_none hinv4 hG with ⟨hl_44, hl_45, hl_46, hl_47⟩

theorem cases_0_12_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_12_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, (∀ d, firstSome [EoCases.__smtx_typeof.case_48 x_a0, EoCases.__smtx_typeof.case_49 x_a0, EoCases.__smtx_typeof.case_50 x_a0, EoCases.__smtx_typeof.case_51 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          ∀ d, firstSome [EoCases.__smtx_typeof.case_48 x_a0, EoCases.__smtx_typeof.case_49 x_a0, EoCases.__smtx_typeof.case_50 x_a0, EoCases.__smtx_typeof.case_51 x_a0] d = __smtx_typeof y0
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_48 x_a0 = none ∧ EoCases.__smtx_typeof.case_49 x_a0 = none ∧ EoCases.__smtx_typeof.case_50 x_a0 = none ∧ EoCases.__smtx_typeof.case_51 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_12_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  group_round_step with case_48_eo__24smtx_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_48 x_a0, EoCases.__smtx_typeof.case_49 x_a0, EoCases.__smtx_typeof.case_50 x_a0, EoCases.__smtx_typeof.case_51 x_a0] = [] ++ [EoCases.__smtx_typeof.case_48 x_a0] ++ [EoCases.__smtx_typeof.case_49 x_a0, EoCases.__smtx_typeof.case_50 x_a0, EoCases.__smtx_typeof.case_51 x_a0] from rfl)
    otherwise ⟨hl_48⟩ using
  group_round_step with case_49_eo__24smtx_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_48 x_a0, EoCases.__smtx_typeof.case_49 x_a0, EoCases.__smtx_typeof.case_50 x_a0, EoCases.__smtx_typeof.case_51 x_a0] = [EoCases.__smtx_typeof.case_48 x_a0] ++ [EoCases.__smtx_typeof.case_49 x_a0] ++ [EoCases.__smtx_typeof.case_50 x_a0, EoCases.__smtx_typeof.case_51 x_a0] from rfl)
    otherwise ⟨hl_49⟩ using hl_48
  group_round_step with case_50_eo__24smtx_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_48 x_a0, EoCases.__smtx_typeof.case_49 x_a0, EoCases.__smtx_typeof.case_50 x_a0, EoCases.__smtx_typeof.case_51 x_a0] = [EoCases.__smtx_typeof.case_48 x_a0, EoCases.__smtx_typeof.case_49 x_a0] ++ [EoCases.__smtx_typeof.case_50 x_a0] ++ [EoCases.__smtx_typeof.case_51 x_a0] from rfl)
    otherwise ⟨hl_50⟩ using hl_48 hl_49
  group_round_step with case_51_eo__24smtx_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_48 x_a0, EoCases.__smtx_typeof.case_49 x_a0, EoCases.__smtx_typeof.case_50 x_a0, EoCases.__smtx_typeof.case_51 x_a0] = [EoCases.__smtx_typeof.case_48 x_a0, EoCases.__smtx_typeof.case_49 x_a0, EoCases.__smtx_typeof.case_50 x_a0] ++ [EoCases.__smtx_typeof.case_51 x_a0] ++ [] from rfl)
    otherwise ⟨hl_51⟩ using hl_48 hl_49 hl_50
  group_none hinv4 hG with ⟨hl_48, hl_49, hl_50, hl_51⟩

theorem cases_0_13_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_13_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, (∀ d, firstSome [EoCases.__smtx_typeof.case_52 x_a0, EoCases.__smtx_typeof.case_53 x_a0, EoCases.__smtx_typeof.case_54 x_a0, EoCases.__smtx_typeof.case_55 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          ∀ d, firstSome [EoCases.__smtx_typeof.case_52 x_a0, EoCases.__smtx_typeof.case_53 x_a0, EoCases.__smtx_typeof.case_54 x_a0, EoCases.__smtx_typeof.case_55 x_a0] d = __smtx_typeof y0
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_52 x_a0 = none ∧ EoCases.__smtx_typeof.case_53 x_a0 = none ∧ EoCases.__smtx_typeof.case_54 x_a0 = none ∧ EoCases.__smtx_typeof.case_55 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_13_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  group_round_step with case_52_eo__24smtx_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_52 x_a0, EoCases.__smtx_typeof.case_53 x_a0, EoCases.__smtx_typeof.case_54 x_a0, EoCases.__smtx_typeof.case_55 x_a0] = [] ++ [EoCases.__smtx_typeof.case_52 x_a0] ++ [EoCases.__smtx_typeof.case_53 x_a0, EoCases.__smtx_typeof.case_54 x_a0, EoCases.__smtx_typeof.case_55 x_a0] from rfl)
    otherwise ⟨hl_52⟩ using
  group_round_step with case_53_eo__24smtx_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_52 x_a0, EoCases.__smtx_typeof.case_53 x_a0, EoCases.__smtx_typeof.case_54 x_a0, EoCases.__smtx_typeof.case_55 x_a0] = [EoCases.__smtx_typeof.case_52 x_a0] ++ [EoCases.__smtx_typeof.case_53 x_a0] ++ [EoCases.__smtx_typeof.case_54 x_a0, EoCases.__smtx_typeof.case_55 x_a0] from rfl)
    otherwise ⟨hl_53⟩ using hl_52
  group_round_step with case_54_eo__24smtx_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_52 x_a0, EoCases.__smtx_typeof.case_53 x_a0, EoCases.__smtx_typeof.case_54 x_a0, EoCases.__smtx_typeof.case_55 x_a0] = [EoCases.__smtx_typeof.case_52 x_a0, EoCases.__smtx_typeof.case_53 x_a0] ++ [EoCases.__smtx_typeof.case_54 x_a0] ++ [EoCases.__smtx_typeof.case_55 x_a0] from rfl)
    otherwise ⟨hl_54⟩ using hl_52 hl_53
  group_round_step with case_55_eo__24smtx_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_52 x_a0, EoCases.__smtx_typeof.case_53 x_a0, EoCases.__smtx_typeof.case_54 x_a0, EoCases.__smtx_typeof.case_55 x_a0] = [EoCases.__smtx_typeof.case_52 x_a0, EoCases.__smtx_typeof.case_53 x_a0, EoCases.__smtx_typeof.case_54 x_a0] ++ [EoCases.__smtx_typeof.case_55 x_a0] ++ [] from rfl)
    otherwise ⟨hl_55⟩ using hl_52 hl_53 hl_54
  group_none hinv4 hG with ⟨hl_52, hl_53, hl_54, hl_55⟩

theorem cases_0_14_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_14_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, (∀ d, firstSome [EoCases.__smtx_typeof.case_56 x_a0, EoCases.__smtx_typeof.case_57 x_a0, EoCases.__smtx_typeof.case_58 x_a0, EoCases.__smtx_typeof.case_59 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          ∀ d, firstSome [EoCases.__smtx_typeof.case_56 x_a0, EoCases.__smtx_typeof.case_57 x_a0, EoCases.__smtx_typeof.case_58 x_a0, EoCases.__smtx_typeof.case_59 x_a0] d = __smtx_typeof y0
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_56 x_a0 = none ∧ EoCases.__smtx_typeof.case_57 x_a0 = none ∧ EoCases.__smtx_typeof.case_58 x_a0 = none ∧ EoCases.__smtx_typeof.case_59 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_14_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  group_round_step with case_56_eo__24smtx_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_56 x_a0, EoCases.__smtx_typeof.case_57 x_a0, EoCases.__smtx_typeof.case_58 x_a0, EoCases.__smtx_typeof.case_59 x_a0] = [] ++ [EoCases.__smtx_typeof.case_56 x_a0] ++ [EoCases.__smtx_typeof.case_57 x_a0, EoCases.__smtx_typeof.case_58 x_a0, EoCases.__smtx_typeof.case_59 x_a0] from rfl)
    otherwise ⟨hl_56⟩ using
  group_round_step with case_57_eo__24smtx_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_56 x_a0, EoCases.__smtx_typeof.case_57 x_a0, EoCases.__smtx_typeof.case_58 x_a0, EoCases.__smtx_typeof.case_59 x_a0] = [EoCases.__smtx_typeof.case_56 x_a0] ++ [EoCases.__smtx_typeof.case_57 x_a0] ++ [EoCases.__smtx_typeof.case_58 x_a0, EoCases.__smtx_typeof.case_59 x_a0] from rfl)
    otherwise ⟨hl_57⟩ using hl_56
  group_round_step with case_58_eo__24smtx_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_56 x_a0, EoCases.__smtx_typeof.case_57 x_a0, EoCases.__smtx_typeof.case_58 x_a0, EoCases.__smtx_typeof.case_59 x_a0] = [EoCases.__smtx_typeof.case_56 x_a0, EoCases.__smtx_typeof.case_57 x_a0] ++ [EoCases.__smtx_typeof.case_58 x_a0] ++ [EoCases.__smtx_typeof.case_59 x_a0] from rfl)
    otherwise ⟨hl_58⟩ using hl_56 hl_57
  group_round_step with case_59_eo__24smtx_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_56 x_a0, EoCases.__smtx_typeof.case_57 x_a0, EoCases.__smtx_typeof.case_58 x_a0, EoCases.__smtx_typeof.case_59 x_a0] = [EoCases.__smtx_typeof.case_56 x_a0, EoCases.__smtx_typeof.case_57 x_a0, EoCases.__smtx_typeof.case_58 x_a0] ++ [EoCases.__smtx_typeof.case_59 x_a0] ++ [] from rfl)
    otherwise ⟨hl_59⟩ using hl_56 hl_57 hl_58
  group_none hinv4 hG with ⟨hl_56, hl_57, hl_58, hl_59⟩

theorem cases_0_15_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_15_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, (∀ d, firstSome [EoCases.__smtx_typeof.case_60 x_a0, EoCases.__smtx_typeof.case_61 x_a0, EoCases.__smtx_typeof.case_62 x_a0, EoCases.__smtx_typeof.case_63 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          ∀ d, firstSome [EoCases.__smtx_typeof.case_60 x_a0, EoCases.__smtx_typeof.case_61 x_a0, EoCases.__smtx_typeof.case_62 x_a0, EoCases.__smtx_typeof.case_63 x_a0] d = __smtx_typeof y0
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_60 x_a0 = none ∧ EoCases.__smtx_typeof.case_61 x_a0 = none ∧ EoCases.__smtx_typeof.case_62 x_a0 = none ∧ EoCases.__smtx_typeof.case_63 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_15_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  group_round_step with case_60_eo__24smtx_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_60 x_a0, EoCases.__smtx_typeof.case_61 x_a0, EoCases.__smtx_typeof.case_62 x_a0, EoCases.__smtx_typeof.case_63 x_a0] = [] ++ [EoCases.__smtx_typeof.case_60 x_a0] ++ [EoCases.__smtx_typeof.case_61 x_a0, EoCases.__smtx_typeof.case_62 x_a0, EoCases.__smtx_typeof.case_63 x_a0] from rfl)
    otherwise ⟨hl_60⟩ using
  group_round_step with case_61_eo__24smtx_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_60 x_a0, EoCases.__smtx_typeof.case_61 x_a0, EoCases.__smtx_typeof.case_62 x_a0, EoCases.__smtx_typeof.case_63 x_a0] = [EoCases.__smtx_typeof.case_60 x_a0] ++ [EoCases.__smtx_typeof.case_61 x_a0] ++ [EoCases.__smtx_typeof.case_62 x_a0, EoCases.__smtx_typeof.case_63 x_a0] from rfl)
    otherwise ⟨hl_61⟩ using hl_60
  group_round_step with case_62_eo__24smtx_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_60 x_a0, EoCases.__smtx_typeof.case_61 x_a0, EoCases.__smtx_typeof.case_62 x_a0, EoCases.__smtx_typeof.case_63 x_a0] = [EoCases.__smtx_typeof.case_60 x_a0, EoCases.__smtx_typeof.case_61 x_a0] ++ [EoCases.__smtx_typeof.case_62 x_a0] ++ [EoCases.__smtx_typeof.case_63 x_a0] from rfl)
    otherwise ⟨hl_62⟩ using hl_60 hl_61
  group_round_step with case_63_eo__24smtx_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_60 x_a0, EoCases.__smtx_typeof.case_61 x_a0, EoCases.__smtx_typeof.case_62 x_a0, EoCases.__smtx_typeof.case_63 x_a0] = [EoCases.__smtx_typeof.case_60 x_a0, EoCases.__smtx_typeof.case_61 x_a0, EoCases.__smtx_typeof.case_62 x_a0] ++ [EoCases.__smtx_typeof.case_63 x_a0] ++ [] from rfl)
    otherwise ⟨hl_63⟩ using hl_60 hl_61 hl_62
  group_none hinv4 hG with ⟨hl_60, hl_61, hl_62, hl_63⟩

theorem cases_0_16_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_16_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, (∀ d, firstSome [EoCases.__smtx_typeof.case_64 x_a0, EoCases.__smtx_typeof.case_65 x_a0, EoCases.__smtx_typeof.case_66 x_a0, EoCases.__smtx_typeof.case_67 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          ∀ d, firstSome [EoCases.__smtx_typeof.case_64 x_a0, EoCases.__smtx_typeof.case_65 x_a0, EoCases.__smtx_typeof.case_66 x_a0, EoCases.__smtx_typeof.case_67 x_a0] d = __smtx_typeof y0
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_64 x_a0 = none ∧ EoCases.__smtx_typeof.case_65 x_a0 = none ∧ EoCases.__smtx_typeof.case_66 x_a0 = none ∧ EoCases.__smtx_typeof.case_67 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_16_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  group_round_step with case_64_eo__24smtx_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_64 x_a0, EoCases.__smtx_typeof.case_65 x_a0, EoCases.__smtx_typeof.case_66 x_a0, EoCases.__smtx_typeof.case_67 x_a0] = [] ++ [EoCases.__smtx_typeof.case_64 x_a0] ++ [EoCases.__smtx_typeof.case_65 x_a0, EoCases.__smtx_typeof.case_66 x_a0, EoCases.__smtx_typeof.case_67 x_a0] from rfl)
    otherwise ⟨hl_64⟩ using
  group_round_step with case_65_eo__24smtx_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_64 x_a0, EoCases.__smtx_typeof.case_65 x_a0, EoCases.__smtx_typeof.case_66 x_a0, EoCases.__smtx_typeof.case_67 x_a0] = [EoCases.__smtx_typeof.case_64 x_a0] ++ [EoCases.__smtx_typeof.case_65 x_a0] ++ [EoCases.__smtx_typeof.case_66 x_a0, EoCases.__smtx_typeof.case_67 x_a0] from rfl)
    otherwise ⟨hl_65⟩ using hl_64
  group_round_step with case_66_eo__24smtx_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_64 x_a0, EoCases.__smtx_typeof.case_65 x_a0, EoCases.__smtx_typeof.case_66 x_a0, EoCases.__smtx_typeof.case_67 x_a0] = [EoCases.__smtx_typeof.case_64 x_a0, EoCases.__smtx_typeof.case_65 x_a0] ++ [EoCases.__smtx_typeof.case_66 x_a0] ++ [EoCases.__smtx_typeof.case_67 x_a0] from rfl)
    otherwise ⟨hl_66⟩ using hl_64 hl_65
  group_round_step with case_67_eo__24smtx_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_64 x_a0, EoCases.__smtx_typeof.case_65 x_a0, EoCases.__smtx_typeof.case_66 x_a0, EoCases.__smtx_typeof.case_67 x_a0] = [EoCases.__smtx_typeof.case_64 x_a0, EoCases.__smtx_typeof.case_65 x_a0, EoCases.__smtx_typeof.case_66 x_a0] ++ [EoCases.__smtx_typeof.case_67 x_a0] ++ [] from rfl)
    otherwise ⟨hl_67⟩ using hl_64 hl_65 hl_66
  group_none hinv4 hG with ⟨hl_64, hl_65, hl_66, hl_67⟩

theorem cases_0_17_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_17_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, (∀ d, firstSome [EoCases.__smtx_typeof.case_68 x_a0, EoCases.__smtx_typeof.case_69 x_a0, EoCases.__smtx_typeof.case_70 x_a0, EoCases.__smtx_typeof.case_71 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          ∀ d, firstSome [EoCases.__smtx_typeof.case_68 x_a0, EoCases.__smtx_typeof.case_69 x_a0, EoCases.__smtx_typeof.case_70 x_a0, EoCases.__smtx_typeof.case_71 x_a0] d = __smtx_typeof y0
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_68 x_a0 = none ∧ EoCases.__smtx_typeof.case_69 x_a0 = none ∧ EoCases.__smtx_typeof.case_70 x_a0 = none ∧ EoCases.__smtx_typeof.case_71 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_17_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  group_round_step with case_68_eo__24smtx_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_68 x_a0, EoCases.__smtx_typeof.case_69 x_a0, EoCases.__smtx_typeof.case_70 x_a0, EoCases.__smtx_typeof.case_71 x_a0] = [] ++ [EoCases.__smtx_typeof.case_68 x_a0] ++ [EoCases.__smtx_typeof.case_69 x_a0, EoCases.__smtx_typeof.case_70 x_a0, EoCases.__smtx_typeof.case_71 x_a0] from rfl)
    otherwise ⟨hl_68⟩ using
  group_round_step with case_69_eo__24smtx_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_68 x_a0, EoCases.__smtx_typeof.case_69 x_a0, EoCases.__smtx_typeof.case_70 x_a0, EoCases.__smtx_typeof.case_71 x_a0] = [EoCases.__smtx_typeof.case_68 x_a0] ++ [EoCases.__smtx_typeof.case_69 x_a0] ++ [EoCases.__smtx_typeof.case_70 x_a0, EoCases.__smtx_typeof.case_71 x_a0] from rfl)
    otherwise ⟨hl_69⟩ using hl_68
  group_round_step with case_70_eo__24smtx_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_68 x_a0, EoCases.__smtx_typeof.case_69 x_a0, EoCases.__smtx_typeof.case_70 x_a0, EoCases.__smtx_typeof.case_71 x_a0] = [EoCases.__smtx_typeof.case_68 x_a0, EoCases.__smtx_typeof.case_69 x_a0] ++ [EoCases.__smtx_typeof.case_70 x_a0] ++ [EoCases.__smtx_typeof.case_71 x_a0] from rfl)
    otherwise ⟨hl_70⟩ using hl_68 hl_69
  group_round_step with case_71_eo__24smtx_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_68 x_a0, EoCases.__smtx_typeof.case_69 x_a0, EoCases.__smtx_typeof.case_70 x_a0, EoCases.__smtx_typeof.case_71 x_a0] = [EoCases.__smtx_typeof.case_68 x_a0, EoCases.__smtx_typeof.case_69 x_a0, EoCases.__smtx_typeof.case_70 x_a0] ++ [EoCases.__smtx_typeof.case_71 x_a0] ++ [] from rfl)
    otherwise ⟨hl_71⟩ using hl_68 hl_69 hl_70
  group_none hinv4 hG with ⟨hl_68, hl_69, hl_70, hl_71⟩

theorem cases_0_18_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_18_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, (∀ d, firstSome [EoCases.__smtx_typeof.case_72 x_a0, EoCases.__smtx_typeof.case_73 x_a0, EoCases.__smtx_typeof.case_74 x_a0, EoCases.__smtx_typeof.case_75 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          ∀ d, firstSome [EoCases.__smtx_typeof.case_72 x_a0, EoCases.__smtx_typeof.case_73 x_a0, EoCases.__smtx_typeof.case_74 x_a0, EoCases.__smtx_typeof.case_75 x_a0] d = __smtx_typeof y0
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_72 x_a0 = none ∧ EoCases.__smtx_typeof.case_73 x_a0 = none ∧ EoCases.__smtx_typeof.case_74 x_a0 = none ∧ EoCases.__smtx_typeof.case_75 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_18_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  group_round_step with case_72_eo__24smtx_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_72 x_a0, EoCases.__smtx_typeof.case_73 x_a0, EoCases.__smtx_typeof.case_74 x_a0, EoCases.__smtx_typeof.case_75 x_a0] = [] ++ [EoCases.__smtx_typeof.case_72 x_a0] ++ [EoCases.__smtx_typeof.case_73 x_a0, EoCases.__smtx_typeof.case_74 x_a0, EoCases.__smtx_typeof.case_75 x_a0] from rfl)
    otherwise ⟨hl_72⟩ using
  group_round_step with case_73_eo__24smtx_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_72 x_a0, EoCases.__smtx_typeof.case_73 x_a0, EoCases.__smtx_typeof.case_74 x_a0, EoCases.__smtx_typeof.case_75 x_a0] = [EoCases.__smtx_typeof.case_72 x_a0] ++ [EoCases.__smtx_typeof.case_73 x_a0] ++ [EoCases.__smtx_typeof.case_74 x_a0, EoCases.__smtx_typeof.case_75 x_a0] from rfl)
    otherwise ⟨hl_73⟩ using hl_72
  group_round_step with case_74_eo__24smtx_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_72 x_a0, EoCases.__smtx_typeof.case_73 x_a0, EoCases.__smtx_typeof.case_74 x_a0, EoCases.__smtx_typeof.case_75 x_a0] = [EoCases.__smtx_typeof.case_72 x_a0, EoCases.__smtx_typeof.case_73 x_a0] ++ [EoCases.__smtx_typeof.case_74 x_a0] ++ [EoCases.__smtx_typeof.case_75 x_a0] from rfl)
    otherwise ⟨hl_74⟩ using hl_72 hl_73
  group_round_step with case_75_eo__24smtx_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_72 x_a0, EoCases.__smtx_typeof.case_73 x_a0, EoCases.__smtx_typeof.case_74 x_a0, EoCases.__smtx_typeof.case_75 x_a0] = [EoCases.__smtx_typeof.case_72 x_a0, EoCases.__smtx_typeof.case_73 x_a0, EoCases.__smtx_typeof.case_74 x_a0] ++ [EoCases.__smtx_typeof.case_75 x_a0] ++ [] from rfl)
    otherwise ⟨hl_75⟩ using hl_72 hl_73 hl_74
  group_none hinv4 hG with ⟨hl_72, hl_73, hl_74, hl_75⟩

theorem cases_0_19_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_19_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, (∀ d, firstSome [EoCases.__smtx_typeof.case_76 x_a0, EoCases.__smtx_typeof.case_77 x_a0, EoCases.__smtx_typeof.case_78 x_a0, EoCases.__smtx_typeof.case_79 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          ∀ d, firstSome [EoCases.__smtx_typeof.case_76 x_a0, EoCases.__smtx_typeof.case_77 x_a0, EoCases.__smtx_typeof.case_78 x_a0, EoCases.__smtx_typeof.case_79 x_a0] d = __smtx_typeof y0
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_76 x_a0 = none ∧ EoCases.__smtx_typeof.case_77 x_a0 = none ∧ EoCases.__smtx_typeof.case_78 x_a0 = none ∧ EoCases.__smtx_typeof.case_79 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_19_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  group_round_step with case_76_eo__24smtx_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_76 x_a0, EoCases.__smtx_typeof.case_77 x_a0, EoCases.__smtx_typeof.case_78 x_a0, EoCases.__smtx_typeof.case_79 x_a0] = [] ++ [EoCases.__smtx_typeof.case_76 x_a0] ++ [EoCases.__smtx_typeof.case_77 x_a0, EoCases.__smtx_typeof.case_78 x_a0, EoCases.__smtx_typeof.case_79 x_a0] from rfl)
    otherwise ⟨hl_76⟩ using
  group_round_step with case_77_eo__24smtx_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_76 x_a0, EoCases.__smtx_typeof.case_77 x_a0, EoCases.__smtx_typeof.case_78 x_a0, EoCases.__smtx_typeof.case_79 x_a0] = [EoCases.__smtx_typeof.case_76 x_a0] ++ [EoCases.__smtx_typeof.case_77 x_a0] ++ [EoCases.__smtx_typeof.case_78 x_a0, EoCases.__smtx_typeof.case_79 x_a0] from rfl)
    otherwise ⟨hl_77⟩ using hl_76
  group_round_step with case_78_eo__24smtx_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_76 x_a0, EoCases.__smtx_typeof.case_77 x_a0, EoCases.__smtx_typeof.case_78 x_a0, EoCases.__smtx_typeof.case_79 x_a0] = [EoCases.__smtx_typeof.case_76 x_a0, EoCases.__smtx_typeof.case_77 x_a0] ++ [EoCases.__smtx_typeof.case_78 x_a0] ++ [EoCases.__smtx_typeof.case_79 x_a0] from rfl)
    otherwise ⟨hl_78⟩ using hl_76 hl_77
  group_round_step with case_79_eo__24smtx_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_76 x_a0, EoCases.__smtx_typeof.case_77 x_a0, EoCases.__smtx_typeof.case_78 x_a0, EoCases.__smtx_typeof.case_79 x_a0] = [EoCases.__smtx_typeof.case_76 x_a0, EoCases.__smtx_typeof.case_77 x_a0, EoCases.__smtx_typeof.case_78 x_a0] ++ [EoCases.__smtx_typeof.case_79 x_a0] ++ [] from rfl)
    otherwise ⟨hl_79⟩ using hl_76 hl_77 hl_78
  group_none hinv4 hG with ⟨hl_76, hl_77, hl_78, hl_79⟩

theorem cases_0_20_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_20_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, (∀ d, firstSome [EoCases.__smtx_typeof.case_80 x_a0, EoCases.__smtx_typeof.case_81 x_a0, EoCases.__smtx_typeof.case_82 x_a0, EoCases.__smtx_typeof.case_83 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          ∀ d, firstSome [EoCases.__smtx_typeof.case_80 x_a0, EoCases.__smtx_typeof.case_81 x_a0, EoCases.__smtx_typeof.case_82 x_a0, EoCases.__smtx_typeof.case_83 x_a0] d = __smtx_typeof y0
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_80 x_a0 = none ∧ EoCases.__smtx_typeof.case_81 x_a0 = none ∧ EoCases.__smtx_typeof.case_82 x_a0 = none ∧ EoCases.__smtx_typeof.case_83 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_20_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  group_round_step with case_80_eo__24smtx_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_80 x_a0, EoCases.__smtx_typeof.case_81 x_a0, EoCases.__smtx_typeof.case_82 x_a0, EoCases.__smtx_typeof.case_83 x_a0] = [] ++ [EoCases.__smtx_typeof.case_80 x_a0] ++ [EoCases.__smtx_typeof.case_81 x_a0, EoCases.__smtx_typeof.case_82 x_a0, EoCases.__smtx_typeof.case_83 x_a0] from rfl)
    otherwise ⟨hl_80⟩ using
  group_round_step with case_81_eo__24smtx_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_80 x_a0, EoCases.__smtx_typeof.case_81 x_a0, EoCases.__smtx_typeof.case_82 x_a0, EoCases.__smtx_typeof.case_83 x_a0] = [EoCases.__smtx_typeof.case_80 x_a0] ++ [EoCases.__smtx_typeof.case_81 x_a0] ++ [EoCases.__smtx_typeof.case_82 x_a0, EoCases.__smtx_typeof.case_83 x_a0] from rfl)
    otherwise ⟨hl_81⟩ using hl_80
  group_round_step with case_82_eo__24smtx_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_80 x_a0, EoCases.__smtx_typeof.case_81 x_a0, EoCases.__smtx_typeof.case_82 x_a0, EoCases.__smtx_typeof.case_83 x_a0] = [EoCases.__smtx_typeof.case_80 x_a0, EoCases.__smtx_typeof.case_81 x_a0] ++ [EoCases.__smtx_typeof.case_82 x_a0] ++ [EoCases.__smtx_typeof.case_83 x_a0] from rfl)
    otherwise ⟨hl_82⟩ using hl_80 hl_81
  group_round_step with case_83_eo__24smtx_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_80 x_a0, EoCases.__smtx_typeof.case_81 x_a0, EoCases.__smtx_typeof.case_82 x_a0, EoCases.__smtx_typeof.case_83 x_a0] = [EoCases.__smtx_typeof.case_80 x_a0, EoCases.__smtx_typeof.case_81 x_a0, EoCases.__smtx_typeof.case_82 x_a0] ++ [EoCases.__smtx_typeof.case_83 x_a0] ++ [] from rfl)
    otherwise ⟨hl_83⟩ using hl_80 hl_81 hl_82
  group_none hinv4 hG with ⟨hl_80, hl_81, hl_82, hl_83⟩

theorem cases_0_21_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_21_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, (∀ d, firstSome [EoCases.__smtx_typeof.case_84 x_a0, EoCases.__smtx_typeof.case_85 x_a0, EoCases.__smtx_typeof.case_86 x_a0, EoCases.__smtx_typeof.case_87 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          ∀ d, firstSome [EoCases.__smtx_typeof.case_84 x_a0, EoCases.__smtx_typeof.case_85 x_a0, EoCases.__smtx_typeof.case_86 x_a0, EoCases.__smtx_typeof.case_87 x_a0] d = __smtx_typeof y0
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_84 x_a0 = none ∧ EoCases.__smtx_typeof.case_85 x_a0 = none ∧ EoCases.__smtx_typeof.case_86 x_a0 = none ∧ EoCases.__smtx_typeof.case_87 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_21_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  group_round_step with case_84_eo__24smtx_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_84 x_a0, EoCases.__smtx_typeof.case_85 x_a0, EoCases.__smtx_typeof.case_86 x_a0, EoCases.__smtx_typeof.case_87 x_a0] = [] ++ [EoCases.__smtx_typeof.case_84 x_a0] ++ [EoCases.__smtx_typeof.case_85 x_a0, EoCases.__smtx_typeof.case_86 x_a0, EoCases.__smtx_typeof.case_87 x_a0] from rfl)
    otherwise ⟨hl_84⟩ using
  group_round_step with case_85_eo__24smtx_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_84 x_a0, EoCases.__smtx_typeof.case_85 x_a0, EoCases.__smtx_typeof.case_86 x_a0, EoCases.__smtx_typeof.case_87 x_a0] = [EoCases.__smtx_typeof.case_84 x_a0] ++ [EoCases.__smtx_typeof.case_85 x_a0] ++ [EoCases.__smtx_typeof.case_86 x_a0, EoCases.__smtx_typeof.case_87 x_a0] from rfl)
    otherwise ⟨hl_85⟩ using hl_84
  group_round_step with case_86_eo__24smtx_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_84 x_a0, EoCases.__smtx_typeof.case_85 x_a0, EoCases.__smtx_typeof.case_86 x_a0, EoCases.__smtx_typeof.case_87 x_a0] = [EoCases.__smtx_typeof.case_84 x_a0, EoCases.__smtx_typeof.case_85 x_a0] ++ [EoCases.__smtx_typeof.case_86 x_a0] ++ [EoCases.__smtx_typeof.case_87 x_a0] from rfl)
    otherwise ⟨hl_86⟩ using hl_84 hl_85
  group_round_step with case_87_eo__24smtx_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_84 x_a0, EoCases.__smtx_typeof.case_85 x_a0, EoCases.__smtx_typeof.case_86 x_a0, EoCases.__smtx_typeof.case_87 x_a0] = [EoCases.__smtx_typeof.case_84 x_a0, EoCases.__smtx_typeof.case_85 x_a0, EoCases.__smtx_typeof.case_86 x_a0] ++ [EoCases.__smtx_typeof.case_87 x_a0] ++ [] from rfl)
    otherwise ⟨hl_87⟩ using hl_84 hl_85 hl_86
  group_none hinv4 hG with ⟨hl_84, hl_85, hl_86, hl_87⟩

theorem cases_0_22_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_22_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, (∀ d, firstSome [EoCases.__smtx_typeof.case_88 x_a0, EoCases.__smtx_typeof.case_89 x_a0, EoCases.__smtx_typeof.case_90 x_a0, EoCases.__smtx_typeof.case_91 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          ∀ d, firstSome [EoCases.__smtx_typeof.case_88 x_a0, EoCases.__smtx_typeof.case_89 x_a0, EoCases.__smtx_typeof.case_90 x_a0, EoCases.__smtx_typeof.case_91 x_a0] d = __smtx_typeof y0
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_88 x_a0 = none ∧ EoCases.__smtx_typeof.case_89 x_a0 = none ∧ EoCases.__smtx_typeof.case_90 x_a0 = none ∧ EoCases.__smtx_typeof.case_91 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_22_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  group_round_step with case_88_eo__24smtx_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_88 x_a0, EoCases.__smtx_typeof.case_89 x_a0, EoCases.__smtx_typeof.case_90 x_a0, EoCases.__smtx_typeof.case_91 x_a0] = [] ++ [EoCases.__smtx_typeof.case_88 x_a0] ++ [EoCases.__smtx_typeof.case_89 x_a0, EoCases.__smtx_typeof.case_90 x_a0, EoCases.__smtx_typeof.case_91 x_a0] from rfl)
    otherwise ⟨hl_88⟩ using
  group_round_step with case_89_eo__24smtx_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_88 x_a0, EoCases.__smtx_typeof.case_89 x_a0, EoCases.__smtx_typeof.case_90 x_a0, EoCases.__smtx_typeof.case_91 x_a0] = [EoCases.__smtx_typeof.case_88 x_a0] ++ [EoCases.__smtx_typeof.case_89 x_a0] ++ [EoCases.__smtx_typeof.case_90 x_a0, EoCases.__smtx_typeof.case_91 x_a0] from rfl)
    otherwise ⟨hl_89⟩ using hl_88
  group_round_step with case_90_eo__24smtx_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_88 x_a0, EoCases.__smtx_typeof.case_89 x_a0, EoCases.__smtx_typeof.case_90 x_a0, EoCases.__smtx_typeof.case_91 x_a0] = [EoCases.__smtx_typeof.case_88 x_a0, EoCases.__smtx_typeof.case_89 x_a0] ++ [EoCases.__smtx_typeof.case_90 x_a0] ++ [EoCases.__smtx_typeof.case_91 x_a0] from rfl)
    otherwise ⟨hl_90⟩ using hl_88 hl_89
  group_round_step with case_91_eo__24smtx_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_88 x_a0, EoCases.__smtx_typeof.case_89 x_a0, EoCases.__smtx_typeof.case_90 x_a0, EoCases.__smtx_typeof.case_91 x_a0] = [EoCases.__smtx_typeof.case_88 x_a0, EoCases.__smtx_typeof.case_89 x_a0, EoCases.__smtx_typeof.case_90 x_a0] ++ [EoCases.__smtx_typeof.case_91 x_a0] ++ [] from rfl)
    otherwise ⟨hl_91⟩ using hl_88 hl_89 hl_90
  group_none hinv4 hG with ⟨hl_88, hl_89, hl_90, hl_91⟩

theorem cases_0_23_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_23_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, (∀ d, firstSome [EoCases.__smtx_typeof.case_92 x_a0, EoCases.__smtx_typeof.case_93 x_a0, EoCases.__smtx_typeof.case_94 x_a0, EoCases.__smtx_typeof.case_95 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          ∀ d, firstSome [EoCases.__smtx_typeof.case_92 x_a0, EoCases.__smtx_typeof.case_93 x_a0, EoCases.__smtx_typeof.case_94 x_a0, EoCases.__smtx_typeof.case_95 x_a0] d = __smtx_typeof y0
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_92 x_a0 = none ∧ EoCases.__smtx_typeof.case_93 x_a0 = none ∧ EoCases.__smtx_typeof.case_94 x_a0 = none ∧ EoCases.__smtx_typeof.case_95 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_23_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  group_round_step with case_92_eo__24smtx_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_92 x_a0, EoCases.__smtx_typeof.case_93 x_a0, EoCases.__smtx_typeof.case_94 x_a0, EoCases.__smtx_typeof.case_95 x_a0] = [] ++ [EoCases.__smtx_typeof.case_92 x_a0] ++ [EoCases.__smtx_typeof.case_93 x_a0, EoCases.__smtx_typeof.case_94 x_a0, EoCases.__smtx_typeof.case_95 x_a0] from rfl)
    otherwise ⟨hl_92⟩ using
  group_round_step with case_93_eo__24smtx_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_92 x_a0, EoCases.__smtx_typeof.case_93 x_a0, EoCases.__smtx_typeof.case_94 x_a0, EoCases.__smtx_typeof.case_95 x_a0] = [EoCases.__smtx_typeof.case_92 x_a0] ++ [EoCases.__smtx_typeof.case_93 x_a0] ++ [EoCases.__smtx_typeof.case_94 x_a0, EoCases.__smtx_typeof.case_95 x_a0] from rfl)
    otherwise ⟨hl_93⟩ using hl_92
  group_round_step with case_94_eo__24smtx_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_92 x_a0, EoCases.__smtx_typeof.case_93 x_a0, EoCases.__smtx_typeof.case_94 x_a0, EoCases.__smtx_typeof.case_95 x_a0] = [EoCases.__smtx_typeof.case_92 x_a0, EoCases.__smtx_typeof.case_93 x_a0] ++ [EoCases.__smtx_typeof.case_94 x_a0] ++ [EoCases.__smtx_typeof.case_95 x_a0] from rfl)
    otherwise ⟨hl_94⟩ using hl_92 hl_93
  group_round_step with case_95_eo__24smtx_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_92 x_a0, EoCases.__smtx_typeof.case_93 x_a0, EoCases.__smtx_typeof.case_94 x_a0, EoCases.__smtx_typeof.case_95 x_a0] = [EoCases.__smtx_typeof.case_92 x_a0, EoCases.__smtx_typeof.case_93 x_a0, EoCases.__smtx_typeof.case_94 x_a0] ++ [EoCases.__smtx_typeof.case_95 x_a0] ++ [] from rfl)
    otherwise ⟨hl_95⟩ using hl_92 hl_93 hl_94
  group_none hinv4 hG with ⟨hl_92, hl_93, hl_94, hl_95⟩

theorem cases_0_24_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_24_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, (∀ d, firstSome [EoCases.__smtx_typeof.case_96 x_a0, EoCases.__smtx_typeof.case_97 x_a0, EoCases.__smtx_typeof.case_98 x_a0, EoCases.__smtx_typeof.case_99 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          ∀ d, firstSome [EoCases.__smtx_typeof.case_96 x_a0, EoCases.__smtx_typeof.case_97 x_a0, EoCases.__smtx_typeof.case_98 x_a0, EoCases.__smtx_typeof.case_99 x_a0] d = __smtx_typeof y0
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_96 x_a0 = none ∧ EoCases.__smtx_typeof.case_97 x_a0 = none ∧ EoCases.__smtx_typeof.case_98 x_a0 = none ∧ EoCases.__smtx_typeof.case_99 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_24_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  group_round_step with case_96_eo__24smtx_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_96 x_a0, EoCases.__smtx_typeof.case_97 x_a0, EoCases.__smtx_typeof.case_98 x_a0, EoCases.__smtx_typeof.case_99 x_a0] = [] ++ [EoCases.__smtx_typeof.case_96 x_a0] ++ [EoCases.__smtx_typeof.case_97 x_a0, EoCases.__smtx_typeof.case_98 x_a0, EoCases.__smtx_typeof.case_99 x_a0] from rfl)
    otherwise ⟨hl_96⟩ using
  group_round_step with case_97_eo__24smtx_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_96 x_a0, EoCases.__smtx_typeof.case_97 x_a0, EoCases.__smtx_typeof.case_98 x_a0, EoCases.__smtx_typeof.case_99 x_a0] = [EoCases.__smtx_typeof.case_96 x_a0] ++ [EoCases.__smtx_typeof.case_97 x_a0] ++ [EoCases.__smtx_typeof.case_98 x_a0, EoCases.__smtx_typeof.case_99 x_a0] from rfl)
    otherwise ⟨hl_97⟩ using hl_96
  group_round_step with case_98_eo__24smtx_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_96 x_a0, EoCases.__smtx_typeof.case_97 x_a0, EoCases.__smtx_typeof.case_98 x_a0, EoCases.__smtx_typeof.case_99 x_a0] = [EoCases.__smtx_typeof.case_96 x_a0, EoCases.__smtx_typeof.case_97 x_a0] ++ [EoCases.__smtx_typeof.case_98 x_a0] ++ [EoCases.__smtx_typeof.case_99 x_a0] from rfl)
    otherwise ⟨hl_98⟩ using hl_96 hl_97
  group_round_step with case_99_eo__24smtx_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_96 x_a0, EoCases.__smtx_typeof.case_97 x_a0, EoCases.__smtx_typeof.case_98 x_a0, EoCases.__smtx_typeof.case_99 x_a0] = [EoCases.__smtx_typeof.case_96 x_a0, EoCases.__smtx_typeof.case_97 x_a0, EoCases.__smtx_typeof.case_98 x_a0] ++ [EoCases.__smtx_typeof.case_99 x_a0] ++ [] from rfl)
    otherwise ⟨hl_99⟩ using hl_96 hl_97 hl_98
  group_none hinv4 hG with ⟨hl_96, hl_97, hl_98, hl_99⟩

theorem cases_0_25_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_25_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, (∀ d, firstSome [EoCases.__smtx_typeof.case_100 x_a0, EoCases.__smtx_typeof.case_101 x_a0, EoCases.__smtx_typeof.case_102 x_a0, EoCases.__smtx_typeof.case_103 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          ∀ d, firstSome [EoCases.__smtx_typeof.case_100 x_a0, EoCases.__smtx_typeof.case_101 x_a0, EoCases.__smtx_typeof.case_102 x_a0, EoCases.__smtx_typeof.case_103 x_a0] d = __smtx_typeof y0
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_100 x_a0 = none ∧ EoCases.__smtx_typeof.case_101 x_a0 = none ∧ EoCases.__smtx_typeof.case_102 x_a0 = none ∧ EoCases.__smtx_typeof.case_103 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_25_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  group_round_step with case_100_eo__24smtx_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_100 x_a0, EoCases.__smtx_typeof.case_101 x_a0, EoCases.__smtx_typeof.case_102 x_a0, EoCases.__smtx_typeof.case_103 x_a0] = [] ++ [EoCases.__smtx_typeof.case_100 x_a0] ++ [EoCases.__smtx_typeof.case_101 x_a0, EoCases.__smtx_typeof.case_102 x_a0, EoCases.__smtx_typeof.case_103 x_a0] from rfl)
    otherwise ⟨hl_100⟩ using
  group_round_step with case_101_eo__24smtx_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_100 x_a0, EoCases.__smtx_typeof.case_101 x_a0, EoCases.__smtx_typeof.case_102 x_a0, EoCases.__smtx_typeof.case_103 x_a0] = [EoCases.__smtx_typeof.case_100 x_a0] ++ [EoCases.__smtx_typeof.case_101 x_a0] ++ [EoCases.__smtx_typeof.case_102 x_a0, EoCases.__smtx_typeof.case_103 x_a0] from rfl)
    otherwise ⟨hl_101⟩ using hl_100
  group_round_step with case_102_eo__24smtx_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_100 x_a0, EoCases.__smtx_typeof.case_101 x_a0, EoCases.__smtx_typeof.case_102 x_a0, EoCases.__smtx_typeof.case_103 x_a0] = [EoCases.__smtx_typeof.case_100 x_a0, EoCases.__smtx_typeof.case_101 x_a0] ++ [EoCases.__smtx_typeof.case_102 x_a0] ++ [EoCases.__smtx_typeof.case_103 x_a0] from rfl)
    otherwise ⟨hl_102⟩ using hl_100 hl_101
  group_round_step with case_103_eo__24smtx_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_100 x_a0, EoCases.__smtx_typeof.case_101 x_a0, EoCases.__smtx_typeof.case_102 x_a0, EoCases.__smtx_typeof.case_103 x_a0] = [EoCases.__smtx_typeof.case_100 x_a0, EoCases.__smtx_typeof.case_101 x_a0, EoCases.__smtx_typeof.case_102 x_a0] ++ [EoCases.__smtx_typeof.case_103 x_a0] ++ [] from rfl)
    otherwise ⟨hl_103⟩ using hl_100 hl_101 hl_102
  group_none hinv4 hG with ⟨hl_100, hl_101, hl_102, hl_103⟩

theorem cases_0_26_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_26_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, (∀ d, firstSome [EoCases.__smtx_typeof.case_104 x_a0, EoCases.__smtx_typeof.case_105 x_a0, EoCases.__smtx_typeof.case_106 x_a0, EoCases.__smtx_typeof.case_107 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          ∀ d, firstSome [EoCases.__smtx_typeof.case_104 x_a0, EoCases.__smtx_typeof.case_105 x_a0, EoCases.__smtx_typeof.case_106 x_a0, EoCases.__smtx_typeof.case_107 x_a0] d = __smtx_typeof y0
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_104 x_a0 = none ∧ EoCases.__smtx_typeof.case_105 x_a0 = none ∧ EoCases.__smtx_typeof.case_106 x_a0 = none ∧ EoCases.__smtx_typeof.case_107 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_26_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  group_round_step with case_104_eo__24smtx_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_104 x_a0, EoCases.__smtx_typeof.case_105 x_a0, EoCases.__smtx_typeof.case_106 x_a0, EoCases.__smtx_typeof.case_107 x_a0] = [] ++ [EoCases.__smtx_typeof.case_104 x_a0] ++ [EoCases.__smtx_typeof.case_105 x_a0, EoCases.__smtx_typeof.case_106 x_a0, EoCases.__smtx_typeof.case_107 x_a0] from rfl)
    otherwise ⟨hl_104⟩ using
  group_round_step with case_105_eo__24smtx_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_104 x_a0, EoCases.__smtx_typeof.case_105 x_a0, EoCases.__smtx_typeof.case_106 x_a0, EoCases.__smtx_typeof.case_107 x_a0] = [EoCases.__smtx_typeof.case_104 x_a0] ++ [EoCases.__smtx_typeof.case_105 x_a0] ++ [EoCases.__smtx_typeof.case_106 x_a0, EoCases.__smtx_typeof.case_107 x_a0] from rfl)
    otherwise ⟨hl_105⟩ using hl_104
  group_round_step with case_106_eo__24smtx_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_104 x_a0, EoCases.__smtx_typeof.case_105 x_a0, EoCases.__smtx_typeof.case_106 x_a0, EoCases.__smtx_typeof.case_107 x_a0] = [EoCases.__smtx_typeof.case_104 x_a0, EoCases.__smtx_typeof.case_105 x_a0] ++ [EoCases.__smtx_typeof.case_106 x_a0] ++ [EoCases.__smtx_typeof.case_107 x_a0] from rfl)
    otherwise ⟨hl_106⟩ using hl_104 hl_105
  group_round_step with case_107_eo__24smtx_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_104 x_a0, EoCases.__smtx_typeof.case_105 x_a0, EoCases.__smtx_typeof.case_106 x_a0, EoCases.__smtx_typeof.case_107 x_a0] = [EoCases.__smtx_typeof.case_104 x_a0, EoCases.__smtx_typeof.case_105 x_a0, EoCases.__smtx_typeof.case_106 x_a0] ++ [EoCases.__smtx_typeof.case_107 x_a0] ++ [] from rfl)
    otherwise ⟨hl_107⟩ using hl_104 hl_105 hl_106
  group_none hinv4 hG with ⟨hl_104, hl_105, hl_106, hl_107⟩

theorem cases_0_27_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_27_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, (∀ d, firstSome [EoCases.__smtx_typeof.case_108 x_a0, EoCases.__smtx_typeof.case_109 x_a0, EoCases.__smtx_typeof.case_110 x_a0, EoCases.__smtx_typeof.case_111 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          ∀ d, firstSome [EoCases.__smtx_typeof.case_108 x_a0, EoCases.__smtx_typeof.case_109 x_a0, EoCases.__smtx_typeof.case_110 x_a0, EoCases.__smtx_typeof.case_111 x_a0] d = __smtx_typeof y0
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_108 x_a0 = none ∧ EoCases.__smtx_typeof.case_109 x_a0 = none ∧ EoCases.__smtx_typeof.case_110 x_a0 = none ∧ EoCases.__smtx_typeof.case_111 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_27_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  group_round_step with case_108_eo__24smtx_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_108 x_a0, EoCases.__smtx_typeof.case_109 x_a0, EoCases.__smtx_typeof.case_110 x_a0, EoCases.__smtx_typeof.case_111 x_a0] = [] ++ [EoCases.__smtx_typeof.case_108 x_a0] ++ [EoCases.__smtx_typeof.case_109 x_a0, EoCases.__smtx_typeof.case_110 x_a0, EoCases.__smtx_typeof.case_111 x_a0] from rfl)
    otherwise ⟨hl_108⟩ using
  group_round_step with case_109_eo__24smtx_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_108 x_a0, EoCases.__smtx_typeof.case_109 x_a0, EoCases.__smtx_typeof.case_110 x_a0, EoCases.__smtx_typeof.case_111 x_a0] = [EoCases.__smtx_typeof.case_108 x_a0] ++ [EoCases.__smtx_typeof.case_109 x_a0] ++ [EoCases.__smtx_typeof.case_110 x_a0, EoCases.__smtx_typeof.case_111 x_a0] from rfl)
    otherwise ⟨hl_109⟩ using hl_108
  group_round_step with case_110_eo__24smtx_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_108 x_a0, EoCases.__smtx_typeof.case_109 x_a0, EoCases.__smtx_typeof.case_110 x_a0, EoCases.__smtx_typeof.case_111 x_a0] = [EoCases.__smtx_typeof.case_108 x_a0, EoCases.__smtx_typeof.case_109 x_a0] ++ [EoCases.__smtx_typeof.case_110 x_a0] ++ [EoCases.__smtx_typeof.case_111 x_a0] from rfl)
    otherwise ⟨hl_110⟩ using hl_108 hl_109
  group_round_step with case_111_eo__24smtx_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_108 x_a0, EoCases.__smtx_typeof.case_109 x_a0, EoCases.__smtx_typeof.case_110 x_a0, EoCases.__smtx_typeof.case_111 x_a0] = [EoCases.__smtx_typeof.case_108 x_a0, EoCases.__smtx_typeof.case_109 x_a0, EoCases.__smtx_typeof.case_110 x_a0] ++ [EoCases.__smtx_typeof.case_111 x_a0] ++ [] from rfl)
    otherwise ⟨hl_111⟩ using hl_108 hl_109 hl_110
  group_none hinv4 hG with ⟨hl_108, hl_109, hl_110, hl_111⟩

theorem cases_0_28_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_28_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, (∀ d, firstSome [EoCases.__smtx_typeof.case_112 x_a0, EoCases.__smtx_typeof.case_113 x_a0, EoCases.__smtx_typeof.case_114 x_a0, EoCases.__smtx_typeof.case_115 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          ∀ d, firstSome [EoCases.__smtx_typeof.case_112 x_a0, EoCases.__smtx_typeof.case_113 x_a0, EoCases.__smtx_typeof.case_114 x_a0, EoCases.__smtx_typeof.case_115 x_a0] d = __smtx_typeof y0
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_112 x_a0 = none ∧ EoCases.__smtx_typeof.case_113 x_a0 = none ∧ EoCases.__smtx_typeof.case_114 x_a0 = none ∧ EoCases.__smtx_typeof.case_115 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_28_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  group_round_step with case_112_eo__24smtx_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_112 x_a0, EoCases.__smtx_typeof.case_113 x_a0, EoCases.__smtx_typeof.case_114 x_a0, EoCases.__smtx_typeof.case_115 x_a0] = [] ++ [EoCases.__smtx_typeof.case_112 x_a0] ++ [EoCases.__smtx_typeof.case_113 x_a0, EoCases.__smtx_typeof.case_114 x_a0, EoCases.__smtx_typeof.case_115 x_a0] from rfl)
    otherwise ⟨hl_112⟩ using
  group_round_step with case_113_eo__24smtx_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_112 x_a0, EoCases.__smtx_typeof.case_113 x_a0, EoCases.__smtx_typeof.case_114 x_a0, EoCases.__smtx_typeof.case_115 x_a0] = [EoCases.__smtx_typeof.case_112 x_a0] ++ [EoCases.__smtx_typeof.case_113 x_a0] ++ [EoCases.__smtx_typeof.case_114 x_a0, EoCases.__smtx_typeof.case_115 x_a0] from rfl)
    otherwise ⟨hl_113⟩ using hl_112
  group_round_step with case_114_eo__24smtx_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_112 x_a0, EoCases.__smtx_typeof.case_113 x_a0, EoCases.__smtx_typeof.case_114 x_a0, EoCases.__smtx_typeof.case_115 x_a0] = [EoCases.__smtx_typeof.case_112 x_a0, EoCases.__smtx_typeof.case_113 x_a0] ++ [EoCases.__smtx_typeof.case_114 x_a0] ++ [EoCases.__smtx_typeof.case_115 x_a0] from rfl)
    otherwise ⟨hl_114⟩ using hl_112 hl_113
  group_round_step with case_115_eo__24smtx_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_112 x_a0, EoCases.__smtx_typeof.case_113 x_a0, EoCases.__smtx_typeof.case_114 x_a0, EoCases.__smtx_typeof.case_115 x_a0] = [EoCases.__smtx_typeof.case_112 x_a0, EoCases.__smtx_typeof.case_113 x_a0, EoCases.__smtx_typeof.case_114 x_a0] ++ [EoCases.__smtx_typeof.case_115 x_a0] ++ [] from rfl)
    otherwise ⟨hl_115⟩ using hl_112 hl_113 hl_114
  group_none hinv4 hG with ⟨hl_112, hl_113, hl_114, hl_115⟩

theorem cases_0_29_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_29_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, (∀ d, firstSome [EoCases.__smtx_typeof.case_116 x_a0, EoCases.__smtx_typeof.case_117 x_a0, EoCases.__smtx_typeof.case_118 x_a0, EoCases.__smtx_typeof.case_119 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          ∀ d, firstSome [EoCases.__smtx_typeof.case_116 x_a0, EoCases.__smtx_typeof.case_117 x_a0, EoCases.__smtx_typeof.case_118 x_a0, EoCases.__smtx_typeof.case_119 x_a0] d = __smtx_typeof y0
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_116 x_a0 = none ∧ EoCases.__smtx_typeof.case_117 x_a0 = none ∧ EoCases.__smtx_typeof.case_118 x_a0 = none ∧ EoCases.__smtx_typeof.case_119 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_29_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  group_round_step with case_116_eo__24smtx_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_116 x_a0, EoCases.__smtx_typeof.case_117 x_a0, EoCases.__smtx_typeof.case_118 x_a0, EoCases.__smtx_typeof.case_119 x_a0] = [] ++ [EoCases.__smtx_typeof.case_116 x_a0] ++ [EoCases.__smtx_typeof.case_117 x_a0, EoCases.__smtx_typeof.case_118 x_a0, EoCases.__smtx_typeof.case_119 x_a0] from rfl)
    otherwise ⟨hl_116⟩ using
  group_round_step with case_117_eo__24smtx_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_116 x_a0, EoCases.__smtx_typeof.case_117 x_a0, EoCases.__smtx_typeof.case_118 x_a0, EoCases.__smtx_typeof.case_119 x_a0] = [EoCases.__smtx_typeof.case_116 x_a0] ++ [EoCases.__smtx_typeof.case_117 x_a0] ++ [EoCases.__smtx_typeof.case_118 x_a0, EoCases.__smtx_typeof.case_119 x_a0] from rfl)
    otherwise ⟨hl_117⟩ using hl_116
  group_round_step with case_118_eo__24smtx_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_116 x_a0, EoCases.__smtx_typeof.case_117 x_a0, EoCases.__smtx_typeof.case_118 x_a0, EoCases.__smtx_typeof.case_119 x_a0] = [EoCases.__smtx_typeof.case_116 x_a0, EoCases.__smtx_typeof.case_117 x_a0] ++ [EoCases.__smtx_typeof.case_118 x_a0] ++ [EoCases.__smtx_typeof.case_119 x_a0] from rfl)
    otherwise ⟨hl_118⟩ using hl_116 hl_117
  group_round_step with case_119_eo__24smtx_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_116 x_a0, EoCases.__smtx_typeof.case_117 x_a0, EoCases.__smtx_typeof.case_118 x_a0, EoCases.__smtx_typeof.case_119 x_a0] = [EoCases.__smtx_typeof.case_116 x_a0, EoCases.__smtx_typeof.case_117 x_a0, EoCases.__smtx_typeof.case_118 x_a0] ++ [EoCases.__smtx_typeof.case_119 x_a0] ++ [] from rfl)
    otherwise ⟨hl_119⟩ using hl_116 hl_117 hl_118
  group_none hinv4 hG with ⟨hl_116, hl_117, hl_118, hl_119⟩

theorem cases_0_30_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_30_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, (∀ d, firstSome [EoCases.__smtx_typeof.case_120 x_a0, EoCases.__smtx_typeof.case_121 x_a0, EoCases.__smtx_typeof.case_122 x_a0, EoCases.__smtx_typeof.case_123 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          ∀ d, firstSome [EoCases.__smtx_typeof.case_120 x_a0, EoCases.__smtx_typeof.case_121 x_a0, EoCases.__smtx_typeof.case_122 x_a0, EoCases.__smtx_typeof.case_123 x_a0] d = __smtx_typeof y0
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_120 x_a0 = none ∧ EoCases.__smtx_typeof.case_121 x_a0 = none ∧ EoCases.__smtx_typeof.case_122 x_a0 = none ∧ EoCases.__smtx_typeof.case_123 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_30_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  group_round_step with case_120_eo__24smtx_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_120 x_a0, EoCases.__smtx_typeof.case_121 x_a0, EoCases.__smtx_typeof.case_122 x_a0, EoCases.__smtx_typeof.case_123 x_a0] = [] ++ [EoCases.__smtx_typeof.case_120 x_a0] ++ [EoCases.__smtx_typeof.case_121 x_a0, EoCases.__smtx_typeof.case_122 x_a0, EoCases.__smtx_typeof.case_123 x_a0] from rfl)
    otherwise ⟨hl_120⟩ using
  group_round_step with case_121_eo__24smtx_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_120 x_a0, EoCases.__smtx_typeof.case_121 x_a0, EoCases.__smtx_typeof.case_122 x_a0, EoCases.__smtx_typeof.case_123 x_a0] = [EoCases.__smtx_typeof.case_120 x_a0] ++ [EoCases.__smtx_typeof.case_121 x_a0] ++ [EoCases.__smtx_typeof.case_122 x_a0, EoCases.__smtx_typeof.case_123 x_a0] from rfl)
    otherwise ⟨hl_121⟩ using hl_120
  group_round_step with case_122_eo__24smtx_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_120 x_a0, EoCases.__smtx_typeof.case_121 x_a0, EoCases.__smtx_typeof.case_122 x_a0, EoCases.__smtx_typeof.case_123 x_a0] = [EoCases.__smtx_typeof.case_120 x_a0, EoCases.__smtx_typeof.case_121 x_a0] ++ [EoCases.__smtx_typeof.case_122 x_a0] ++ [EoCases.__smtx_typeof.case_123 x_a0] from rfl)
    otherwise ⟨hl_122⟩ using hl_120 hl_121
  group_round_step with case_123_eo__24smtx_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_120 x_a0, EoCases.__smtx_typeof.case_121 x_a0, EoCases.__smtx_typeof.case_122 x_a0, EoCases.__smtx_typeof.case_123 x_a0] = [EoCases.__smtx_typeof.case_120 x_a0, EoCases.__smtx_typeof.case_121 x_a0, EoCases.__smtx_typeof.case_122 x_a0] ++ [EoCases.__smtx_typeof.case_123 x_a0] ++ [] from rfl)
    otherwise ⟨hl_123⟩ using hl_120 hl_121 hl_122
  group_none hinv4 hG with ⟨hl_120, hl_121, hl_122, hl_123⟩

theorem cases_0_31_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_31_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, (∀ d, firstSome [EoCases.__smtx_typeof.case_124 x_a0, EoCases.__smtx_typeof.case_125 x_a0, EoCases.__smtx_typeof.case_126 x_a0, EoCases.__smtx_typeof.case_127 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          ∀ d, firstSome [EoCases.__smtx_typeof.case_124 x_a0, EoCases.__smtx_typeof.case_125 x_a0, EoCases.__smtx_typeof.case_126 x_a0, EoCases.__smtx_typeof.case_127 x_a0] d = __smtx_typeof y0
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_124 x_a0 = none ∧ EoCases.__smtx_typeof.case_125 x_a0 = none ∧ EoCases.__smtx_typeof.case_126 x_a0 = none ∧ EoCases.__smtx_typeof.case_127 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_31_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  group_round_step with case_124_eo__24smtx_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_124 x_a0, EoCases.__smtx_typeof.case_125 x_a0, EoCases.__smtx_typeof.case_126 x_a0, EoCases.__smtx_typeof.case_127 x_a0] = [] ++ [EoCases.__smtx_typeof.case_124 x_a0] ++ [EoCases.__smtx_typeof.case_125 x_a0, EoCases.__smtx_typeof.case_126 x_a0, EoCases.__smtx_typeof.case_127 x_a0] from rfl)
    otherwise ⟨hl_124⟩ using
  group_round_step with case_125_eo__24smtx_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_124 x_a0, EoCases.__smtx_typeof.case_125 x_a0, EoCases.__smtx_typeof.case_126 x_a0, EoCases.__smtx_typeof.case_127 x_a0] = [EoCases.__smtx_typeof.case_124 x_a0] ++ [EoCases.__smtx_typeof.case_125 x_a0] ++ [EoCases.__smtx_typeof.case_126 x_a0, EoCases.__smtx_typeof.case_127 x_a0] from rfl)
    otherwise ⟨hl_125⟩ using hl_124
  group_round_step with case_126_eo__24smtx_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_124 x_a0, EoCases.__smtx_typeof.case_125 x_a0, EoCases.__smtx_typeof.case_126 x_a0, EoCases.__smtx_typeof.case_127 x_a0] = [EoCases.__smtx_typeof.case_124 x_a0, EoCases.__smtx_typeof.case_125 x_a0] ++ [EoCases.__smtx_typeof.case_126 x_a0] ++ [EoCases.__smtx_typeof.case_127 x_a0] from rfl)
    otherwise ⟨hl_126⟩ using hl_124 hl_125
  group_round_step with case_127_eo__24smtx_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_124 x_a0, EoCases.__smtx_typeof.case_125 x_a0, EoCases.__smtx_typeof.case_126 x_a0, EoCases.__smtx_typeof.case_127 x_a0] = [EoCases.__smtx_typeof.case_124 x_a0, EoCases.__smtx_typeof.case_125 x_a0, EoCases.__smtx_typeof.case_126 x_a0] ++ [EoCases.__smtx_typeof.case_127 x_a0] ++ [] from rfl)
    otherwise ⟨hl_127⟩ using hl_124 hl_125 hl_126
  group_none hinv4 hG with ⟨hl_124, hl_125, hl_126, hl_127⟩

theorem cases_0_32_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_32_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, (∀ d, firstSome [EoCases.__smtx_typeof.case_128 x_a0, EoCases.__smtx_typeof.case_129 x_a0, EoCases.__smtx_typeof.case_130 x_a0, EoCases.__smtx_typeof.case_131 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          ∀ d, firstSome [EoCases.__smtx_typeof.case_128 x_a0, EoCases.__smtx_typeof.case_129 x_a0, EoCases.__smtx_typeof.case_130 x_a0, EoCases.__smtx_typeof.case_131 x_a0] d = __smtx_typeof y0
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_128 x_a0 = none ∧ EoCases.__smtx_typeof.case_129 x_a0 = none ∧ EoCases.__smtx_typeof.case_130 x_a0 = none ∧ EoCases.__smtx_typeof.case_131 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_32_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  group_round_step with case_128_eo__24smtx_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_128 x_a0, EoCases.__smtx_typeof.case_129 x_a0, EoCases.__smtx_typeof.case_130 x_a0, EoCases.__smtx_typeof.case_131 x_a0] = [] ++ [EoCases.__smtx_typeof.case_128 x_a0] ++ [EoCases.__smtx_typeof.case_129 x_a0, EoCases.__smtx_typeof.case_130 x_a0, EoCases.__smtx_typeof.case_131 x_a0] from rfl)
    otherwise ⟨hl_128⟩ using
  group_round_step with case_129_eo__24smtx_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_128 x_a0, EoCases.__smtx_typeof.case_129 x_a0, EoCases.__smtx_typeof.case_130 x_a0, EoCases.__smtx_typeof.case_131 x_a0] = [EoCases.__smtx_typeof.case_128 x_a0] ++ [EoCases.__smtx_typeof.case_129 x_a0] ++ [EoCases.__smtx_typeof.case_130 x_a0, EoCases.__smtx_typeof.case_131 x_a0] from rfl)
    otherwise ⟨hl_129⟩ using hl_128
  group_round_step with case_130_eo__24smtx_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_128 x_a0, EoCases.__smtx_typeof.case_129 x_a0, EoCases.__smtx_typeof.case_130 x_a0, EoCases.__smtx_typeof.case_131 x_a0] = [EoCases.__smtx_typeof.case_128 x_a0, EoCases.__smtx_typeof.case_129 x_a0] ++ [EoCases.__smtx_typeof.case_130 x_a0] ++ [EoCases.__smtx_typeof.case_131 x_a0] from rfl)
    otherwise ⟨hl_130⟩ using hl_128 hl_129
  group_round_step with case_131_eo__24smtx_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_128 x_a0, EoCases.__smtx_typeof.case_129 x_a0, EoCases.__smtx_typeof.case_130 x_a0, EoCases.__smtx_typeof.case_131 x_a0] = [EoCases.__smtx_typeof.case_128 x_a0, EoCases.__smtx_typeof.case_129 x_a0, EoCases.__smtx_typeof.case_130 x_a0] ++ [EoCases.__smtx_typeof.case_131 x_a0] ++ [] from rfl)
    otherwise ⟨hl_131⟩ using hl_128 hl_129 hl_130
  group_none hinv4 hG with ⟨hl_128, hl_129, hl_130, hl_131⟩

theorem cases_0_33_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_33_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, (∀ d, firstSome [EoCases.__smtx_typeof.case_132 x_a0, EoCases.__smtx_typeof.case_133 x_a0, EoCases.__smtx_typeof.case_134 x_a0, EoCases.__smtx_typeof.case_135 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          ∀ d, firstSome [EoCases.__smtx_typeof.case_132 x_a0, EoCases.__smtx_typeof.case_133 x_a0, EoCases.__smtx_typeof.case_134 x_a0, EoCases.__smtx_typeof.case_135 x_a0] d = __smtx_typeof y0
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_132 x_a0 = none ∧ EoCases.__smtx_typeof.case_133 x_a0 = none ∧ EoCases.__smtx_typeof.case_134 x_a0 = none ∧ EoCases.__smtx_typeof.case_135 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_33_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  group_round_step with case_132_eo__24smtx_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_132 x_a0, EoCases.__smtx_typeof.case_133 x_a0, EoCases.__smtx_typeof.case_134 x_a0, EoCases.__smtx_typeof.case_135 x_a0] = [] ++ [EoCases.__smtx_typeof.case_132 x_a0] ++ [EoCases.__smtx_typeof.case_133 x_a0, EoCases.__smtx_typeof.case_134 x_a0, EoCases.__smtx_typeof.case_135 x_a0] from rfl)
    otherwise ⟨hl_132⟩ using
  group_round_step with case_133_eo__24smtx_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_132 x_a0, EoCases.__smtx_typeof.case_133 x_a0, EoCases.__smtx_typeof.case_134 x_a0, EoCases.__smtx_typeof.case_135 x_a0] = [EoCases.__smtx_typeof.case_132 x_a0] ++ [EoCases.__smtx_typeof.case_133 x_a0] ++ [EoCases.__smtx_typeof.case_134 x_a0, EoCases.__smtx_typeof.case_135 x_a0] from rfl)
    otherwise ⟨hl_133⟩ using hl_132
  group_round_step with case_134_eo__24smtx_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_132 x_a0, EoCases.__smtx_typeof.case_133 x_a0, EoCases.__smtx_typeof.case_134 x_a0, EoCases.__smtx_typeof.case_135 x_a0] = [EoCases.__smtx_typeof.case_132 x_a0, EoCases.__smtx_typeof.case_133 x_a0] ++ [EoCases.__smtx_typeof.case_134 x_a0] ++ [EoCases.__smtx_typeof.case_135 x_a0] from rfl)
    otherwise ⟨hl_134⟩ using hl_132 hl_133
  group_round_step with case_135_eo__24smtx_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_132 x_a0, EoCases.__smtx_typeof.case_133 x_a0, EoCases.__smtx_typeof.case_134 x_a0, EoCases.__smtx_typeof.case_135 x_a0] = [EoCases.__smtx_typeof.case_132 x_a0, EoCases.__smtx_typeof.case_133 x_a0, EoCases.__smtx_typeof.case_134 x_a0] ++ [EoCases.__smtx_typeof.case_135 x_a0] ++ [] from rfl)
    otherwise ⟨hl_135⟩ using hl_132 hl_133 hl_134
  group_none hinv4 hG with ⟨hl_132, hl_133, hl_134, hl_135⟩

theorem cases_0_34_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_34_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, (∀ d, firstSome [EoCases.__smtx_typeof.case_136 x_a0, EoCases.__smtx_typeof.case_137 x_a0, EoCases.__smtx_typeof.case_138 x_a0, EoCases.__smtx_typeof.case_139 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          ∀ d, firstSome [EoCases.__smtx_typeof.case_136 x_a0, EoCases.__smtx_typeof.case_137 x_a0, EoCases.__smtx_typeof.case_138 x_a0, EoCases.__smtx_typeof.case_139 x_a0] d = __smtx_typeof y0
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_136 x_a0 = none ∧ EoCases.__smtx_typeof.case_137 x_a0 = none ∧ EoCases.__smtx_typeof.case_138 x_a0 = none ∧ EoCases.__smtx_typeof.case_139 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_34_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  group_round_step with case_136_eo__24smtx_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_136 x_a0, EoCases.__smtx_typeof.case_137 x_a0, EoCases.__smtx_typeof.case_138 x_a0, EoCases.__smtx_typeof.case_139 x_a0] = [] ++ [EoCases.__smtx_typeof.case_136 x_a0] ++ [EoCases.__smtx_typeof.case_137 x_a0, EoCases.__smtx_typeof.case_138 x_a0, EoCases.__smtx_typeof.case_139 x_a0] from rfl)
    otherwise ⟨hl_136⟩ using
  group_round_step with case_137_eo__24smtx_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_136 x_a0, EoCases.__smtx_typeof.case_137 x_a0, EoCases.__smtx_typeof.case_138 x_a0, EoCases.__smtx_typeof.case_139 x_a0] = [EoCases.__smtx_typeof.case_136 x_a0] ++ [EoCases.__smtx_typeof.case_137 x_a0] ++ [EoCases.__smtx_typeof.case_138 x_a0, EoCases.__smtx_typeof.case_139 x_a0] from rfl)
    otherwise ⟨hl_137⟩ using hl_136
  group_round_step with case_138_eo__24smtx_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_136 x_a0, EoCases.__smtx_typeof.case_137 x_a0, EoCases.__smtx_typeof.case_138 x_a0, EoCases.__smtx_typeof.case_139 x_a0] = [EoCases.__smtx_typeof.case_136 x_a0, EoCases.__smtx_typeof.case_137 x_a0] ++ [EoCases.__smtx_typeof.case_138 x_a0] ++ [EoCases.__smtx_typeof.case_139 x_a0] from rfl)
    otherwise ⟨hl_138⟩ using hl_136 hl_137
  group_round_step with case_139_eo__24smtx_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_136 x_a0, EoCases.__smtx_typeof.case_137 x_a0, EoCases.__smtx_typeof.case_138 x_a0, EoCases.__smtx_typeof.case_139 x_a0] = [EoCases.__smtx_typeof.case_136 x_a0, EoCases.__smtx_typeof.case_137 x_a0, EoCases.__smtx_typeof.case_138 x_a0] ++ [EoCases.__smtx_typeof.case_139 x_a0] ++ [] from rfl)
    otherwise ⟨hl_139⟩ using hl_136 hl_137 hl_138
  group_none hinv4 hG with ⟨hl_136, hl_137, hl_138, hl_139⟩

theorem cases_0_35_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_35_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, (∀ d, firstSome [EoCases.__smtx_typeof.case_140 x_a0, EoCases.__smtx_typeof.case_141 x_a0, EoCases.__smtx_typeof.case_142 x_a0, EoCases.__smtx_typeof.case_143 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          ∀ d, firstSome [EoCases.__smtx_typeof.case_140 x_a0, EoCases.__smtx_typeof.case_141 x_a0, EoCases.__smtx_typeof.case_142 x_a0, EoCases.__smtx_typeof.case_143 x_a0] d = __smtx_typeof y0
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_140 x_a0 = none ∧ EoCases.__smtx_typeof.case_141 x_a0 = none ∧ EoCases.__smtx_typeof.case_142 x_a0 = none ∧ EoCases.__smtx_typeof.case_143 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_35_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  group_round_step with case_140_eo__24smtx_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_140 x_a0, EoCases.__smtx_typeof.case_141 x_a0, EoCases.__smtx_typeof.case_142 x_a0, EoCases.__smtx_typeof.case_143 x_a0] = [] ++ [EoCases.__smtx_typeof.case_140 x_a0] ++ [EoCases.__smtx_typeof.case_141 x_a0, EoCases.__smtx_typeof.case_142 x_a0, EoCases.__smtx_typeof.case_143 x_a0] from rfl)
    otherwise ⟨hl_140⟩ using
  group_round_step with case_141_eo__24smtx_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_140 x_a0, EoCases.__smtx_typeof.case_141 x_a0, EoCases.__smtx_typeof.case_142 x_a0, EoCases.__smtx_typeof.case_143 x_a0] = [EoCases.__smtx_typeof.case_140 x_a0] ++ [EoCases.__smtx_typeof.case_141 x_a0] ++ [EoCases.__smtx_typeof.case_142 x_a0, EoCases.__smtx_typeof.case_143 x_a0] from rfl)
    otherwise ⟨hl_141⟩ using hl_140
  group_round_step with case_142_eo__24smtx_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_140 x_a0, EoCases.__smtx_typeof.case_141 x_a0, EoCases.__smtx_typeof.case_142 x_a0, EoCases.__smtx_typeof.case_143 x_a0] = [EoCases.__smtx_typeof.case_140 x_a0, EoCases.__smtx_typeof.case_141 x_a0] ++ [EoCases.__smtx_typeof.case_142 x_a0] ++ [EoCases.__smtx_typeof.case_143 x_a0] from rfl)
    otherwise ⟨hl_142⟩ using hl_140 hl_141
  group_round_step with case_143_eo__24smtx_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_140 x_a0, EoCases.__smtx_typeof.case_141 x_a0, EoCases.__smtx_typeof.case_142 x_a0, EoCases.__smtx_typeof.case_143 x_a0] = [EoCases.__smtx_typeof.case_140 x_a0, EoCases.__smtx_typeof.case_141 x_a0, EoCases.__smtx_typeof.case_142 x_a0] ++ [EoCases.__smtx_typeof.case_143 x_a0] ++ [] from rfl)
    otherwise ⟨hl_143⟩ using hl_140 hl_141 hl_142
  group_none hinv4 hG with ⟨hl_140, hl_141, hl_142, hl_143⟩

theorem cases_0_36_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_36_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, (∀ d, firstSome [EoCases.__smtx_typeof.case_144 x_a0, EoCases.__smtx_typeof.case_145 x_a0, EoCases.__smtx_typeof.case_146 x_a0, EoCases.__smtx_typeof.case_147 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          ∀ d, firstSome [EoCases.__smtx_typeof.case_144 x_a0, EoCases.__smtx_typeof.case_145 x_a0, EoCases.__smtx_typeof.case_146 x_a0, EoCases.__smtx_typeof.case_147 x_a0] d = __smtx_typeof y0
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_144 x_a0 = none ∧ EoCases.__smtx_typeof.case_145 x_a0 = none ∧ EoCases.__smtx_typeof.case_146 x_a0 = none ∧ EoCases.__smtx_typeof.case_147 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_36_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  group_round_step with case_144_eo__24smtx_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_144 x_a0, EoCases.__smtx_typeof.case_145 x_a0, EoCases.__smtx_typeof.case_146 x_a0, EoCases.__smtx_typeof.case_147 x_a0] = [] ++ [EoCases.__smtx_typeof.case_144 x_a0] ++ [EoCases.__smtx_typeof.case_145 x_a0, EoCases.__smtx_typeof.case_146 x_a0, EoCases.__smtx_typeof.case_147 x_a0] from rfl)
    otherwise ⟨hl_144⟩ using
  group_round_step with case_145_eo__24smtx_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_144 x_a0, EoCases.__smtx_typeof.case_145 x_a0, EoCases.__smtx_typeof.case_146 x_a0, EoCases.__smtx_typeof.case_147 x_a0] = [EoCases.__smtx_typeof.case_144 x_a0] ++ [EoCases.__smtx_typeof.case_145 x_a0] ++ [EoCases.__smtx_typeof.case_146 x_a0, EoCases.__smtx_typeof.case_147 x_a0] from rfl)
    otherwise ⟨hl_145⟩ using hl_144
  group_round_step with case_146_eo__24smtx_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_144 x_a0, EoCases.__smtx_typeof.case_145 x_a0, EoCases.__smtx_typeof.case_146 x_a0, EoCases.__smtx_typeof.case_147 x_a0] = [EoCases.__smtx_typeof.case_144 x_a0, EoCases.__smtx_typeof.case_145 x_a0] ++ [EoCases.__smtx_typeof.case_146 x_a0] ++ [EoCases.__smtx_typeof.case_147 x_a0] from rfl)
    otherwise ⟨hl_146⟩ using hl_144 hl_145
  group_round_step with case_147_eo__24smtx_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_144 x_a0, EoCases.__smtx_typeof.case_145 x_a0, EoCases.__smtx_typeof.case_146 x_a0, EoCases.__smtx_typeof.case_147 x_a0] = [EoCases.__smtx_typeof.case_144 x_a0, EoCases.__smtx_typeof.case_145 x_a0, EoCases.__smtx_typeof.case_146 x_a0] ++ [EoCases.__smtx_typeof.case_147 x_a0] ++ [] from rfl)
    otherwise ⟨hl_147⟩ using hl_144 hl_145 hl_146
  group_none hinv4 hG with ⟨hl_144, hl_145, hl_146, hl_147⟩

theorem cases_1_0_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_1_0_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, (∀ d, firstSome [EoCases.__smtx_typeof.case_0 x_a0, EoCases.__smtx_typeof.case_1 x_a0, EoCases.__smtx_typeof.case_2 x_a0, EoCases.__smtx_typeof.case_3 x_a0, EoCases.__smtx_typeof.case_4 x_a0, EoCases.__smtx_typeof.case_5 x_a0, EoCases.__smtx_typeof.case_6 x_a0, EoCases.__smtx_typeof.case_7 x_a0, EoCases.__smtx_typeof.case_8 x_a0, EoCases.__smtx_typeof.case_9 x_a0, EoCases.__smtx_typeof.case_10 x_a0, EoCases.__smtx_typeof.case_11 x_a0, EoCases.__smtx_typeof.case_12 x_a0, EoCases.__smtx_typeof.case_13 x_a0, EoCases.__smtx_typeof.case_14 x_a0, EoCases.__smtx_typeof.case_15 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          ∀ d, firstSome [EoCases.__smtx_typeof.case_0 x_a0, EoCases.__smtx_typeof.case_1 x_a0, EoCases.__smtx_typeof.case_2 x_a0, EoCases.__smtx_typeof.case_3 x_a0, EoCases.__smtx_typeof.case_4 x_a0, EoCases.__smtx_typeof.case_5 x_a0, EoCases.__smtx_typeof.case_6 x_a0, EoCases.__smtx_typeof.case_7 x_a0, EoCases.__smtx_typeof.case_8 x_a0, EoCases.__smtx_typeof.case_9 x_a0, EoCases.__smtx_typeof.case_10 x_a0, EoCases.__smtx_typeof.case_11 x_a0, EoCases.__smtx_typeof.case_12 x_a0, EoCases.__smtx_typeof.case_13 x_a0, EoCases.__smtx_typeof.case_14 x_a0, EoCases.__smtx_typeof.case_15 x_a0] d = __smtx_typeof y0
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_0 x_a0 = none ∧ EoCases.__smtx_typeof.case_1 x_a0 = none ∧ EoCases.__smtx_typeof.case_2 x_a0 = none ∧ EoCases.__smtx_typeof.case_3 x_a0 = none ∧ EoCases.__smtx_typeof.case_4 x_a0 = none ∧ EoCases.__smtx_typeof.case_5 x_a0 = none ∧ EoCases.__smtx_typeof.case_6 x_a0 = none ∧ EoCases.__smtx_typeof.case_7 x_a0 = none ∧ EoCases.__smtx_typeof.case_8 x_a0 = none ∧ EoCases.__smtx_typeof.case_9 x_a0 = none ∧ EoCases.__smtx_typeof.case_10 x_a0 = none ∧ EoCases.__smtx_typeof.case_11 x_a0 = none ∧ EoCases.__smtx_typeof.case_12 x_a0 = none ∧ EoCases.__smtx_typeof.case_13 x_a0 = none ∧ EoCases.__smtx_typeof.case_14 x_a0 = none ∧ EoCases.__smtx_typeof.case_15 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_1_0_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  group_round_step with cases_0_0_eo__24smtx_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_0 x_a0, EoCases.__smtx_typeof.case_1 x_a0, EoCases.__smtx_typeof.case_2 x_a0, EoCases.__smtx_typeof.case_3 x_a0, EoCases.__smtx_typeof.case_4 x_a0, EoCases.__smtx_typeof.case_5 x_a0, EoCases.__smtx_typeof.case_6 x_a0, EoCases.__smtx_typeof.case_7 x_a0, EoCases.__smtx_typeof.case_8 x_a0, EoCases.__smtx_typeof.case_9 x_a0, EoCases.__smtx_typeof.case_10 x_a0, EoCases.__smtx_typeof.case_11 x_a0, EoCases.__smtx_typeof.case_12 x_a0, EoCases.__smtx_typeof.case_13 x_a0, EoCases.__smtx_typeof.case_14 x_a0, EoCases.__smtx_typeof.case_15 x_a0] = [] ++ [EoCases.__smtx_typeof.case_0 x_a0, EoCases.__smtx_typeof.case_1 x_a0, EoCases.__smtx_typeof.case_2 x_a0, EoCases.__smtx_typeof.case_3 x_a0] ++ [EoCases.__smtx_typeof.case_4 x_a0, EoCases.__smtx_typeof.case_5 x_a0, EoCases.__smtx_typeof.case_6 x_a0, EoCases.__smtx_typeof.case_7 x_a0, EoCases.__smtx_typeof.case_8 x_a0, EoCases.__smtx_typeof.case_9 x_a0, EoCases.__smtx_typeof.case_10 x_a0, EoCases.__smtx_typeof.case_11 x_a0, EoCases.__smtx_typeof.case_12 x_a0, EoCases.__smtx_typeof.case_13 x_a0, EoCases.__smtx_typeof.case_14 x_a0, EoCases.__smtx_typeof.case_15 x_a0] from rfl)
    otherwise ⟨hl_0, hl_1, hl_2, hl_3⟩ using
  group_round_step with cases_0_1_eo__24smtx_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_0 x_a0, EoCases.__smtx_typeof.case_1 x_a0, EoCases.__smtx_typeof.case_2 x_a0, EoCases.__smtx_typeof.case_3 x_a0, EoCases.__smtx_typeof.case_4 x_a0, EoCases.__smtx_typeof.case_5 x_a0, EoCases.__smtx_typeof.case_6 x_a0, EoCases.__smtx_typeof.case_7 x_a0, EoCases.__smtx_typeof.case_8 x_a0, EoCases.__smtx_typeof.case_9 x_a0, EoCases.__smtx_typeof.case_10 x_a0, EoCases.__smtx_typeof.case_11 x_a0, EoCases.__smtx_typeof.case_12 x_a0, EoCases.__smtx_typeof.case_13 x_a0, EoCases.__smtx_typeof.case_14 x_a0, EoCases.__smtx_typeof.case_15 x_a0] = [EoCases.__smtx_typeof.case_0 x_a0, EoCases.__smtx_typeof.case_1 x_a0, EoCases.__smtx_typeof.case_2 x_a0, EoCases.__smtx_typeof.case_3 x_a0] ++ [EoCases.__smtx_typeof.case_4 x_a0, EoCases.__smtx_typeof.case_5 x_a0, EoCases.__smtx_typeof.case_6 x_a0, EoCases.__smtx_typeof.case_7 x_a0] ++ [EoCases.__smtx_typeof.case_8 x_a0, EoCases.__smtx_typeof.case_9 x_a0, EoCases.__smtx_typeof.case_10 x_a0, EoCases.__smtx_typeof.case_11 x_a0, EoCases.__smtx_typeof.case_12 x_a0, EoCases.__smtx_typeof.case_13 x_a0, EoCases.__smtx_typeof.case_14 x_a0, EoCases.__smtx_typeof.case_15 x_a0] from rfl)
    otherwise ⟨hl_4, hl_5, hl_6, hl_7⟩ using hl_0 hl_1 hl_2 hl_3
  group_round_step with cases_0_2_eo__24smtx_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_0 x_a0, EoCases.__smtx_typeof.case_1 x_a0, EoCases.__smtx_typeof.case_2 x_a0, EoCases.__smtx_typeof.case_3 x_a0, EoCases.__smtx_typeof.case_4 x_a0, EoCases.__smtx_typeof.case_5 x_a0, EoCases.__smtx_typeof.case_6 x_a0, EoCases.__smtx_typeof.case_7 x_a0, EoCases.__smtx_typeof.case_8 x_a0, EoCases.__smtx_typeof.case_9 x_a0, EoCases.__smtx_typeof.case_10 x_a0, EoCases.__smtx_typeof.case_11 x_a0, EoCases.__smtx_typeof.case_12 x_a0, EoCases.__smtx_typeof.case_13 x_a0, EoCases.__smtx_typeof.case_14 x_a0, EoCases.__smtx_typeof.case_15 x_a0] = [EoCases.__smtx_typeof.case_0 x_a0, EoCases.__smtx_typeof.case_1 x_a0, EoCases.__smtx_typeof.case_2 x_a0, EoCases.__smtx_typeof.case_3 x_a0, EoCases.__smtx_typeof.case_4 x_a0, EoCases.__smtx_typeof.case_5 x_a0, EoCases.__smtx_typeof.case_6 x_a0, EoCases.__smtx_typeof.case_7 x_a0] ++ [EoCases.__smtx_typeof.case_8 x_a0, EoCases.__smtx_typeof.case_9 x_a0, EoCases.__smtx_typeof.case_10 x_a0, EoCases.__smtx_typeof.case_11 x_a0] ++ [EoCases.__smtx_typeof.case_12 x_a0, EoCases.__smtx_typeof.case_13 x_a0, EoCases.__smtx_typeof.case_14 x_a0, EoCases.__smtx_typeof.case_15 x_a0] from rfl)
    otherwise ⟨hl_8, hl_9, hl_10, hl_11⟩ using hl_0 hl_1 hl_2 hl_3 hl_4 hl_5 hl_6 hl_7
  group_round_step with cases_0_3_eo__24smtx_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_0 x_a0, EoCases.__smtx_typeof.case_1 x_a0, EoCases.__smtx_typeof.case_2 x_a0, EoCases.__smtx_typeof.case_3 x_a0, EoCases.__smtx_typeof.case_4 x_a0, EoCases.__smtx_typeof.case_5 x_a0, EoCases.__smtx_typeof.case_6 x_a0, EoCases.__smtx_typeof.case_7 x_a0, EoCases.__smtx_typeof.case_8 x_a0, EoCases.__smtx_typeof.case_9 x_a0, EoCases.__smtx_typeof.case_10 x_a0, EoCases.__smtx_typeof.case_11 x_a0, EoCases.__smtx_typeof.case_12 x_a0, EoCases.__smtx_typeof.case_13 x_a0, EoCases.__smtx_typeof.case_14 x_a0, EoCases.__smtx_typeof.case_15 x_a0] = [EoCases.__smtx_typeof.case_0 x_a0, EoCases.__smtx_typeof.case_1 x_a0, EoCases.__smtx_typeof.case_2 x_a0, EoCases.__smtx_typeof.case_3 x_a0, EoCases.__smtx_typeof.case_4 x_a0, EoCases.__smtx_typeof.case_5 x_a0, EoCases.__smtx_typeof.case_6 x_a0, EoCases.__smtx_typeof.case_7 x_a0, EoCases.__smtx_typeof.case_8 x_a0, EoCases.__smtx_typeof.case_9 x_a0, EoCases.__smtx_typeof.case_10 x_a0, EoCases.__smtx_typeof.case_11 x_a0] ++ [EoCases.__smtx_typeof.case_12 x_a0, EoCases.__smtx_typeof.case_13 x_a0, EoCases.__smtx_typeof.case_14 x_a0, EoCases.__smtx_typeof.case_15 x_a0] ++ [] from rfl)
    otherwise ⟨hl_12, hl_13, hl_14, hl_15⟩ using hl_0 hl_1 hl_2 hl_3 hl_4 hl_5 hl_6 hl_7 hl_8 hl_9 hl_10 hl_11
  group_none hinv4 hG with ⟨hl_0, hl_1, hl_2, hl_3, hl_4, hl_5, hl_6, hl_7, hl_8, hl_9, hl_10, hl_11, hl_12, hl_13, hl_14, hl_15⟩

theorem cases_1_1_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_1_1_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, (∀ d, firstSome [EoCases.__smtx_typeof.case_16 x_a0, EoCases.__smtx_typeof.case_17 x_a0, EoCases.__smtx_typeof.case_18 x_a0, EoCases.__smtx_typeof.case_19 x_a0, EoCases.__smtx_typeof.case_20 x_a0, EoCases.__smtx_typeof.case_21 x_a0, EoCases.__smtx_typeof.case_22 x_a0, EoCases.__smtx_typeof.case_23 x_a0, EoCases.__smtx_typeof.case_24 x_a0, EoCases.__smtx_typeof.case_25 x_a0, EoCases.__smtx_typeof.case_26 x_a0, EoCases.__smtx_typeof.case_27 x_a0, EoCases.__smtx_typeof.case_28 x_a0, EoCases.__smtx_typeof.case_29 x_a0, EoCases.__smtx_typeof.case_30 x_a0, EoCases.__smtx_typeof.case_31 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          ∀ d, firstSome [EoCases.__smtx_typeof.case_16 x_a0, EoCases.__smtx_typeof.case_17 x_a0, EoCases.__smtx_typeof.case_18 x_a0, EoCases.__smtx_typeof.case_19 x_a0, EoCases.__smtx_typeof.case_20 x_a0, EoCases.__smtx_typeof.case_21 x_a0, EoCases.__smtx_typeof.case_22 x_a0, EoCases.__smtx_typeof.case_23 x_a0, EoCases.__smtx_typeof.case_24 x_a0, EoCases.__smtx_typeof.case_25 x_a0, EoCases.__smtx_typeof.case_26 x_a0, EoCases.__smtx_typeof.case_27 x_a0, EoCases.__smtx_typeof.case_28 x_a0, EoCases.__smtx_typeof.case_29 x_a0, EoCases.__smtx_typeof.case_30 x_a0, EoCases.__smtx_typeof.case_31 x_a0] d = __smtx_typeof y0
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_16 x_a0 = none ∧ EoCases.__smtx_typeof.case_17 x_a0 = none ∧ EoCases.__smtx_typeof.case_18 x_a0 = none ∧ EoCases.__smtx_typeof.case_19 x_a0 = none ∧ EoCases.__smtx_typeof.case_20 x_a0 = none ∧ EoCases.__smtx_typeof.case_21 x_a0 = none ∧ EoCases.__smtx_typeof.case_22 x_a0 = none ∧ EoCases.__smtx_typeof.case_23 x_a0 = none ∧ EoCases.__smtx_typeof.case_24 x_a0 = none ∧ EoCases.__smtx_typeof.case_25 x_a0 = none ∧ EoCases.__smtx_typeof.case_26 x_a0 = none ∧ EoCases.__smtx_typeof.case_27 x_a0 = none ∧ EoCases.__smtx_typeof.case_28 x_a0 = none ∧ EoCases.__smtx_typeof.case_29 x_a0 = none ∧ EoCases.__smtx_typeof.case_30 x_a0 = none ∧ EoCases.__smtx_typeof.case_31 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_1_1_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  group_round_step with cases_0_4_eo__24smtx_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_16 x_a0, EoCases.__smtx_typeof.case_17 x_a0, EoCases.__smtx_typeof.case_18 x_a0, EoCases.__smtx_typeof.case_19 x_a0, EoCases.__smtx_typeof.case_20 x_a0, EoCases.__smtx_typeof.case_21 x_a0, EoCases.__smtx_typeof.case_22 x_a0, EoCases.__smtx_typeof.case_23 x_a0, EoCases.__smtx_typeof.case_24 x_a0, EoCases.__smtx_typeof.case_25 x_a0, EoCases.__smtx_typeof.case_26 x_a0, EoCases.__smtx_typeof.case_27 x_a0, EoCases.__smtx_typeof.case_28 x_a0, EoCases.__smtx_typeof.case_29 x_a0, EoCases.__smtx_typeof.case_30 x_a0, EoCases.__smtx_typeof.case_31 x_a0] = [] ++ [EoCases.__smtx_typeof.case_16 x_a0, EoCases.__smtx_typeof.case_17 x_a0, EoCases.__smtx_typeof.case_18 x_a0, EoCases.__smtx_typeof.case_19 x_a0] ++ [EoCases.__smtx_typeof.case_20 x_a0, EoCases.__smtx_typeof.case_21 x_a0, EoCases.__smtx_typeof.case_22 x_a0, EoCases.__smtx_typeof.case_23 x_a0, EoCases.__smtx_typeof.case_24 x_a0, EoCases.__smtx_typeof.case_25 x_a0, EoCases.__smtx_typeof.case_26 x_a0, EoCases.__smtx_typeof.case_27 x_a0, EoCases.__smtx_typeof.case_28 x_a0, EoCases.__smtx_typeof.case_29 x_a0, EoCases.__smtx_typeof.case_30 x_a0, EoCases.__smtx_typeof.case_31 x_a0] from rfl)
    otherwise ⟨hl_16, hl_17, hl_18, hl_19⟩ using
  group_round_step with cases_0_5_eo__24smtx_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_16 x_a0, EoCases.__smtx_typeof.case_17 x_a0, EoCases.__smtx_typeof.case_18 x_a0, EoCases.__smtx_typeof.case_19 x_a0, EoCases.__smtx_typeof.case_20 x_a0, EoCases.__smtx_typeof.case_21 x_a0, EoCases.__smtx_typeof.case_22 x_a0, EoCases.__smtx_typeof.case_23 x_a0, EoCases.__smtx_typeof.case_24 x_a0, EoCases.__smtx_typeof.case_25 x_a0, EoCases.__smtx_typeof.case_26 x_a0, EoCases.__smtx_typeof.case_27 x_a0, EoCases.__smtx_typeof.case_28 x_a0, EoCases.__smtx_typeof.case_29 x_a0, EoCases.__smtx_typeof.case_30 x_a0, EoCases.__smtx_typeof.case_31 x_a0] = [EoCases.__smtx_typeof.case_16 x_a0, EoCases.__smtx_typeof.case_17 x_a0, EoCases.__smtx_typeof.case_18 x_a0, EoCases.__smtx_typeof.case_19 x_a0] ++ [EoCases.__smtx_typeof.case_20 x_a0, EoCases.__smtx_typeof.case_21 x_a0, EoCases.__smtx_typeof.case_22 x_a0, EoCases.__smtx_typeof.case_23 x_a0] ++ [EoCases.__smtx_typeof.case_24 x_a0, EoCases.__smtx_typeof.case_25 x_a0, EoCases.__smtx_typeof.case_26 x_a0, EoCases.__smtx_typeof.case_27 x_a0, EoCases.__smtx_typeof.case_28 x_a0, EoCases.__smtx_typeof.case_29 x_a0, EoCases.__smtx_typeof.case_30 x_a0, EoCases.__smtx_typeof.case_31 x_a0] from rfl)
    otherwise ⟨hl_20, hl_21, hl_22, hl_23⟩ using hl_16 hl_17 hl_18 hl_19
  group_round_step with cases_0_6_eo__24smtx_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_16 x_a0, EoCases.__smtx_typeof.case_17 x_a0, EoCases.__smtx_typeof.case_18 x_a0, EoCases.__smtx_typeof.case_19 x_a0, EoCases.__smtx_typeof.case_20 x_a0, EoCases.__smtx_typeof.case_21 x_a0, EoCases.__smtx_typeof.case_22 x_a0, EoCases.__smtx_typeof.case_23 x_a0, EoCases.__smtx_typeof.case_24 x_a0, EoCases.__smtx_typeof.case_25 x_a0, EoCases.__smtx_typeof.case_26 x_a0, EoCases.__smtx_typeof.case_27 x_a0, EoCases.__smtx_typeof.case_28 x_a0, EoCases.__smtx_typeof.case_29 x_a0, EoCases.__smtx_typeof.case_30 x_a0, EoCases.__smtx_typeof.case_31 x_a0] = [EoCases.__smtx_typeof.case_16 x_a0, EoCases.__smtx_typeof.case_17 x_a0, EoCases.__smtx_typeof.case_18 x_a0, EoCases.__smtx_typeof.case_19 x_a0, EoCases.__smtx_typeof.case_20 x_a0, EoCases.__smtx_typeof.case_21 x_a0, EoCases.__smtx_typeof.case_22 x_a0, EoCases.__smtx_typeof.case_23 x_a0] ++ [EoCases.__smtx_typeof.case_24 x_a0, EoCases.__smtx_typeof.case_25 x_a0, EoCases.__smtx_typeof.case_26 x_a0, EoCases.__smtx_typeof.case_27 x_a0] ++ [EoCases.__smtx_typeof.case_28 x_a0, EoCases.__smtx_typeof.case_29 x_a0, EoCases.__smtx_typeof.case_30 x_a0, EoCases.__smtx_typeof.case_31 x_a0] from rfl)
    otherwise ⟨hl_24, hl_25, hl_26, hl_27⟩ using hl_16 hl_17 hl_18 hl_19 hl_20 hl_21 hl_22 hl_23
  group_round_step with cases_0_7_eo__24smtx_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_16 x_a0, EoCases.__smtx_typeof.case_17 x_a0, EoCases.__smtx_typeof.case_18 x_a0, EoCases.__smtx_typeof.case_19 x_a0, EoCases.__smtx_typeof.case_20 x_a0, EoCases.__smtx_typeof.case_21 x_a0, EoCases.__smtx_typeof.case_22 x_a0, EoCases.__smtx_typeof.case_23 x_a0, EoCases.__smtx_typeof.case_24 x_a0, EoCases.__smtx_typeof.case_25 x_a0, EoCases.__smtx_typeof.case_26 x_a0, EoCases.__smtx_typeof.case_27 x_a0, EoCases.__smtx_typeof.case_28 x_a0, EoCases.__smtx_typeof.case_29 x_a0, EoCases.__smtx_typeof.case_30 x_a0, EoCases.__smtx_typeof.case_31 x_a0] = [EoCases.__smtx_typeof.case_16 x_a0, EoCases.__smtx_typeof.case_17 x_a0, EoCases.__smtx_typeof.case_18 x_a0, EoCases.__smtx_typeof.case_19 x_a0, EoCases.__smtx_typeof.case_20 x_a0, EoCases.__smtx_typeof.case_21 x_a0, EoCases.__smtx_typeof.case_22 x_a0, EoCases.__smtx_typeof.case_23 x_a0, EoCases.__smtx_typeof.case_24 x_a0, EoCases.__smtx_typeof.case_25 x_a0, EoCases.__smtx_typeof.case_26 x_a0, EoCases.__smtx_typeof.case_27 x_a0] ++ [EoCases.__smtx_typeof.case_28 x_a0, EoCases.__smtx_typeof.case_29 x_a0, EoCases.__smtx_typeof.case_30 x_a0, EoCases.__smtx_typeof.case_31 x_a0] ++ [] from rfl)
    otherwise ⟨hl_28, hl_29, hl_30, hl_31⟩ using hl_16 hl_17 hl_18 hl_19 hl_20 hl_21 hl_22 hl_23 hl_24 hl_25 hl_26 hl_27
  group_none hinv4 hG with ⟨hl_16, hl_17, hl_18, hl_19, hl_20, hl_21, hl_22, hl_23, hl_24, hl_25, hl_26, hl_27, hl_28, hl_29, hl_30, hl_31⟩

theorem cases_1_2_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_1_2_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, (∀ d, firstSome [EoCases.__smtx_typeof.case_32 x_a0, EoCases.__smtx_typeof.case_33 x_a0, EoCases.__smtx_typeof.case_34 x_a0, EoCases.__smtx_typeof.case_35 x_a0, EoCases.__smtx_typeof.case_36 x_a0, EoCases.__smtx_typeof.case_37 x_a0, EoCases.__smtx_typeof.case_38 x_a0, EoCases.__smtx_typeof.case_39 x_a0, EoCases.__smtx_typeof.case_40 x_a0, EoCases.__smtx_typeof.case_41 x_a0, EoCases.__smtx_typeof.case_42 x_a0, EoCases.__smtx_typeof.case_43 x_a0, EoCases.__smtx_typeof.case_44 x_a0, EoCases.__smtx_typeof.case_45 x_a0, EoCases.__smtx_typeof.case_46 x_a0, EoCases.__smtx_typeof.case_47 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          ∀ d, firstSome [EoCases.__smtx_typeof.case_32 x_a0, EoCases.__smtx_typeof.case_33 x_a0, EoCases.__smtx_typeof.case_34 x_a0, EoCases.__smtx_typeof.case_35 x_a0, EoCases.__smtx_typeof.case_36 x_a0, EoCases.__smtx_typeof.case_37 x_a0, EoCases.__smtx_typeof.case_38 x_a0, EoCases.__smtx_typeof.case_39 x_a0, EoCases.__smtx_typeof.case_40 x_a0, EoCases.__smtx_typeof.case_41 x_a0, EoCases.__smtx_typeof.case_42 x_a0, EoCases.__smtx_typeof.case_43 x_a0, EoCases.__smtx_typeof.case_44 x_a0, EoCases.__smtx_typeof.case_45 x_a0, EoCases.__smtx_typeof.case_46 x_a0, EoCases.__smtx_typeof.case_47 x_a0] d = __smtx_typeof y0
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_32 x_a0 = none ∧ EoCases.__smtx_typeof.case_33 x_a0 = none ∧ EoCases.__smtx_typeof.case_34 x_a0 = none ∧ EoCases.__smtx_typeof.case_35 x_a0 = none ∧ EoCases.__smtx_typeof.case_36 x_a0 = none ∧ EoCases.__smtx_typeof.case_37 x_a0 = none ∧ EoCases.__smtx_typeof.case_38 x_a0 = none ∧ EoCases.__smtx_typeof.case_39 x_a0 = none ∧ EoCases.__smtx_typeof.case_40 x_a0 = none ∧ EoCases.__smtx_typeof.case_41 x_a0 = none ∧ EoCases.__smtx_typeof.case_42 x_a0 = none ∧ EoCases.__smtx_typeof.case_43 x_a0 = none ∧ EoCases.__smtx_typeof.case_44 x_a0 = none ∧ EoCases.__smtx_typeof.case_45 x_a0 = none ∧ EoCases.__smtx_typeof.case_46 x_a0 = none ∧ EoCases.__smtx_typeof.case_47 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_1_2_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  group_round_step with cases_0_8_eo__24smtx_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_32 x_a0, EoCases.__smtx_typeof.case_33 x_a0, EoCases.__smtx_typeof.case_34 x_a0, EoCases.__smtx_typeof.case_35 x_a0, EoCases.__smtx_typeof.case_36 x_a0, EoCases.__smtx_typeof.case_37 x_a0, EoCases.__smtx_typeof.case_38 x_a0, EoCases.__smtx_typeof.case_39 x_a0, EoCases.__smtx_typeof.case_40 x_a0, EoCases.__smtx_typeof.case_41 x_a0, EoCases.__smtx_typeof.case_42 x_a0, EoCases.__smtx_typeof.case_43 x_a0, EoCases.__smtx_typeof.case_44 x_a0, EoCases.__smtx_typeof.case_45 x_a0, EoCases.__smtx_typeof.case_46 x_a0, EoCases.__smtx_typeof.case_47 x_a0] = [] ++ [EoCases.__smtx_typeof.case_32 x_a0, EoCases.__smtx_typeof.case_33 x_a0, EoCases.__smtx_typeof.case_34 x_a0, EoCases.__smtx_typeof.case_35 x_a0] ++ [EoCases.__smtx_typeof.case_36 x_a0, EoCases.__smtx_typeof.case_37 x_a0, EoCases.__smtx_typeof.case_38 x_a0, EoCases.__smtx_typeof.case_39 x_a0, EoCases.__smtx_typeof.case_40 x_a0, EoCases.__smtx_typeof.case_41 x_a0, EoCases.__smtx_typeof.case_42 x_a0, EoCases.__smtx_typeof.case_43 x_a0, EoCases.__smtx_typeof.case_44 x_a0, EoCases.__smtx_typeof.case_45 x_a0, EoCases.__smtx_typeof.case_46 x_a0, EoCases.__smtx_typeof.case_47 x_a0] from rfl)
    otherwise ⟨hl_32, hl_33, hl_34, hl_35⟩ using
  group_round_step with cases_0_9_eo__24smtx_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_32 x_a0, EoCases.__smtx_typeof.case_33 x_a0, EoCases.__smtx_typeof.case_34 x_a0, EoCases.__smtx_typeof.case_35 x_a0, EoCases.__smtx_typeof.case_36 x_a0, EoCases.__smtx_typeof.case_37 x_a0, EoCases.__smtx_typeof.case_38 x_a0, EoCases.__smtx_typeof.case_39 x_a0, EoCases.__smtx_typeof.case_40 x_a0, EoCases.__smtx_typeof.case_41 x_a0, EoCases.__smtx_typeof.case_42 x_a0, EoCases.__smtx_typeof.case_43 x_a0, EoCases.__smtx_typeof.case_44 x_a0, EoCases.__smtx_typeof.case_45 x_a0, EoCases.__smtx_typeof.case_46 x_a0, EoCases.__smtx_typeof.case_47 x_a0] = [EoCases.__smtx_typeof.case_32 x_a0, EoCases.__smtx_typeof.case_33 x_a0, EoCases.__smtx_typeof.case_34 x_a0, EoCases.__smtx_typeof.case_35 x_a0] ++ [EoCases.__smtx_typeof.case_36 x_a0, EoCases.__smtx_typeof.case_37 x_a0, EoCases.__smtx_typeof.case_38 x_a0, EoCases.__smtx_typeof.case_39 x_a0] ++ [EoCases.__smtx_typeof.case_40 x_a0, EoCases.__smtx_typeof.case_41 x_a0, EoCases.__smtx_typeof.case_42 x_a0, EoCases.__smtx_typeof.case_43 x_a0, EoCases.__smtx_typeof.case_44 x_a0, EoCases.__smtx_typeof.case_45 x_a0, EoCases.__smtx_typeof.case_46 x_a0, EoCases.__smtx_typeof.case_47 x_a0] from rfl)
    otherwise ⟨hl_36, hl_37, hl_38, hl_39⟩ using hl_32 hl_33 hl_34 hl_35
  group_round_step with cases_0_10_eo__24smtx_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_32 x_a0, EoCases.__smtx_typeof.case_33 x_a0, EoCases.__smtx_typeof.case_34 x_a0, EoCases.__smtx_typeof.case_35 x_a0, EoCases.__smtx_typeof.case_36 x_a0, EoCases.__smtx_typeof.case_37 x_a0, EoCases.__smtx_typeof.case_38 x_a0, EoCases.__smtx_typeof.case_39 x_a0, EoCases.__smtx_typeof.case_40 x_a0, EoCases.__smtx_typeof.case_41 x_a0, EoCases.__smtx_typeof.case_42 x_a0, EoCases.__smtx_typeof.case_43 x_a0, EoCases.__smtx_typeof.case_44 x_a0, EoCases.__smtx_typeof.case_45 x_a0, EoCases.__smtx_typeof.case_46 x_a0, EoCases.__smtx_typeof.case_47 x_a0] = [EoCases.__smtx_typeof.case_32 x_a0, EoCases.__smtx_typeof.case_33 x_a0, EoCases.__smtx_typeof.case_34 x_a0, EoCases.__smtx_typeof.case_35 x_a0, EoCases.__smtx_typeof.case_36 x_a0, EoCases.__smtx_typeof.case_37 x_a0, EoCases.__smtx_typeof.case_38 x_a0, EoCases.__smtx_typeof.case_39 x_a0] ++ [EoCases.__smtx_typeof.case_40 x_a0, EoCases.__smtx_typeof.case_41 x_a0, EoCases.__smtx_typeof.case_42 x_a0, EoCases.__smtx_typeof.case_43 x_a0] ++ [EoCases.__smtx_typeof.case_44 x_a0, EoCases.__smtx_typeof.case_45 x_a0, EoCases.__smtx_typeof.case_46 x_a0, EoCases.__smtx_typeof.case_47 x_a0] from rfl)
    otherwise ⟨hl_40, hl_41, hl_42, hl_43⟩ using hl_32 hl_33 hl_34 hl_35 hl_36 hl_37 hl_38 hl_39
  group_round_step with cases_0_11_eo__24smtx_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_32 x_a0, EoCases.__smtx_typeof.case_33 x_a0, EoCases.__smtx_typeof.case_34 x_a0, EoCases.__smtx_typeof.case_35 x_a0, EoCases.__smtx_typeof.case_36 x_a0, EoCases.__smtx_typeof.case_37 x_a0, EoCases.__smtx_typeof.case_38 x_a0, EoCases.__smtx_typeof.case_39 x_a0, EoCases.__smtx_typeof.case_40 x_a0, EoCases.__smtx_typeof.case_41 x_a0, EoCases.__smtx_typeof.case_42 x_a0, EoCases.__smtx_typeof.case_43 x_a0, EoCases.__smtx_typeof.case_44 x_a0, EoCases.__smtx_typeof.case_45 x_a0, EoCases.__smtx_typeof.case_46 x_a0, EoCases.__smtx_typeof.case_47 x_a0] = [EoCases.__smtx_typeof.case_32 x_a0, EoCases.__smtx_typeof.case_33 x_a0, EoCases.__smtx_typeof.case_34 x_a0, EoCases.__smtx_typeof.case_35 x_a0, EoCases.__smtx_typeof.case_36 x_a0, EoCases.__smtx_typeof.case_37 x_a0, EoCases.__smtx_typeof.case_38 x_a0, EoCases.__smtx_typeof.case_39 x_a0, EoCases.__smtx_typeof.case_40 x_a0, EoCases.__smtx_typeof.case_41 x_a0, EoCases.__smtx_typeof.case_42 x_a0, EoCases.__smtx_typeof.case_43 x_a0] ++ [EoCases.__smtx_typeof.case_44 x_a0, EoCases.__smtx_typeof.case_45 x_a0, EoCases.__smtx_typeof.case_46 x_a0, EoCases.__smtx_typeof.case_47 x_a0] ++ [] from rfl)
    otherwise ⟨hl_44, hl_45, hl_46, hl_47⟩ using hl_32 hl_33 hl_34 hl_35 hl_36 hl_37 hl_38 hl_39 hl_40 hl_41 hl_42 hl_43
  group_none hinv4 hG with ⟨hl_32, hl_33, hl_34, hl_35, hl_36, hl_37, hl_38, hl_39, hl_40, hl_41, hl_42, hl_43, hl_44, hl_45, hl_46, hl_47⟩

theorem cases_1_3_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_1_3_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, (∀ d, firstSome [EoCases.__smtx_typeof.case_48 x_a0, EoCases.__smtx_typeof.case_49 x_a0, EoCases.__smtx_typeof.case_50 x_a0, EoCases.__smtx_typeof.case_51 x_a0, EoCases.__smtx_typeof.case_52 x_a0, EoCases.__smtx_typeof.case_53 x_a0, EoCases.__smtx_typeof.case_54 x_a0, EoCases.__smtx_typeof.case_55 x_a0, EoCases.__smtx_typeof.case_56 x_a0, EoCases.__smtx_typeof.case_57 x_a0, EoCases.__smtx_typeof.case_58 x_a0, EoCases.__smtx_typeof.case_59 x_a0, EoCases.__smtx_typeof.case_60 x_a0, EoCases.__smtx_typeof.case_61 x_a0, EoCases.__smtx_typeof.case_62 x_a0, EoCases.__smtx_typeof.case_63 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          ∀ d, firstSome [EoCases.__smtx_typeof.case_48 x_a0, EoCases.__smtx_typeof.case_49 x_a0, EoCases.__smtx_typeof.case_50 x_a0, EoCases.__smtx_typeof.case_51 x_a0, EoCases.__smtx_typeof.case_52 x_a0, EoCases.__smtx_typeof.case_53 x_a0, EoCases.__smtx_typeof.case_54 x_a0, EoCases.__smtx_typeof.case_55 x_a0, EoCases.__smtx_typeof.case_56 x_a0, EoCases.__smtx_typeof.case_57 x_a0, EoCases.__smtx_typeof.case_58 x_a0, EoCases.__smtx_typeof.case_59 x_a0, EoCases.__smtx_typeof.case_60 x_a0, EoCases.__smtx_typeof.case_61 x_a0, EoCases.__smtx_typeof.case_62 x_a0, EoCases.__smtx_typeof.case_63 x_a0] d = __smtx_typeof y0
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_48 x_a0 = none ∧ EoCases.__smtx_typeof.case_49 x_a0 = none ∧ EoCases.__smtx_typeof.case_50 x_a0 = none ∧ EoCases.__smtx_typeof.case_51 x_a0 = none ∧ EoCases.__smtx_typeof.case_52 x_a0 = none ∧ EoCases.__smtx_typeof.case_53 x_a0 = none ∧ EoCases.__smtx_typeof.case_54 x_a0 = none ∧ EoCases.__smtx_typeof.case_55 x_a0 = none ∧ EoCases.__smtx_typeof.case_56 x_a0 = none ∧ EoCases.__smtx_typeof.case_57 x_a0 = none ∧ EoCases.__smtx_typeof.case_58 x_a0 = none ∧ EoCases.__smtx_typeof.case_59 x_a0 = none ∧ EoCases.__smtx_typeof.case_60 x_a0 = none ∧ EoCases.__smtx_typeof.case_61 x_a0 = none ∧ EoCases.__smtx_typeof.case_62 x_a0 = none ∧ EoCases.__smtx_typeof.case_63 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_1_3_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  group_round_step with cases_0_12_eo__24smtx_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_48 x_a0, EoCases.__smtx_typeof.case_49 x_a0, EoCases.__smtx_typeof.case_50 x_a0, EoCases.__smtx_typeof.case_51 x_a0, EoCases.__smtx_typeof.case_52 x_a0, EoCases.__smtx_typeof.case_53 x_a0, EoCases.__smtx_typeof.case_54 x_a0, EoCases.__smtx_typeof.case_55 x_a0, EoCases.__smtx_typeof.case_56 x_a0, EoCases.__smtx_typeof.case_57 x_a0, EoCases.__smtx_typeof.case_58 x_a0, EoCases.__smtx_typeof.case_59 x_a0, EoCases.__smtx_typeof.case_60 x_a0, EoCases.__smtx_typeof.case_61 x_a0, EoCases.__smtx_typeof.case_62 x_a0, EoCases.__smtx_typeof.case_63 x_a0] = [] ++ [EoCases.__smtx_typeof.case_48 x_a0, EoCases.__smtx_typeof.case_49 x_a0, EoCases.__smtx_typeof.case_50 x_a0, EoCases.__smtx_typeof.case_51 x_a0] ++ [EoCases.__smtx_typeof.case_52 x_a0, EoCases.__smtx_typeof.case_53 x_a0, EoCases.__smtx_typeof.case_54 x_a0, EoCases.__smtx_typeof.case_55 x_a0, EoCases.__smtx_typeof.case_56 x_a0, EoCases.__smtx_typeof.case_57 x_a0, EoCases.__smtx_typeof.case_58 x_a0, EoCases.__smtx_typeof.case_59 x_a0, EoCases.__smtx_typeof.case_60 x_a0, EoCases.__smtx_typeof.case_61 x_a0, EoCases.__smtx_typeof.case_62 x_a0, EoCases.__smtx_typeof.case_63 x_a0] from rfl)
    otherwise ⟨hl_48, hl_49, hl_50, hl_51⟩ using
  group_round_step with cases_0_13_eo__24smtx_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_48 x_a0, EoCases.__smtx_typeof.case_49 x_a0, EoCases.__smtx_typeof.case_50 x_a0, EoCases.__smtx_typeof.case_51 x_a0, EoCases.__smtx_typeof.case_52 x_a0, EoCases.__smtx_typeof.case_53 x_a0, EoCases.__smtx_typeof.case_54 x_a0, EoCases.__smtx_typeof.case_55 x_a0, EoCases.__smtx_typeof.case_56 x_a0, EoCases.__smtx_typeof.case_57 x_a0, EoCases.__smtx_typeof.case_58 x_a0, EoCases.__smtx_typeof.case_59 x_a0, EoCases.__smtx_typeof.case_60 x_a0, EoCases.__smtx_typeof.case_61 x_a0, EoCases.__smtx_typeof.case_62 x_a0, EoCases.__smtx_typeof.case_63 x_a0] = [EoCases.__smtx_typeof.case_48 x_a0, EoCases.__smtx_typeof.case_49 x_a0, EoCases.__smtx_typeof.case_50 x_a0, EoCases.__smtx_typeof.case_51 x_a0] ++ [EoCases.__smtx_typeof.case_52 x_a0, EoCases.__smtx_typeof.case_53 x_a0, EoCases.__smtx_typeof.case_54 x_a0, EoCases.__smtx_typeof.case_55 x_a0] ++ [EoCases.__smtx_typeof.case_56 x_a0, EoCases.__smtx_typeof.case_57 x_a0, EoCases.__smtx_typeof.case_58 x_a0, EoCases.__smtx_typeof.case_59 x_a0, EoCases.__smtx_typeof.case_60 x_a0, EoCases.__smtx_typeof.case_61 x_a0, EoCases.__smtx_typeof.case_62 x_a0, EoCases.__smtx_typeof.case_63 x_a0] from rfl)
    otherwise ⟨hl_52, hl_53, hl_54, hl_55⟩ using hl_48 hl_49 hl_50 hl_51
  group_round_step with cases_0_14_eo__24smtx_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_48 x_a0, EoCases.__smtx_typeof.case_49 x_a0, EoCases.__smtx_typeof.case_50 x_a0, EoCases.__smtx_typeof.case_51 x_a0, EoCases.__smtx_typeof.case_52 x_a0, EoCases.__smtx_typeof.case_53 x_a0, EoCases.__smtx_typeof.case_54 x_a0, EoCases.__smtx_typeof.case_55 x_a0, EoCases.__smtx_typeof.case_56 x_a0, EoCases.__smtx_typeof.case_57 x_a0, EoCases.__smtx_typeof.case_58 x_a0, EoCases.__smtx_typeof.case_59 x_a0, EoCases.__smtx_typeof.case_60 x_a0, EoCases.__smtx_typeof.case_61 x_a0, EoCases.__smtx_typeof.case_62 x_a0, EoCases.__smtx_typeof.case_63 x_a0] = [EoCases.__smtx_typeof.case_48 x_a0, EoCases.__smtx_typeof.case_49 x_a0, EoCases.__smtx_typeof.case_50 x_a0, EoCases.__smtx_typeof.case_51 x_a0, EoCases.__smtx_typeof.case_52 x_a0, EoCases.__smtx_typeof.case_53 x_a0, EoCases.__smtx_typeof.case_54 x_a0, EoCases.__smtx_typeof.case_55 x_a0] ++ [EoCases.__smtx_typeof.case_56 x_a0, EoCases.__smtx_typeof.case_57 x_a0, EoCases.__smtx_typeof.case_58 x_a0, EoCases.__smtx_typeof.case_59 x_a0] ++ [EoCases.__smtx_typeof.case_60 x_a0, EoCases.__smtx_typeof.case_61 x_a0, EoCases.__smtx_typeof.case_62 x_a0, EoCases.__smtx_typeof.case_63 x_a0] from rfl)
    otherwise ⟨hl_56, hl_57, hl_58, hl_59⟩ using hl_48 hl_49 hl_50 hl_51 hl_52 hl_53 hl_54 hl_55
  group_round_step with cases_0_15_eo__24smtx_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_48 x_a0, EoCases.__smtx_typeof.case_49 x_a0, EoCases.__smtx_typeof.case_50 x_a0, EoCases.__smtx_typeof.case_51 x_a0, EoCases.__smtx_typeof.case_52 x_a0, EoCases.__smtx_typeof.case_53 x_a0, EoCases.__smtx_typeof.case_54 x_a0, EoCases.__smtx_typeof.case_55 x_a0, EoCases.__smtx_typeof.case_56 x_a0, EoCases.__smtx_typeof.case_57 x_a0, EoCases.__smtx_typeof.case_58 x_a0, EoCases.__smtx_typeof.case_59 x_a0, EoCases.__smtx_typeof.case_60 x_a0, EoCases.__smtx_typeof.case_61 x_a0, EoCases.__smtx_typeof.case_62 x_a0, EoCases.__smtx_typeof.case_63 x_a0] = [EoCases.__smtx_typeof.case_48 x_a0, EoCases.__smtx_typeof.case_49 x_a0, EoCases.__smtx_typeof.case_50 x_a0, EoCases.__smtx_typeof.case_51 x_a0, EoCases.__smtx_typeof.case_52 x_a0, EoCases.__smtx_typeof.case_53 x_a0, EoCases.__smtx_typeof.case_54 x_a0, EoCases.__smtx_typeof.case_55 x_a0, EoCases.__smtx_typeof.case_56 x_a0, EoCases.__smtx_typeof.case_57 x_a0, EoCases.__smtx_typeof.case_58 x_a0, EoCases.__smtx_typeof.case_59 x_a0] ++ [EoCases.__smtx_typeof.case_60 x_a0, EoCases.__smtx_typeof.case_61 x_a0, EoCases.__smtx_typeof.case_62 x_a0, EoCases.__smtx_typeof.case_63 x_a0] ++ [] from rfl)
    otherwise ⟨hl_60, hl_61, hl_62, hl_63⟩ using hl_48 hl_49 hl_50 hl_51 hl_52 hl_53 hl_54 hl_55 hl_56 hl_57 hl_58 hl_59
  group_none hinv4 hG with ⟨hl_48, hl_49, hl_50, hl_51, hl_52, hl_53, hl_54, hl_55, hl_56, hl_57, hl_58, hl_59, hl_60, hl_61, hl_62, hl_63⟩

theorem cases_1_4_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_1_4_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, (∀ d, firstSome [EoCases.__smtx_typeof.case_64 x_a0, EoCases.__smtx_typeof.case_65 x_a0, EoCases.__smtx_typeof.case_66 x_a0, EoCases.__smtx_typeof.case_67 x_a0, EoCases.__smtx_typeof.case_68 x_a0, EoCases.__smtx_typeof.case_69 x_a0, EoCases.__smtx_typeof.case_70 x_a0, EoCases.__smtx_typeof.case_71 x_a0, EoCases.__smtx_typeof.case_72 x_a0, EoCases.__smtx_typeof.case_73 x_a0, EoCases.__smtx_typeof.case_74 x_a0, EoCases.__smtx_typeof.case_75 x_a0, EoCases.__smtx_typeof.case_76 x_a0, EoCases.__smtx_typeof.case_77 x_a0, EoCases.__smtx_typeof.case_78 x_a0, EoCases.__smtx_typeof.case_79 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          ∀ d, firstSome [EoCases.__smtx_typeof.case_64 x_a0, EoCases.__smtx_typeof.case_65 x_a0, EoCases.__smtx_typeof.case_66 x_a0, EoCases.__smtx_typeof.case_67 x_a0, EoCases.__smtx_typeof.case_68 x_a0, EoCases.__smtx_typeof.case_69 x_a0, EoCases.__smtx_typeof.case_70 x_a0, EoCases.__smtx_typeof.case_71 x_a0, EoCases.__smtx_typeof.case_72 x_a0, EoCases.__smtx_typeof.case_73 x_a0, EoCases.__smtx_typeof.case_74 x_a0, EoCases.__smtx_typeof.case_75 x_a0, EoCases.__smtx_typeof.case_76 x_a0, EoCases.__smtx_typeof.case_77 x_a0, EoCases.__smtx_typeof.case_78 x_a0, EoCases.__smtx_typeof.case_79 x_a0] d = __smtx_typeof y0
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_64 x_a0 = none ∧ EoCases.__smtx_typeof.case_65 x_a0 = none ∧ EoCases.__smtx_typeof.case_66 x_a0 = none ∧ EoCases.__smtx_typeof.case_67 x_a0 = none ∧ EoCases.__smtx_typeof.case_68 x_a0 = none ∧ EoCases.__smtx_typeof.case_69 x_a0 = none ∧ EoCases.__smtx_typeof.case_70 x_a0 = none ∧ EoCases.__smtx_typeof.case_71 x_a0 = none ∧ EoCases.__smtx_typeof.case_72 x_a0 = none ∧ EoCases.__smtx_typeof.case_73 x_a0 = none ∧ EoCases.__smtx_typeof.case_74 x_a0 = none ∧ EoCases.__smtx_typeof.case_75 x_a0 = none ∧ EoCases.__smtx_typeof.case_76 x_a0 = none ∧ EoCases.__smtx_typeof.case_77 x_a0 = none ∧ EoCases.__smtx_typeof.case_78 x_a0 = none ∧ EoCases.__smtx_typeof.case_79 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_1_4_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  group_round_step with cases_0_16_eo__24smtx_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_64 x_a0, EoCases.__smtx_typeof.case_65 x_a0, EoCases.__smtx_typeof.case_66 x_a0, EoCases.__smtx_typeof.case_67 x_a0, EoCases.__smtx_typeof.case_68 x_a0, EoCases.__smtx_typeof.case_69 x_a0, EoCases.__smtx_typeof.case_70 x_a0, EoCases.__smtx_typeof.case_71 x_a0, EoCases.__smtx_typeof.case_72 x_a0, EoCases.__smtx_typeof.case_73 x_a0, EoCases.__smtx_typeof.case_74 x_a0, EoCases.__smtx_typeof.case_75 x_a0, EoCases.__smtx_typeof.case_76 x_a0, EoCases.__smtx_typeof.case_77 x_a0, EoCases.__smtx_typeof.case_78 x_a0, EoCases.__smtx_typeof.case_79 x_a0] = [] ++ [EoCases.__smtx_typeof.case_64 x_a0, EoCases.__smtx_typeof.case_65 x_a0, EoCases.__smtx_typeof.case_66 x_a0, EoCases.__smtx_typeof.case_67 x_a0] ++ [EoCases.__smtx_typeof.case_68 x_a0, EoCases.__smtx_typeof.case_69 x_a0, EoCases.__smtx_typeof.case_70 x_a0, EoCases.__smtx_typeof.case_71 x_a0, EoCases.__smtx_typeof.case_72 x_a0, EoCases.__smtx_typeof.case_73 x_a0, EoCases.__smtx_typeof.case_74 x_a0, EoCases.__smtx_typeof.case_75 x_a0, EoCases.__smtx_typeof.case_76 x_a0, EoCases.__smtx_typeof.case_77 x_a0, EoCases.__smtx_typeof.case_78 x_a0, EoCases.__smtx_typeof.case_79 x_a0] from rfl)
    otherwise ⟨hl_64, hl_65, hl_66, hl_67⟩ using
  group_round_step with cases_0_17_eo__24smtx_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_64 x_a0, EoCases.__smtx_typeof.case_65 x_a0, EoCases.__smtx_typeof.case_66 x_a0, EoCases.__smtx_typeof.case_67 x_a0, EoCases.__smtx_typeof.case_68 x_a0, EoCases.__smtx_typeof.case_69 x_a0, EoCases.__smtx_typeof.case_70 x_a0, EoCases.__smtx_typeof.case_71 x_a0, EoCases.__smtx_typeof.case_72 x_a0, EoCases.__smtx_typeof.case_73 x_a0, EoCases.__smtx_typeof.case_74 x_a0, EoCases.__smtx_typeof.case_75 x_a0, EoCases.__smtx_typeof.case_76 x_a0, EoCases.__smtx_typeof.case_77 x_a0, EoCases.__smtx_typeof.case_78 x_a0, EoCases.__smtx_typeof.case_79 x_a0] = [EoCases.__smtx_typeof.case_64 x_a0, EoCases.__smtx_typeof.case_65 x_a0, EoCases.__smtx_typeof.case_66 x_a0, EoCases.__smtx_typeof.case_67 x_a0] ++ [EoCases.__smtx_typeof.case_68 x_a0, EoCases.__smtx_typeof.case_69 x_a0, EoCases.__smtx_typeof.case_70 x_a0, EoCases.__smtx_typeof.case_71 x_a0] ++ [EoCases.__smtx_typeof.case_72 x_a0, EoCases.__smtx_typeof.case_73 x_a0, EoCases.__smtx_typeof.case_74 x_a0, EoCases.__smtx_typeof.case_75 x_a0, EoCases.__smtx_typeof.case_76 x_a0, EoCases.__smtx_typeof.case_77 x_a0, EoCases.__smtx_typeof.case_78 x_a0, EoCases.__smtx_typeof.case_79 x_a0] from rfl)
    otherwise ⟨hl_68, hl_69, hl_70, hl_71⟩ using hl_64 hl_65 hl_66 hl_67
  group_round_step with cases_0_18_eo__24smtx_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_64 x_a0, EoCases.__smtx_typeof.case_65 x_a0, EoCases.__smtx_typeof.case_66 x_a0, EoCases.__smtx_typeof.case_67 x_a0, EoCases.__smtx_typeof.case_68 x_a0, EoCases.__smtx_typeof.case_69 x_a0, EoCases.__smtx_typeof.case_70 x_a0, EoCases.__smtx_typeof.case_71 x_a0, EoCases.__smtx_typeof.case_72 x_a0, EoCases.__smtx_typeof.case_73 x_a0, EoCases.__smtx_typeof.case_74 x_a0, EoCases.__smtx_typeof.case_75 x_a0, EoCases.__smtx_typeof.case_76 x_a0, EoCases.__smtx_typeof.case_77 x_a0, EoCases.__smtx_typeof.case_78 x_a0, EoCases.__smtx_typeof.case_79 x_a0] = [EoCases.__smtx_typeof.case_64 x_a0, EoCases.__smtx_typeof.case_65 x_a0, EoCases.__smtx_typeof.case_66 x_a0, EoCases.__smtx_typeof.case_67 x_a0, EoCases.__smtx_typeof.case_68 x_a0, EoCases.__smtx_typeof.case_69 x_a0, EoCases.__smtx_typeof.case_70 x_a0, EoCases.__smtx_typeof.case_71 x_a0] ++ [EoCases.__smtx_typeof.case_72 x_a0, EoCases.__smtx_typeof.case_73 x_a0, EoCases.__smtx_typeof.case_74 x_a0, EoCases.__smtx_typeof.case_75 x_a0] ++ [EoCases.__smtx_typeof.case_76 x_a0, EoCases.__smtx_typeof.case_77 x_a0, EoCases.__smtx_typeof.case_78 x_a0, EoCases.__smtx_typeof.case_79 x_a0] from rfl)
    otherwise ⟨hl_72, hl_73, hl_74, hl_75⟩ using hl_64 hl_65 hl_66 hl_67 hl_68 hl_69 hl_70 hl_71
  group_round_step with cases_0_19_eo__24smtx_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_64 x_a0, EoCases.__smtx_typeof.case_65 x_a0, EoCases.__smtx_typeof.case_66 x_a0, EoCases.__smtx_typeof.case_67 x_a0, EoCases.__smtx_typeof.case_68 x_a0, EoCases.__smtx_typeof.case_69 x_a0, EoCases.__smtx_typeof.case_70 x_a0, EoCases.__smtx_typeof.case_71 x_a0, EoCases.__smtx_typeof.case_72 x_a0, EoCases.__smtx_typeof.case_73 x_a0, EoCases.__smtx_typeof.case_74 x_a0, EoCases.__smtx_typeof.case_75 x_a0, EoCases.__smtx_typeof.case_76 x_a0, EoCases.__smtx_typeof.case_77 x_a0, EoCases.__smtx_typeof.case_78 x_a0, EoCases.__smtx_typeof.case_79 x_a0] = [EoCases.__smtx_typeof.case_64 x_a0, EoCases.__smtx_typeof.case_65 x_a0, EoCases.__smtx_typeof.case_66 x_a0, EoCases.__smtx_typeof.case_67 x_a0, EoCases.__smtx_typeof.case_68 x_a0, EoCases.__smtx_typeof.case_69 x_a0, EoCases.__smtx_typeof.case_70 x_a0, EoCases.__smtx_typeof.case_71 x_a0, EoCases.__smtx_typeof.case_72 x_a0, EoCases.__smtx_typeof.case_73 x_a0, EoCases.__smtx_typeof.case_74 x_a0, EoCases.__smtx_typeof.case_75 x_a0] ++ [EoCases.__smtx_typeof.case_76 x_a0, EoCases.__smtx_typeof.case_77 x_a0, EoCases.__smtx_typeof.case_78 x_a0, EoCases.__smtx_typeof.case_79 x_a0] ++ [] from rfl)
    otherwise ⟨hl_76, hl_77, hl_78, hl_79⟩ using hl_64 hl_65 hl_66 hl_67 hl_68 hl_69 hl_70 hl_71 hl_72 hl_73 hl_74 hl_75
  group_none hinv4 hG with ⟨hl_64, hl_65, hl_66, hl_67, hl_68, hl_69, hl_70, hl_71, hl_72, hl_73, hl_74, hl_75, hl_76, hl_77, hl_78, hl_79⟩

theorem cases_1_5_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_1_5_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, (∀ d, firstSome [EoCases.__smtx_typeof.case_80 x_a0, EoCases.__smtx_typeof.case_81 x_a0, EoCases.__smtx_typeof.case_82 x_a0, EoCases.__smtx_typeof.case_83 x_a0, EoCases.__smtx_typeof.case_84 x_a0, EoCases.__smtx_typeof.case_85 x_a0, EoCases.__smtx_typeof.case_86 x_a0, EoCases.__smtx_typeof.case_87 x_a0, EoCases.__smtx_typeof.case_88 x_a0, EoCases.__smtx_typeof.case_89 x_a0, EoCases.__smtx_typeof.case_90 x_a0, EoCases.__smtx_typeof.case_91 x_a0, EoCases.__smtx_typeof.case_92 x_a0, EoCases.__smtx_typeof.case_93 x_a0, EoCases.__smtx_typeof.case_94 x_a0, EoCases.__smtx_typeof.case_95 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          ∀ d, firstSome [EoCases.__smtx_typeof.case_80 x_a0, EoCases.__smtx_typeof.case_81 x_a0, EoCases.__smtx_typeof.case_82 x_a0, EoCases.__smtx_typeof.case_83 x_a0, EoCases.__smtx_typeof.case_84 x_a0, EoCases.__smtx_typeof.case_85 x_a0, EoCases.__smtx_typeof.case_86 x_a0, EoCases.__smtx_typeof.case_87 x_a0, EoCases.__smtx_typeof.case_88 x_a0, EoCases.__smtx_typeof.case_89 x_a0, EoCases.__smtx_typeof.case_90 x_a0, EoCases.__smtx_typeof.case_91 x_a0, EoCases.__smtx_typeof.case_92 x_a0, EoCases.__smtx_typeof.case_93 x_a0, EoCases.__smtx_typeof.case_94 x_a0, EoCases.__smtx_typeof.case_95 x_a0] d = __smtx_typeof y0
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_80 x_a0 = none ∧ EoCases.__smtx_typeof.case_81 x_a0 = none ∧ EoCases.__smtx_typeof.case_82 x_a0 = none ∧ EoCases.__smtx_typeof.case_83 x_a0 = none ∧ EoCases.__smtx_typeof.case_84 x_a0 = none ∧ EoCases.__smtx_typeof.case_85 x_a0 = none ∧ EoCases.__smtx_typeof.case_86 x_a0 = none ∧ EoCases.__smtx_typeof.case_87 x_a0 = none ∧ EoCases.__smtx_typeof.case_88 x_a0 = none ∧ EoCases.__smtx_typeof.case_89 x_a0 = none ∧ EoCases.__smtx_typeof.case_90 x_a0 = none ∧ EoCases.__smtx_typeof.case_91 x_a0 = none ∧ EoCases.__smtx_typeof.case_92 x_a0 = none ∧ EoCases.__smtx_typeof.case_93 x_a0 = none ∧ EoCases.__smtx_typeof.case_94 x_a0 = none ∧ EoCases.__smtx_typeof.case_95 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_1_5_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  group_round_step with cases_0_20_eo__24smtx_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_80 x_a0, EoCases.__smtx_typeof.case_81 x_a0, EoCases.__smtx_typeof.case_82 x_a0, EoCases.__smtx_typeof.case_83 x_a0, EoCases.__smtx_typeof.case_84 x_a0, EoCases.__smtx_typeof.case_85 x_a0, EoCases.__smtx_typeof.case_86 x_a0, EoCases.__smtx_typeof.case_87 x_a0, EoCases.__smtx_typeof.case_88 x_a0, EoCases.__smtx_typeof.case_89 x_a0, EoCases.__smtx_typeof.case_90 x_a0, EoCases.__smtx_typeof.case_91 x_a0, EoCases.__smtx_typeof.case_92 x_a0, EoCases.__smtx_typeof.case_93 x_a0, EoCases.__smtx_typeof.case_94 x_a0, EoCases.__smtx_typeof.case_95 x_a0] = [] ++ [EoCases.__smtx_typeof.case_80 x_a0, EoCases.__smtx_typeof.case_81 x_a0, EoCases.__smtx_typeof.case_82 x_a0, EoCases.__smtx_typeof.case_83 x_a0] ++ [EoCases.__smtx_typeof.case_84 x_a0, EoCases.__smtx_typeof.case_85 x_a0, EoCases.__smtx_typeof.case_86 x_a0, EoCases.__smtx_typeof.case_87 x_a0, EoCases.__smtx_typeof.case_88 x_a0, EoCases.__smtx_typeof.case_89 x_a0, EoCases.__smtx_typeof.case_90 x_a0, EoCases.__smtx_typeof.case_91 x_a0, EoCases.__smtx_typeof.case_92 x_a0, EoCases.__smtx_typeof.case_93 x_a0, EoCases.__smtx_typeof.case_94 x_a0, EoCases.__smtx_typeof.case_95 x_a0] from rfl)
    otherwise ⟨hl_80, hl_81, hl_82, hl_83⟩ using
  group_round_step with cases_0_21_eo__24smtx_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_80 x_a0, EoCases.__smtx_typeof.case_81 x_a0, EoCases.__smtx_typeof.case_82 x_a0, EoCases.__smtx_typeof.case_83 x_a0, EoCases.__smtx_typeof.case_84 x_a0, EoCases.__smtx_typeof.case_85 x_a0, EoCases.__smtx_typeof.case_86 x_a0, EoCases.__smtx_typeof.case_87 x_a0, EoCases.__smtx_typeof.case_88 x_a0, EoCases.__smtx_typeof.case_89 x_a0, EoCases.__smtx_typeof.case_90 x_a0, EoCases.__smtx_typeof.case_91 x_a0, EoCases.__smtx_typeof.case_92 x_a0, EoCases.__smtx_typeof.case_93 x_a0, EoCases.__smtx_typeof.case_94 x_a0, EoCases.__smtx_typeof.case_95 x_a0] = [EoCases.__smtx_typeof.case_80 x_a0, EoCases.__smtx_typeof.case_81 x_a0, EoCases.__smtx_typeof.case_82 x_a0, EoCases.__smtx_typeof.case_83 x_a0] ++ [EoCases.__smtx_typeof.case_84 x_a0, EoCases.__smtx_typeof.case_85 x_a0, EoCases.__smtx_typeof.case_86 x_a0, EoCases.__smtx_typeof.case_87 x_a0] ++ [EoCases.__smtx_typeof.case_88 x_a0, EoCases.__smtx_typeof.case_89 x_a0, EoCases.__smtx_typeof.case_90 x_a0, EoCases.__smtx_typeof.case_91 x_a0, EoCases.__smtx_typeof.case_92 x_a0, EoCases.__smtx_typeof.case_93 x_a0, EoCases.__smtx_typeof.case_94 x_a0, EoCases.__smtx_typeof.case_95 x_a0] from rfl)
    otherwise ⟨hl_84, hl_85, hl_86, hl_87⟩ using hl_80 hl_81 hl_82 hl_83
  group_round_step with cases_0_22_eo__24smtx_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_80 x_a0, EoCases.__smtx_typeof.case_81 x_a0, EoCases.__smtx_typeof.case_82 x_a0, EoCases.__smtx_typeof.case_83 x_a0, EoCases.__smtx_typeof.case_84 x_a0, EoCases.__smtx_typeof.case_85 x_a0, EoCases.__smtx_typeof.case_86 x_a0, EoCases.__smtx_typeof.case_87 x_a0, EoCases.__smtx_typeof.case_88 x_a0, EoCases.__smtx_typeof.case_89 x_a0, EoCases.__smtx_typeof.case_90 x_a0, EoCases.__smtx_typeof.case_91 x_a0, EoCases.__smtx_typeof.case_92 x_a0, EoCases.__smtx_typeof.case_93 x_a0, EoCases.__smtx_typeof.case_94 x_a0, EoCases.__smtx_typeof.case_95 x_a0] = [EoCases.__smtx_typeof.case_80 x_a0, EoCases.__smtx_typeof.case_81 x_a0, EoCases.__smtx_typeof.case_82 x_a0, EoCases.__smtx_typeof.case_83 x_a0, EoCases.__smtx_typeof.case_84 x_a0, EoCases.__smtx_typeof.case_85 x_a0, EoCases.__smtx_typeof.case_86 x_a0, EoCases.__smtx_typeof.case_87 x_a0] ++ [EoCases.__smtx_typeof.case_88 x_a0, EoCases.__smtx_typeof.case_89 x_a0, EoCases.__smtx_typeof.case_90 x_a0, EoCases.__smtx_typeof.case_91 x_a0] ++ [EoCases.__smtx_typeof.case_92 x_a0, EoCases.__smtx_typeof.case_93 x_a0, EoCases.__smtx_typeof.case_94 x_a0, EoCases.__smtx_typeof.case_95 x_a0] from rfl)
    otherwise ⟨hl_88, hl_89, hl_90, hl_91⟩ using hl_80 hl_81 hl_82 hl_83 hl_84 hl_85 hl_86 hl_87
  group_round_step with cases_0_23_eo__24smtx_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_80 x_a0, EoCases.__smtx_typeof.case_81 x_a0, EoCases.__smtx_typeof.case_82 x_a0, EoCases.__smtx_typeof.case_83 x_a0, EoCases.__smtx_typeof.case_84 x_a0, EoCases.__smtx_typeof.case_85 x_a0, EoCases.__smtx_typeof.case_86 x_a0, EoCases.__smtx_typeof.case_87 x_a0, EoCases.__smtx_typeof.case_88 x_a0, EoCases.__smtx_typeof.case_89 x_a0, EoCases.__smtx_typeof.case_90 x_a0, EoCases.__smtx_typeof.case_91 x_a0, EoCases.__smtx_typeof.case_92 x_a0, EoCases.__smtx_typeof.case_93 x_a0, EoCases.__smtx_typeof.case_94 x_a0, EoCases.__smtx_typeof.case_95 x_a0] = [EoCases.__smtx_typeof.case_80 x_a0, EoCases.__smtx_typeof.case_81 x_a0, EoCases.__smtx_typeof.case_82 x_a0, EoCases.__smtx_typeof.case_83 x_a0, EoCases.__smtx_typeof.case_84 x_a0, EoCases.__smtx_typeof.case_85 x_a0, EoCases.__smtx_typeof.case_86 x_a0, EoCases.__smtx_typeof.case_87 x_a0, EoCases.__smtx_typeof.case_88 x_a0, EoCases.__smtx_typeof.case_89 x_a0, EoCases.__smtx_typeof.case_90 x_a0, EoCases.__smtx_typeof.case_91 x_a0] ++ [EoCases.__smtx_typeof.case_92 x_a0, EoCases.__smtx_typeof.case_93 x_a0, EoCases.__smtx_typeof.case_94 x_a0, EoCases.__smtx_typeof.case_95 x_a0] ++ [] from rfl)
    otherwise ⟨hl_92, hl_93, hl_94, hl_95⟩ using hl_80 hl_81 hl_82 hl_83 hl_84 hl_85 hl_86 hl_87 hl_88 hl_89 hl_90 hl_91
  group_none hinv4 hG with ⟨hl_80, hl_81, hl_82, hl_83, hl_84, hl_85, hl_86, hl_87, hl_88, hl_89, hl_90, hl_91, hl_92, hl_93, hl_94, hl_95⟩

theorem cases_1_6_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_1_6_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, (∀ d, firstSome [EoCases.__smtx_typeof.case_96 x_a0, EoCases.__smtx_typeof.case_97 x_a0, EoCases.__smtx_typeof.case_98 x_a0, EoCases.__smtx_typeof.case_99 x_a0, EoCases.__smtx_typeof.case_100 x_a0, EoCases.__smtx_typeof.case_101 x_a0, EoCases.__smtx_typeof.case_102 x_a0, EoCases.__smtx_typeof.case_103 x_a0, EoCases.__smtx_typeof.case_104 x_a0, EoCases.__smtx_typeof.case_105 x_a0, EoCases.__smtx_typeof.case_106 x_a0, EoCases.__smtx_typeof.case_107 x_a0, EoCases.__smtx_typeof.case_108 x_a0, EoCases.__smtx_typeof.case_109 x_a0, EoCases.__smtx_typeof.case_110 x_a0, EoCases.__smtx_typeof.case_111 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          ∀ d, firstSome [EoCases.__smtx_typeof.case_96 x_a0, EoCases.__smtx_typeof.case_97 x_a0, EoCases.__smtx_typeof.case_98 x_a0, EoCases.__smtx_typeof.case_99 x_a0, EoCases.__smtx_typeof.case_100 x_a0, EoCases.__smtx_typeof.case_101 x_a0, EoCases.__smtx_typeof.case_102 x_a0, EoCases.__smtx_typeof.case_103 x_a0, EoCases.__smtx_typeof.case_104 x_a0, EoCases.__smtx_typeof.case_105 x_a0, EoCases.__smtx_typeof.case_106 x_a0, EoCases.__smtx_typeof.case_107 x_a0, EoCases.__smtx_typeof.case_108 x_a0, EoCases.__smtx_typeof.case_109 x_a0, EoCases.__smtx_typeof.case_110 x_a0, EoCases.__smtx_typeof.case_111 x_a0] d = __smtx_typeof y0
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_96 x_a0 = none ∧ EoCases.__smtx_typeof.case_97 x_a0 = none ∧ EoCases.__smtx_typeof.case_98 x_a0 = none ∧ EoCases.__smtx_typeof.case_99 x_a0 = none ∧ EoCases.__smtx_typeof.case_100 x_a0 = none ∧ EoCases.__smtx_typeof.case_101 x_a0 = none ∧ EoCases.__smtx_typeof.case_102 x_a0 = none ∧ EoCases.__smtx_typeof.case_103 x_a0 = none ∧ EoCases.__smtx_typeof.case_104 x_a0 = none ∧ EoCases.__smtx_typeof.case_105 x_a0 = none ∧ EoCases.__smtx_typeof.case_106 x_a0 = none ∧ EoCases.__smtx_typeof.case_107 x_a0 = none ∧ EoCases.__smtx_typeof.case_108 x_a0 = none ∧ EoCases.__smtx_typeof.case_109 x_a0 = none ∧ EoCases.__smtx_typeof.case_110 x_a0 = none ∧ EoCases.__smtx_typeof.case_111 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_1_6_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  group_round_step with cases_0_24_eo__24smtx_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_96 x_a0, EoCases.__smtx_typeof.case_97 x_a0, EoCases.__smtx_typeof.case_98 x_a0, EoCases.__smtx_typeof.case_99 x_a0, EoCases.__smtx_typeof.case_100 x_a0, EoCases.__smtx_typeof.case_101 x_a0, EoCases.__smtx_typeof.case_102 x_a0, EoCases.__smtx_typeof.case_103 x_a0, EoCases.__smtx_typeof.case_104 x_a0, EoCases.__smtx_typeof.case_105 x_a0, EoCases.__smtx_typeof.case_106 x_a0, EoCases.__smtx_typeof.case_107 x_a0, EoCases.__smtx_typeof.case_108 x_a0, EoCases.__smtx_typeof.case_109 x_a0, EoCases.__smtx_typeof.case_110 x_a0, EoCases.__smtx_typeof.case_111 x_a0] = [] ++ [EoCases.__smtx_typeof.case_96 x_a0, EoCases.__smtx_typeof.case_97 x_a0, EoCases.__smtx_typeof.case_98 x_a0, EoCases.__smtx_typeof.case_99 x_a0] ++ [EoCases.__smtx_typeof.case_100 x_a0, EoCases.__smtx_typeof.case_101 x_a0, EoCases.__smtx_typeof.case_102 x_a0, EoCases.__smtx_typeof.case_103 x_a0, EoCases.__smtx_typeof.case_104 x_a0, EoCases.__smtx_typeof.case_105 x_a0, EoCases.__smtx_typeof.case_106 x_a0, EoCases.__smtx_typeof.case_107 x_a0, EoCases.__smtx_typeof.case_108 x_a0, EoCases.__smtx_typeof.case_109 x_a0, EoCases.__smtx_typeof.case_110 x_a0, EoCases.__smtx_typeof.case_111 x_a0] from rfl)
    otherwise ⟨hl_96, hl_97, hl_98, hl_99⟩ using
  group_round_step with cases_0_25_eo__24smtx_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_96 x_a0, EoCases.__smtx_typeof.case_97 x_a0, EoCases.__smtx_typeof.case_98 x_a0, EoCases.__smtx_typeof.case_99 x_a0, EoCases.__smtx_typeof.case_100 x_a0, EoCases.__smtx_typeof.case_101 x_a0, EoCases.__smtx_typeof.case_102 x_a0, EoCases.__smtx_typeof.case_103 x_a0, EoCases.__smtx_typeof.case_104 x_a0, EoCases.__smtx_typeof.case_105 x_a0, EoCases.__smtx_typeof.case_106 x_a0, EoCases.__smtx_typeof.case_107 x_a0, EoCases.__smtx_typeof.case_108 x_a0, EoCases.__smtx_typeof.case_109 x_a0, EoCases.__smtx_typeof.case_110 x_a0, EoCases.__smtx_typeof.case_111 x_a0] = [EoCases.__smtx_typeof.case_96 x_a0, EoCases.__smtx_typeof.case_97 x_a0, EoCases.__smtx_typeof.case_98 x_a0, EoCases.__smtx_typeof.case_99 x_a0] ++ [EoCases.__smtx_typeof.case_100 x_a0, EoCases.__smtx_typeof.case_101 x_a0, EoCases.__smtx_typeof.case_102 x_a0, EoCases.__smtx_typeof.case_103 x_a0] ++ [EoCases.__smtx_typeof.case_104 x_a0, EoCases.__smtx_typeof.case_105 x_a0, EoCases.__smtx_typeof.case_106 x_a0, EoCases.__smtx_typeof.case_107 x_a0, EoCases.__smtx_typeof.case_108 x_a0, EoCases.__smtx_typeof.case_109 x_a0, EoCases.__smtx_typeof.case_110 x_a0, EoCases.__smtx_typeof.case_111 x_a0] from rfl)
    otherwise ⟨hl_100, hl_101, hl_102, hl_103⟩ using hl_96 hl_97 hl_98 hl_99
  group_round_step with cases_0_26_eo__24smtx_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_96 x_a0, EoCases.__smtx_typeof.case_97 x_a0, EoCases.__smtx_typeof.case_98 x_a0, EoCases.__smtx_typeof.case_99 x_a0, EoCases.__smtx_typeof.case_100 x_a0, EoCases.__smtx_typeof.case_101 x_a0, EoCases.__smtx_typeof.case_102 x_a0, EoCases.__smtx_typeof.case_103 x_a0, EoCases.__smtx_typeof.case_104 x_a0, EoCases.__smtx_typeof.case_105 x_a0, EoCases.__smtx_typeof.case_106 x_a0, EoCases.__smtx_typeof.case_107 x_a0, EoCases.__smtx_typeof.case_108 x_a0, EoCases.__smtx_typeof.case_109 x_a0, EoCases.__smtx_typeof.case_110 x_a0, EoCases.__smtx_typeof.case_111 x_a0] = [EoCases.__smtx_typeof.case_96 x_a0, EoCases.__smtx_typeof.case_97 x_a0, EoCases.__smtx_typeof.case_98 x_a0, EoCases.__smtx_typeof.case_99 x_a0, EoCases.__smtx_typeof.case_100 x_a0, EoCases.__smtx_typeof.case_101 x_a0, EoCases.__smtx_typeof.case_102 x_a0, EoCases.__smtx_typeof.case_103 x_a0] ++ [EoCases.__smtx_typeof.case_104 x_a0, EoCases.__smtx_typeof.case_105 x_a0, EoCases.__smtx_typeof.case_106 x_a0, EoCases.__smtx_typeof.case_107 x_a0] ++ [EoCases.__smtx_typeof.case_108 x_a0, EoCases.__smtx_typeof.case_109 x_a0, EoCases.__smtx_typeof.case_110 x_a0, EoCases.__smtx_typeof.case_111 x_a0] from rfl)
    otherwise ⟨hl_104, hl_105, hl_106, hl_107⟩ using hl_96 hl_97 hl_98 hl_99 hl_100 hl_101 hl_102 hl_103
  group_round_step with cases_0_27_eo__24smtx_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_96 x_a0, EoCases.__smtx_typeof.case_97 x_a0, EoCases.__smtx_typeof.case_98 x_a0, EoCases.__smtx_typeof.case_99 x_a0, EoCases.__smtx_typeof.case_100 x_a0, EoCases.__smtx_typeof.case_101 x_a0, EoCases.__smtx_typeof.case_102 x_a0, EoCases.__smtx_typeof.case_103 x_a0, EoCases.__smtx_typeof.case_104 x_a0, EoCases.__smtx_typeof.case_105 x_a0, EoCases.__smtx_typeof.case_106 x_a0, EoCases.__smtx_typeof.case_107 x_a0, EoCases.__smtx_typeof.case_108 x_a0, EoCases.__smtx_typeof.case_109 x_a0, EoCases.__smtx_typeof.case_110 x_a0, EoCases.__smtx_typeof.case_111 x_a0] = [EoCases.__smtx_typeof.case_96 x_a0, EoCases.__smtx_typeof.case_97 x_a0, EoCases.__smtx_typeof.case_98 x_a0, EoCases.__smtx_typeof.case_99 x_a0, EoCases.__smtx_typeof.case_100 x_a0, EoCases.__smtx_typeof.case_101 x_a0, EoCases.__smtx_typeof.case_102 x_a0, EoCases.__smtx_typeof.case_103 x_a0, EoCases.__smtx_typeof.case_104 x_a0, EoCases.__smtx_typeof.case_105 x_a0, EoCases.__smtx_typeof.case_106 x_a0, EoCases.__smtx_typeof.case_107 x_a0] ++ [EoCases.__smtx_typeof.case_108 x_a0, EoCases.__smtx_typeof.case_109 x_a0, EoCases.__smtx_typeof.case_110 x_a0, EoCases.__smtx_typeof.case_111 x_a0] ++ [] from rfl)
    otherwise ⟨hl_108, hl_109, hl_110, hl_111⟩ using hl_96 hl_97 hl_98 hl_99 hl_100 hl_101 hl_102 hl_103 hl_104 hl_105 hl_106 hl_107
  group_none hinv4 hG with ⟨hl_96, hl_97, hl_98, hl_99, hl_100, hl_101, hl_102, hl_103, hl_104, hl_105, hl_106, hl_107, hl_108, hl_109, hl_110, hl_111⟩

theorem cases_1_7_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_1_7_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, (∀ d, firstSome [EoCases.__smtx_typeof.case_112 x_a0, EoCases.__smtx_typeof.case_113 x_a0, EoCases.__smtx_typeof.case_114 x_a0, EoCases.__smtx_typeof.case_115 x_a0, EoCases.__smtx_typeof.case_116 x_a0, EoCases.__smtx_typeof.case_117 x_a0, EoCases.__smtx_typeof.case_118 x_a0, EoCases.__smtx_typeof.case_119 x_a0, EoCases.__smtx_typeof.case_120 x_a0, EoCases.__smtx_typeof.case_121 x_a0, EoCases.__smtx_typeof.case_122 x_a0, EoCases.__smtx_typeof.case_123 x_a0, EoCases.__smtx_typeof.case_124 x_a0, EoCases.__smtx_typeof.case_125 x_a0, EoCases.__smtx_typeof.case_126 x_a0, EoCases.__smtx_typeof.case_127 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          ∀ d, firstSome [EoCases.__smtx_typeof.case_112 x_a0, EoCases.__smtx_typeof.case_113 x_a0, EoCases.__smtx_typeof.case_114 x_a0, EoCases.__smtx_typeof.case_115 x_a0, EoCases.__smtx_typeof.case_116 x_a0, EoCases.__smtx_typeof.case_117 x_a0, EoCases.__smtx_typeof.case_118 x_a0, EoCases.__smtx_typeof.case_119 x_a0, EoCases.__smtx_typeof.case_120 x_a0, EoCases.__smtx_typeof.case_121 x_a0, EoCases.__smtx_typeof.case_122 x_a0, EoCases.__smtx_typeof.case_123 x_a0, EoCases.__smtx_typeof.case_124 x_a0, EoCases.__smtx_typeof.case_125 x_a0, EoCases.__smtx_typeof.case_126 x_a0, EoCases.__smtx_typeof.case_127 x_a0] d = __smtx_typeof y0
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_112 x_a0 = none ∧ EoCases.__smtx_typeof.case_113 x_a0 = none ∧ EoCases.__smtx_typeof.case_114 x_a0 = none ∧ EoCases.__smtx_typeof.case_115 x_a0 = none ∧ EoCases.__smtx_typeof.case_116 x_a0 = none ∧ EoCases.__smtx_typeof.case_117 x_a0 = none ∧ EoCases.__smtx_typeof.case_118 x_a0 = none ∧ EoCases.__smtx_typeof.case_119 x_a0 = none ∧ EoCases.__smtx_typeof.case_120 x_a0 = none ∧ EoCases.__smtx_typeof.case_121 x_a0 = none ∧ EoCases.__smtx_typeof.case_122 x_a0 = none ∧ EoCases.__smtx_typeof.case_123 x_a0 = none ∧ EoCases.__smtx_typeof.case_124 x_a0 = none ∧ EoCases.__smtx_typeof.case_125 x_a0 = none ∧ EoCases.__smtx_typeof.case_126 x_a0 = none ∧ EoCases.__smtx_typeof.case_127 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_1_7_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  group_round_step with cases_0_28_eo__24smtx_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_112 x_a0, EoCases.__smtx_typeof.case_113 x_a0, EoCases.__smtx_typeof.case_114 x_a0, EoCases.__smtx_typeof.case_115 x_a0, EoCases.__smtx_typeof.case_116 x_a0, EoCases.__smtx_typeof.case_117 x_a0, EoCases.__smtx_typeof.case_118 x_a0, EoCases.__smtx_typeof.case_119 x_a0, EoCases.__smtx_typeof.case_120 x_a0, EoCases.__smtx_typeof.case_121 x_a0, EoCases.__smtx_typeof.case_122 x_a0, EoCases.__smtx_typeof.case_123 x_a0, EoCases.__smtx_typeof.case_124 x_a0, EoCases.__smtx_typeof.case_125 x_a0, EoCases.__smtx_typeof.case_126 x_a0, EoCases.__smtx_typeof.case_127 x_a0] = [] ++ [EoCases.__smtx_typeof.case_112 x_a0, EoCases.__smtx_typeof.case_113 x_a0, EoCases.__smtx_typeof.case_114 x_a0, EoCases.__smtx_typeof.case_115 x_a0] ++ [EoCases.__smtx_typeof.case_116 x_a0, EoCases.__smtx_typeof.case_117 x_a0, EoCases.__smtx_typeof.case_118 x_a0, EoCases.__smtx_typeof.case_119 x_a0, EoCases.__smtx_typeof.case_120 x_a0, EoCases.__smtx_typeof.case_121 x_a0, EoCases.__smtx_typeof.case_122 x_a0, EoCases.__smtx_typeof.case_123 x_a0, EoCases.__smtx_typeof.case_124 x_a0, EoCases.__smtx_typeof.case_125 x_a0, EoCases.__smtx_typeof.case_126 x_a0, EoCases.__smtx_typeof.case_127 x_a0] from rfl)
    otherwise ⟨hl_112, hl_113, hl_114, hl_115⟩ using
  group_round_step with cases_0_29_eo__24smtx_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_112 x_a0, EoCases.__smtx_typeof.case_113 x_a0, EoCases.__smtx_typeof.case_114 x_a0, EoCases.__smtx_typeof.case_115 x_a0, EoCases.__smtx_typeof.case_116 x_a0, EoCases.__smtx_typeof.case_117 x_a0, EoCases.__smtx_typeof.case_118 x_a0, EoCases.__smtx_typeof.case_119 x_a0, EoCases.__smtx_typeof.case_120 x_a0, EoCases.__smtx_typeof.case_121 x_a0, EoCases.__smtx_typeof.case_122 x_a0, EoCases.__smtx_typeof.case_123 x_a0, EoCases.__smtx_typeof.case_124 x_a0, EoCases.__smtx_typeof.case_125 x_a0, EoCases.__smtx_typeof.case_126 x_a0, EoCases.__smtx_typeof.case_127 x_a0] = [EoCases.__smtx_typeof.case_112 x_a0, EoCases.__smtx_typeof.case_113 x_a0, EoCases.__smtx_typeof.case_114 x_a0, EoCases.__smtx_typeof.case_115 x_a0] ++ [EoCases.__smtx_typeof.case_116 x_a0, EoCases.__smtx_typeof.case_117 x_a0, EoCases.__smtx_typeof.case_118 x_a0, EoCases.__smtx_typeof.case_119 x_a0] ++ [EoCases.__smtx_typeof.case_120 x_a0, EoCases.__smtx_typeof.case_121 x_a0, EoCases.__smtx_typeof.case_122 x_a0, EoCases.__smtx_typeof.case_123 x_a0, EoCases.__smtx_typeof.case_124 x_a0, EoCases.__smtx_typeof.case_125 x_a0, EoCases.__smtx_typeof.case_126 x_a0, EoCases.__smtx_typeof.case_127 x_a0] from rfl)
    otherwise ⟨hl_116, hl_117, hl_118, hl_119⟩ using hl_112 hl_113 hl_114 hl_115
  group_round_step with cases_0_30_eo__24smtx_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_112 x_a0, EoCases.__smtx_typeof.case_113 x_a0, EoCases.__smtx_typeof.case_114 x_a0, EoCases.__smtx_typeof.case_115 x_a0, EoCases.__smtx_typeof.case_116 x_a0, EoCases.__smtx_typeof.case_117 x_a0, EoCases.__smtx_typeof.case_118 x_a0, EoCases.__smtx_typeof.case_119 x_a0, EoCases.__smtx_typeof.case_120 x_a0, EoCases.__smtx_typeof.case_121 x_a0, EoCases.__smtx_typeof.case_122 x_a0, EoCases.__smtx_typeof.case_123 x_a0, EoCases.__smtx_typeof.case_124 x_a0, EoCases.__smtx_typeof.case_125 x_a0, EoCases.__smtx_typeof.case_126 x_a0, EoCases.__smtx_typeof.case_127 x_a0] = [EoCases.__smtx_typeof.case_112 x_a0, EoCases.__smtx_typeof.case_113 x_a0, EoCases.__smtx_typeof.case_114 x_a0, EoCases.__smtx_typeof.case_115 x_a0, EoCases.__smtx_typeof.case_116 x_a0, EoCases.__smtx_typeof.case_117 x_a0, EoCases.__smtx_typeof.case_118 x_a0, EoCases.__smtx_typeof.case_119 x_a0] ++ [EoCases.__smtx_typeof.case_120 x_a0, EoCases.__smtx_typeof.case_121 x_a0, EoCases.__smtx_typeof.case_122 x_a0, EoCases.__smtx_typeof.case_123 x_a0] ++ [EoCases.__smtx_typeof.case_124 x_a0, EoCases.__smtx_typeof.case_125 x_a0, EoCases.__smtx_typeof.case_126 x_a0, EoCases.__smtx_typeof.case_127 x_a0] from rfl)
    otherwise ⟨hl_120, hl_121, hl_122, hl_123⟩ using hl_112 hl_113 hl_114 hl_115 hl_116 hl_117 hl_118 hl_119
  group_round_step with cases_0_31_eo__24smtx_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_112 x_a0, EoCases.__smtx_typeof.case_113 x_a0, EoCases.__smtx_typeof.case_114 x_a0, EoCases.__smtx_typeof.case_115 x_a0, EoCases.__smtx_typeof.case_116 x_a0, EoCases.__smtx_typeof.case_117 x_a0, EoCases.__smtx_typeof.case_118 x_a0, EoCases.__smtx_typeof.case_119 x_a0, EoCases.__smtx_typeof.case_120 x_a0, EoCases.__smtx_typeof.case_121 x_a0, EoCases.__smtx_typeof.case_122 x_a0, EoCases.__smtx_typeof.case_123 x_a0, EoCases.__smtx_typeof.case_124 x_a0, EoCases.__smtx_typeof.case_125 x_a0, EoCases.__smtx_typeof.case_126 x_a0, EoCases.__smtx_typeof.case_127 x_a0] = [EoCases.__smtx_typeof.case_112 x_a0, EoCases.__smtx_typeof.case_113 x_a0, EoCases.__smtx_typeof.case_114 x_a0, EoCases.__smtx_typeof.case_115 x_a0, EoCases.__smtx_typeof.case_116 x_a0, EoCases.__smtx_typeof.case_117 x_a0, EoCases.__smtx_typeof.case_118 x_a0, EoCases.__smtx_typeof.case_119 x_a0, EoCases.__smtx_typeof.case_120 x_a0, EoCases.__smtx_typeof.case_121 x_a0, EoCases.__smtx_typeof.case_122 x_a0, EoCases.__smtx_typeof.case_123 x_a0] ++ [EoCases.__smtx_typeof.case_124 x_a0, EoCases.__smtx_typeof.case_125 x_a0, EoCases.__smtx_typeof.case_126 x_a0, EoCases.__smtx_typeof.case_127 x_a0] ++ [] from rfl)
    otherwise ⟨hl_124, hl_125, hl_126, hl_127⟩ using hl_112 hl_113 hl_114 hl_115 hl_116 hl_117 hl_118 hl_119 hl_120 hl_121 hl_122 hl_123
  group_none hinv4 hG with ⟨hl_112, hl_113, hl_114, hl_115, hl_116, hl_117, hl_118, hl_119, hl_120, hl_121, hl_122, hl_123, hl_124, hl_125, hl_126, hl_127⟩

theorem cases_1_8_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_1_8_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, (∀ d, firstSome [EoCases.__smtx_typeof.case_128 x_a0, EoCases.__smtx_typeof.case_129 x_a0, EoCases.__smtx_typeof.case_130 x_a0, EoCases.__smtx_typeof.case_131 x_a0, EoCases.__smtx_typeof.case_132 x_a0, EoCases.__smtx_typeof.case_133 x_a0, EoCases.__smtx_typeof.case_134 x_a0, EoCases.__smtx_typeof.case_135 x_a0, EoCases.__smtx_typeof.case_136 x_a0, EoCases.__smtx_typeof.case_137 x_a0, EoCases.__smtx_typeof.case_138 x_a0, EoCases.__smtx_typeof.case_139 x_a0, EoCases.__smtx_typeof.case_140 x_a0, EoCases.__smtx_typeof.case_141 x_a0, EoCases.__smtx_typeof.case_142 x_a0, EoCases.__smtx_typeof.case_143 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          ∀ d, firstSome [EoCases.__smtx_typeof.case_128 x_a0, EoCases.__smtx_typeof.case_129 x_a0, EoCases.__smtx_typeof.case_130 x_a0, EoCases.__smtx_typeof.case_131 x_a0, EoCases.__smtx_typeof.case_132 x_a0, EoCases.__smtx_typeof.case_133 x_a0, EoCases.__smtx_typeof.case_134 x_a0, EoCases.__smtx_typeof.case_135 x_a0, EoCases.__smtx_typeof.case_136 x_a0, EoCases.__smtx_typeof.case_137 x_a0, EoCases.__smtx_typeof.case_138 x_a0, EoCases.__smtx_typeof.case_139 x_a0, EoCases.__smtx_typeof.case_140 x_a0, EoCases.__smtx_typeof.case_141 x_a0, EoCases.__smtx_typeof.case_142 x_a0, EoCases.__smtx_typeof.case_143 x_a0] d = __smtx_typeof y0
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_128 x_a0 = none ∧ EoCases.__smtx_typeof.case_129 x_a0 = none ∧ EoCases.__smtx_typeof.case_130 x_a0 = none ∧ EoCases.__smtx_typeof.case_131 x_a0 = none ∧ EoCases.__smtx_typeof.case_132 x_a0 = none ∧ EoCases.__smtx_typeof.case_133 x_a0 = none ∧ EoCases.__smtx_typeof.case_134 x_a0 = none ∧ EoCases.__smtx_typeof.case_135 x_a0 = none ∧ EoCases.__smtx_typeof.case_136 x_a0 = none ∧ EoCases.__smtx_typeof.case_137 x_a0 = none ∧ EoCases.__smtx_typeof.case_138 x_a0 = none ∧ EoCases.__smtx_typeof.case_139 x_a0 = none ∧ EoCases.__smtx_typeof.case_140 x_a0 = none ∧ EoCases.__smtx_typeof.case_141 x_a0 = none ∧ EoCases.__smtx_typeof.case_142 x_a0 = none ∧ EoCases.__smtx_typeof.case_143 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_1_8_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  group_round_step with cases_0_32_eo__24smtx_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_128 x_a0, EoCases.__smtx_typeof.case_129 x_a0, EoCases.__smtx_typeof.case_130 x_a0, EoCases.__smtx_typeof.case_131 x_a0, EoCases.__smtx_typeof.case_132 x_a0, EoCases.__smtx_typeof.case_133 x_a0, EoCases.__smtx_typeof.case_134 x_a0, EoCases.__smtx_typeof.case_135 x_a0, EoCases.__smtx_typeof.case_136 x_a0, EoCases.__smtx_typeof.case_137 x_a0, EoCases.__smtx_typeof.case_138 x_a0, EoCases.__smtx_typeof.case_139 x_a0, EoCases.__smtx_typeof.case_140 x_a0, EoCases.__smtx_typeof.case_141 x_a0, EoCases.__smtx_typeof.case_142 x_a0, EoCases.__smtx_typeof.case_143 x_a0] = [] ++ [EoCases.__smtx_typeof.case_128 x_a0, EoCases.__smtx_typeof.case_129 x_a0, EoCases.__smtx_typeof.case_130 x_a0, EoCases.__smtx_typeof.case_131 x_a0] ++ [EoCases.__smtx_typeof.case_132 x_a0, EoCases.__smtx_typeof.case_133 x_a0, EoCases.__smtx_typeof.case_134 x_a0, EoCases.__smtx_typeof.case_135 x_a0, EoCases.__smtx_typeof.case_136 x_a0, EoCases.__smtx_typeof.case_137 x_a0, EoCases.__smtx_typeof.case_138 x_a0, EoCases.__smtx_typeof.case_139 x_a0, EoCases.__smtx_typeof.case_140 x_a0, EoCases.__smtx_typeof.case_141 x_a0, EoCases.__smtx_typeof.case_142 x_a0, EoCases.__smtx_typeof.case_143 x_a0] from rfl)
    otherwise ⟨hl_128, hl_129, hl_130, hl_131⟩ using
  group_round_step with cases_0_33_eo__24smtx_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_128 x_a0, EoCases.__smtx_typeof.case_129 x_a0, EoCases.__smtx_typeof.case_130 x_a0, EoCases.__smtx_typeof.case_131 x_a0, EoCases.__smtx_typeof.case_132 x_a0, EoCases.__smtx_typeof.case_133 x_a0, EoCases.__smtx_typeof.case_134 x_a0, EoCases.__smtx_typeof.case_135 x_a0, EoCases.__smtx_typeof.case_136 x_a0, EoCases.__smtx_typeof.case_137 x_a0, EoCases.__smtx_typeof.case_138 x_a0, EoCases.__smtx_typeof.case_139 x_a0, EoCases.__smtx_typeof.case_140 x_a0, EoCases.__smtx_typeof.case_141 x_a0, EoCases.__smtx_typeof.case_142 x_a0, EoCases.__smtx_typeof.case_143 x_a0] = [EoCases.__smtx_typeof.case_128 x_a0, EoCases.__smtx_typeof.case_129 x_a0, EoCases.__smtx_typeof.case_130 x_a0, EoCases.__smtx_typeof.case_131 x_a0] ++ [EoCases.__smtx_typeof.case_132 x_a0, EoCases.__smtx_typeof.case_133 x_a0, EoCases.__smtx_typeof.case_134 x_a0, EoCases.__smtx_typeof.case_135 x_a0] ++ [EoCases.__smtx_typeof.case_136 x_a0, EoCases.__smtx_typeof.case_137 x_a0, EoCases.__smtx_typeof.case_138 x_a0, EoCases.__smtx_typeof.case_139 x_a0, EoCases.__smtx_typeof.case_140 x_a0, EoCases.__smtx_typeof.case_141 x_a0, EoCases.__smtx_typeof.case_142 x_a0, EoCases.__smtx_typeof.case_143 x_a0] from rfl)
    otherwise ⟨hl_132, hl_133, hl_134, hl_135⟩ using hl_128 hl_129 hl_130 hl_131
  group_round_step with cases_0_34_eo__24smtx_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_128 x_a0, EoCases.__smtx_typeof.case_129 x_a0, EoCases.__smtx_typeof.case_130 x_a0, EoCases.__smtx_typeof.case_131 x_a0, EoCases.__smtx_typeof.case_132 x_a0, EoCases.__smtx_typeof.case_133 x_a0, EoCases.__smtx_typeof.case_134 x_a0, EoCases.__smtx_typeof.case_135 x_a0, EoCases.__smtx_typeof.case_136 x_a0, EoCases.__smtx_typeof.case_137 x_a0, EoCases.__smtx_typeof.case_138 x_a0, EoCases.__smtx_typeof.case_139 x_a0, EoCases.__smtx_typeof.case_140 x_a0, EoCases.__smtx_typeof.case_141 x_a0, EoCases.__smtx_typeof.case_142 x_a0, EoCases.__smtx_typeof.case_143 x_a0] = [EoCases.__smtx_typeof.case_128 x_a0, EoCases.__smtx_typeof.case_129 x_a0, EoCases.__smtx_typeof.case_130 x_a0, EoCases.__smtx_typeof.case_131 x_a0, EoCases.__smtx_typeof.case_132 x_a0, EoCases.__smtx_typeof.case_133 x_a0, EoCases.__smtx_typeof.case_134 x_a0, EoCases.__smtx_typeof.case_135 x_a0] ++ [EoCases.__smtx_typeof.case_136 x_a0, EoCases.__smtx_typeof.case_137 x_a0, EoCases.__smtx_typeof.case_138 x_a0, EoCases.__smtx_typeof.case_139 x_a0] ++ [EoCases.__smtx_typeof.case_140 x_a0, EoCases.__smtx_typeof.case_141 x_a0, EoCases.__smtx_typeof.case_142 x_a0, EoCases.__smtx_typeof.case_143 x_a0] from rfl)
    otherwise ⟨hl_136, hl_137, hl_138, hl_139⟩ using hl_128 hl_129 hl_130 hl_131 hl_132 hl_133 hl_134 hl_135
  group_round_step with cases_0_35_eo__24smtx_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_128 x_a0, EoCases.__smtx_typeof.case_129 x_a0, EoCases.__smtx_typeof.case_130 x_a0, EoCases.__smtx_typeof.case_131 x_a0, EoCases.__smtx_typeof.case_132 x_a0, EoCases.__smtx_typeof.case_133 x_a0, EoCases.__smtx_typeof.case_134 x_a0, EoCases.__smtx_typeof.case_135 x_a0, EoCases.__smtx_typeof.case_136 x_a0, EoCases.__smtx_typeof.case_137 x_a0, EoCases.__smtx_typeof.case_138 x_a0, EoCases.__smtx_typeof.case_139 x_a0, EoCases.__smtx_typeof.case_140 x_a0, EoCases.__smtx_typeof.case_141 x_a0, EoCases.__smtx_typeof.case_142 x_a0, EoCases.__smtx_typeof.case_143 x_a0] = [EoCases.__smtx_typeof.case_128 x_a0, EoCases.__smtx_typeof.case_129 x_a0, EoCases.__smtx_typeof.case_130 x_a0, EoCases.__smtx_typeof.case_131 x_a0, EoCases.__smtx_typeof.case_132 x_a0, EoCases.__smtx_typeof.case_133 x_a0, EoCases.__smtx_typeof.case_134 x_a0, EoCases.__smtx_typeof.case_135 x_a0, EoCases.__smtx_typeof.case_136 x_a0, EoCases.__smtx_typeof.case_137 x_a0, EoCases.__smtx_typeof.case_138 x_a0, EoCases.__smtx_typeof.case_139 x_a0] ++ [EoCases.__smtx_typeof.case_140 x_a0, EoCases.__smtx_typeof.case_141 x_a0, EoCases.__smtx_typeof.case_142 x_a0, EoCases.__smtx_typeof.case_143 x_a0] ++ [] from rfl)
    otherwise ⟨hl_140, hl_141, hl_142, hl_143⟩ using hl_128 hl_129 hl_130 hl_131 hl_132 hl_133 hl_134 hl_135 hl_136 hl_137 hl_138 hl_139
  group_none hinv4 hG with ⟨hl_128, hl_129, hl_130, hl_131, hl_132, hl_133, hl_134, hl_135, hl_136, hl_137, hl_138, hl_139, hl_140, hl_141, hl_142, hl_143⟩

theorem cases_1_9_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_1_9_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, (∀ d, firstSome [EoCases.__smtx_typeof.case_144 x_a0, EoCases.__smtx_typeof.case_145 x_a0, EoCases.__smtx_typeof.case_146 x_a0, EoCases.__smtx_typeof.case_147 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          ∀ d, firstSome [EoCases.__smtx_typeof.case_144 x_a0, EoCases.__smtx_typeof.case_145 x_a0, EoCases.__smtx_typeof.case_146 x_a0, EoCases.__smtx_typeof.case_147 x_a0] d = __smtx_typeof y0
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_144 x_a0 = none ∧ EoCases.__smtx_typeof.case_145 x_a0 = none ∧ EoCases.__smtx_typeof.case_146 x_a0 = none ∧ EoCases.__smtx_typeof.case_147 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_1_9_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  group_round_step with cases_0_36_eo__24smtx_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_144 x_a0, EoCases.__smtx_typeof.case_145 x_a0, EoCases.__smtx_typeof.case_146 x_a0, EoCases.__smtx_typeof.case_147 x_a0] = [] ++ [EoCases.__smtx_typeof.case_144 x_a0, EoCases.__smtx_typeof.case_145 x_a0, EoCases.__smtx_typeof.case_146 x_a0, EoCases.__smtx_typeof.case_147 x_a0] ++ [] from rfl)
    otherwise ⟨hl_144, hl_145, hl_146, hl_147⟩ using
  group_none hinv1 hG with ⟨hl_144, hl_145, hl_146, hl_147⟩

theorem cases_2_0_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_2_0_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, (∀ d, firstSome [EoCases.__smtx_typeof.case_0 x_a0, EoCases.__smtx_typeof.case_1 x_a0, EoCases.__smtx_typeof.case_2 x_a0, EoCases.__smtx_typeof.case_3 x_a0, EoCases.__smtx_typeof.case_4 x_a0, EoCases.__smtx_typeof.case_5 x_a0, EoCases.__smtx_typeof.case_6 x_a0, EoCases.__smtx_typeof.case_7 x_a0, EoCases.__smtx_typeof.case_8 x_a0, EoCases.__smtx_typeof.case_9 x_a0, EoCases.__smtx_typeof.case_10 x_a0, EoCases.__smtx_typeof.case_11 x_a0, EoCases.__smtx_typeof.case_12 x_a0, EoCases.__smtx_typeof.case_13 x_a0, EoCases.__smtx_typeof.case_14 x_a0, EoCases.__smtx_typeof.case_15 x_a0, EoCases.__smtx_typeof.case_16 x_a0, EoCases.__smtx_typeof.case_17 x_a0, EoCases.__smtx_typeof.case_18 x_a0, EoCases.__smtx_typeof.case_19 x_a0, EoCases.__smtx_typeof.case_20 x_a0, EoCases.__smtx_typeof.case_21 x_a0, EoCases.__smtx_typeof.case_22 x_a0, EoCases.__smtx_typeof.case_23 x_a0, EoCases.__smtx_typeof.case_24 x_a0, EoCases.__smtx_typeof.case_25 x_a0, EoCases.__smtx_typeof.case_26 x_a0, EoCases.__smtx_typeof.case_27 x_a0, EoCases.__smtx_typeof.case_28 x_a0, EoCases.__smtx_typeof.case_29 x_a0, EoCases.__smtx_typeof.case_30 x_a0, EoCases.__smtx_typeof.case_31 x_a0, EoCases.__smtx_typeof.case_32 x_a0, EoCases.__smtx_typeof.case_33 x_a0, EoCases.__smtx_typeof.case_34 x_a0, EoCases.__smtx_typeof.case_35 x_a0, EoCases.__smtx_typeof.case_36 x_a0, EoCases.__smtx_typeof.case_37 x_a0, EoCases.__smtx_typeof.case_38 x_a0, EoCases.__smtx_typeof.case_39 x_a0, EoCases.__smtx_typeof.case_40 x_a0, EoCases.__smtx_typeof.case_41 x_a0, EoCases.__smtx_typeof.case_42 x_a0, EoCases.__smtx_typeof.case_43 x_a0, EoCases.__smtx_typeof.case_44 x_a0, EoCases.__smtx_typeof.case_45 x_a0, EoCases.__smtx_typeof.case_46 x_a0, EoCases.__smtx_typeof.case_47 x_a0, EoCases.__smtx_typeof.case_48 x_a0, EoCases.__smtx_typeof.case_49 x_a0, EoCases.__smtx_typeof.case_50 x_a0, EoCases.__smtx_typeof.case_51 x_a0, EoCases.__smtx_typeof.case_52 x_a0, EoCases.__smtx_typeof.case_53 x_a0, EoCases.__smtx_typeof.case_54 x_a0, EoCases.__smtx_typeof.case_55 x_a0, EoCases.__smtx_typeof.case_56 x_a0, EoCases.__smtx_typeof.case_57 x_a0, EoCases.__smtx_typeof.case_58 x_a0, EoCases.__smtx_typeof.case_59 x_a0, EoCases.__smtx_typeof.case_60 x_a0, EoCases.__smtx_typeof.case_61 x_a0, EoCases.__smtx_typeof.case_62 x_a0, EoCases.__smtx_typeof.case_63 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          ∀ d, firstSome [EoCases.__smtx_typeof.case_0 x_a0, EoCases.__smtx_typeof.case_1 x_a0, EoCases.__smtx_typeof.case_2 x_a0, EoCases.__smtx_typeof.case_3 x_a0, EoCases.__smtx_typeof.case_4 x_a0, EoCases.__smtx_typeof.case_5 x_a0, EoCases.__smtx_typeof.case_6 x_a0, EoCases.__smtx_typeof.case_7 x_a0, EoCases.__smtx_typeof.case_8 x_a0, EoCases.__smtx_typeof.case_9 x_a0, EoCases.__smtx_typeof.case_10 x_a0, EoCases.__smtx_typeof.case_11 x_a0, EoCases.__smtx_typeof.case_12 x_a0, EoCases.__smtx_typeof.case_13 x_a0, EoCases.__smtx_typeof.case_14 x_a0, EoCases.__smtx_typeof.case_15 x_a0, EoCases.__smtx_typeof.case_16 x_a0, EoCases.__smtx_typeof.case_17 x_a0, EoCases.__smtx_typeof.case_18 x_a0, EoCases.__smtx_typeof.case_19 x_a0, EoCases.__smtx_typeof.case_20 x_a0, EoCases.__smtx_typeof.case_21 x_a0, EoCases.__smtx_typeof.case_22 x_a0, EoCases.__smtx_typeof.case_23 x_a0, EoCases.__smtx_typeof.case_24 x_a0, EoCases.__smtx_typeof.case_25 x_a0, EoCases.__smtx_typeof.case_26 x_a0, EoCases.__smtx_typeof.case_27 x_a0, EoCases.__smtx_typeof.case_28 x_a0, EoCases.__smtx_typeof.case_29 x_a0, EoCases.__smtx_typeof.case_30 x_a0, EoCases.__smtx_typeof.case_31 x_a0, EoCases.__smtx_typeof.case_32 x_a0, EoCases.__smtx_typeof.case_33 x_a0, EoCases.__smtx_typeof.case_34 x_a0, EoCases.__smtx_typeof.case_35 x_a0, EoCases.__smtx_typeof.case_36 x_a0, EoCases.__smtx_typeof.case_37 x_a0, EoCases.__smtx_typeof.case_38 x_a0, EoCases.__smtx_typeof.case_39 x_a0, EoCases.__smtx_typeof.case_40 x_a0, EoCases.__smtx_typeof.case_41 x_a0, EoCases.__smtx_typeof.case_42 x_a0, EoCases.__smtx_typeof.case_43 x_a0, EoCases.__smtx_typeof.case_44 x_a0, EoCases.__smtx_typeof.case_45 x_a0, EoCases.__smtx_typeof.case_46 x_a0, EoCases.__smtx_typeof.case_47 x_a0, EoCases.__smtx_typeof.case_48 x_a0, EoCases.__smtx_typeof.case_49 x_a0, EoCases.__smtx_typeof.case_50 x_a0, EoCases.__smtx_typeof.case_51 x_a0, EoCases.__smtx_typeof.case_52 x_a0, EoCases.__smtx_typeof.case_53 x_a0, EoCases.__smtx_typeof.case_54 x_a0, EoCases.__smtx_typeof.case_55 x_a0, EoCases.__smtx_typeof.case_56 x_a0, EoCases.__smtx_typeof.case_57 x_a0, EoCases.__smtx_typeof.case_58 x_a0, EoCases.__smtx_typeof.case_59 x_a0, EoCases.__smtx_typeof.case_60 x_a0, EoCases.__smtx_typeof.case_61 x_a0, EoCases.__smtx_typeof.case_62 x_a0, EoCases.__smtx_typeof.case_63 x_a0] d = __smtx_typeof y0
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_0 x_a0 = none ∧ EoCases.__smtx_typeof.case_1 x_a0 = none ∧ EoCases.__smtx_typeof.case_2 x_a0 = none ∧ EoCases.__smtx_typeof.case_3 x_a0 = none ∧ EoCases.__smtx_typeof.case_4 x_a0 = none ∧ EoCases.__smtx_typeof.case_5 x_a0 = none ∧ EoCases.__smtx_typeof.case_6 x_a0 = none ∧ EoCases.__smtx_typeof.case_7 x_a0 = none ∧ EoCases.__smtx_typeof.case_8 x_a0 = none ∧ EoCases.__smtx_typeof.case_9 x_a0 = none ∧ EoCases.__smtx_typeof.case_10 x_a0 = none ∧ EoCases.__smtx_typeof.case_11 x_a0 = none ∧ EoCases.__smtx_typeof.case_12 x_a0 = none ∧ EoCases.__smtx_typeof.case_13 x_a0 = none ∧ EoCases.__smtx_typeof.case_14 x_a0 = none ∧ EoCases.__smtx_typeof.case_15 x_a0 = none ∧ EoCases.__smtx_typeof.case_16 x_a0 = none ∧ EoCases.__smtx_typeof.case_17 x_a0 = none ∧ EoCases.__smtx_typeof.case_18 x_a0 = none ∧ EoCases.__smtx_typeof.case_19 x_a0 = none ∧ EoCases.__smtx_typeof.case_20 x_a0 = none ∧ EoCases.__smtx_typeof.case_21 x_a0 = none ∧ EoCases.__smtx_typeof.case_22 x_a0 = none ∧ EoCases.__smtx_typeof.case_23 x_a0 = none ∧ EoCases.__smtx_typeof.case_24 x_a0 = none ∧ EoCases.__smtx_typeof.case_25 x_a0 = none ∧ EoCases.__smtx_typeof.case_26 x_a0 = none ∧ EoCases.__smtx_typeof.case_27 x_a0 = none ∧ EoCases.__smtx_typeof.case_28 x_a0 = none ∧ EoCases.__smtx_typeof.case_29 x_a0 = none ∧ EoCases.__smtx_typeof.case_30 x_a0 = none ∧ EoCases.__smtx_typeof.case_31 x_a0 = none ∧ EoCases.__smtx_typeof.case_32 x_a0 = none ∧ EoCases.__smtx_typeof.case_33 x_a0 = none ∧ EoCases.__smtx_typeof.case_34 x_a0 = none ∧ EoCases.__smtx_typeof.case_35 x_a0 = none ∧ EoCases.__smtx_typeof.case_36 x_a0 = none ∧ EoCases.__smtx_typeof.case_37 x_a0 = none ∧ EoCases.__smtx_typeof.case_38 x_a0 = none ∧ EoCases.__smtx_typeof.case_39 x_a0 = none ∧ EoCases.__smtx_typeof.case_40 x_a0 = none ∧ EoCases.__smtx_typeof.case_41 x_a0 = none ∧ EoCases.__smtx_typeof.case_42 x_a0 = none ∧ EoCases.__smtx_typeof.case_43 x_a0 = none ∧ EoCases.__smtx_typeof.case_44 x_a0 = none ∧ EoCases.__smtx_typeof.case_45 x_a0 = none ∧ EoCases.__smtx_typeof.case_46 x_a0 = none ∧ EoCases.__smtx_typeof.case_47 x_a0 = none ∧ EoCases.__smtx_typeof.case_48 x_a0 = none ∧ EoCases.__smtx_typeof.case_49 x_a0 = none ∧ EoCases.__smtx_typeof.case_50 x_a0 = none ∧ EoCases.__smtx_typeof.case_51 x_a0 = none ∧ EoCases.__smtx_typeof.case_52 x_a0 = none ∧ EoCases.__smtx_typeof.case_53 x_a0 = none ∧ EoCases.__smtx_typeof.case_54 x_a0 = none ∧ EoCases.__smtx_typeof.case_55 x_a0 = none ∧ EoCases.__smtx_typeof.case_56 x_a0 = none ∧ EoCases.__smtx_typeof.case_57 x_a0 = none ∧ EoCases.__smtx_typeof.case_58 x_a0 = none ∧ EoCases.__smtx_typeof.case_59 x_a0 = none ∧ EoCases.__smtx_typeof.case_60 x_a0 = none ∧ EoCases.__smtx_typeof.case_61 x_a0 = none ∧ EoCases.__smtx_typeof.case_62 x_a0 = none ∧ EoCases.__smtx_typeof.case_63 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_2_0_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  group_round_step with cases_1_0_eo__24smtx_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_0 x_a0, EoCases.__smtx_typeof.case_1 x_a0, EoCases.__smtx_typeof.case_2 x_a0, EoCases.__smtx_typeof.case_3 x_a0, EoCases.__smtx_typeof.case_4 x_a0, EoCases.__smtx_typeof.case_5 x_a0, EoCases.__smtx_typeof.case_6 x_a0, EoCases.__smtx_typeof.case_7 x_a0, EoCases.__smtx_typeof.case_8 x_a0, EoCases.__smtx_typeof.case_9 x_a0, EoCases.__smtx_typeof.case_10 x_a0, EoCases.__smtx_typeof.case_11 x_a0, EoCases.__smtx_typeof.case_12 x_a0, EoCases.__smtx_typeof.case_13 x_a0, EoCases.__smtx_typeof.case_14 x_a0, EoCases.__smtx_typeof.case_15 x_a0, EoCases.__smtx_typeof.case_16 x_a0, EoCases.__smtx_typeof.case_17 x_a0, EoCases.__smtx_typeof.case_18 x_a0, EoCases.__smtx_typeof.case_19 x_a0, EoCases.__smtx_typeof.case_20 x_a0, EoCases.__smtx_typeof.case_21 x_a0, EoCases.__smtx_typeof.case_22 x_a0, EoCases.__smtx_typeof.case_23 x_a0, EoCases.__smtx_typeof.case_24 x_a0, EoCases.__smtx_typeof.case_25 x_a0, EoCases.__smtx_typeof.case_26 x_a0, EoCases.__smtx_typeof.case_27 x_a0, EoCases.__smtx_typeof.case_28 x_a0, EoCases.__smtx_typeof.case_29 x_a0, EoCases.__smtx_typeof.case_30 x_a0, EoCases.__smtx_typeof.case_31 x_a0, EoCases.__smtx_typeof.case_32 x_a0, EoCases.__smtx_typeof.case_33 x_a0, EoCases.__smtx_typeof.case_34 x_a0, EoCases.__smtx_typeof.case_35 x_a0, EoCases.__smtx_typeof.case_36 x_a0, EoCases.__smtx_typeof.case_37 x_a0, EoCases.__smtx_typeof.case_38 x_a0, EoCases.__smtx_typeof.case_39 x_a0, EoCases.__smtx_typeof.case_40 x_a0, EoCases.__smtx_typeof.case_41 x_a0, EoCases.__smtx_typeof.case_42 x_a0, EoCases.__smtx_typeof.case_43 x_a0, EoCases.__smtx_typeof.case_44 x_a0, EoCases.__smtx_typeof.case_45 x_a0, EoCases.__smtx_typeof.case_46 x_a0, EoCases.__smtx_typeof.case_47 x_a0, EoCases.__smtx_typeof.case_48 x_a0, EoCases.__smtx_typeof.case_49 x_a0, EoCases.__smtx_typeof.case_50 x_a0, EoCases.__smtx_typeof.case_51 x_a0, EoCases.__smtx_typeof.case_52 x_a0, EoCases.__smtx_typeof.case_53 x_a0, EoCases.__smtx_typeof.case_54 x_a0, EoCases.__smtx_typeof.case_55 x_a0, EoCases.__smtx_typeof.case_56 x_a0, EoCases.__smtx_typeof.case_57 x_a0, EoCases.__smtx_typeof.case_58 x_a0, EoCases.__smtx_typeof.case_59 x_a0, EoCases.__smtx_typeof.case_60 x_a0, EoCases.__smtx_typeof.case_61 x_a0, EoCases.__smtx_typeof.case_62 x_a0, EoCases.__smtx_typeof.case_63 x_a0] = [] ++ [EoCases.__smtx_typeof.case_0 x_a0, EoCases.__smtx_typeof.case_1 x_a0, EoCases.__smtx_typeof.case_2 x_a0, EoCases.__smtx_typeof.case_3 x_a0, EoCases.__smtx_typeof.case_4 x_a0, EoCases.__smtx_typeof.case_5 x_a0, EoCases.__smtx_typeof.case_6 x_a0, EoCases.__smtx_typeof.case_7 x_a0, EoCases.__smtx_typeof.case_8 x_a0, EoCases.__smtx_typeof.case_9 x_a0, EoCases.__smtx_typeof.case_10 x_a0, EoCases.__smtx_typeof.case_11 x_a0, EoCases.__smtx_typeof.case_12 x_a0, EoCases.__smtx_typeof.case_13 x_a0, EoCases.__smtx_typeof.case_14 x_a0, EoCases.__smtx_typeof.case_15 x_a0] ++ [EoCases.__smtx_typeof.case_16 x_a0, EoCases.__smtx_typeof.case_17 x_a0, EoCases.__smtx_typeof.case_18 x_a0, EoCases.__smtx_typeof.case_19 x_a0, EoCases.__smtx_typeof.case_20 x_a0, EoCases.__smtx_typeof.case_21 x_a0, EoCases.__smtx_typeof.case_22 x_a0, EoCases.__smtx_typeof.case_23 x_a0, EoCases.__smtx_typeof.case_24 x_a0, EoCases.__smtx_typeof.case_25 x_a0, EoCases.__smtx_typeof.case_26 x_a0, EoCases.__smtx_typeof.case_27 x_a0, EoCases.__smtx_typeof.case_28 x_a0, EoCases.__smtx_typeof.case_29 x_a0, EoCases.__smtx_typeof.case_30 x_a0, EoCases.__smtx_typeof.case_31 x_a0, EoCases.__smtx_typeof.case_32 x_a0, EoCases.__smtx_typeof.case_33 x_a0, EoCases.__smtx_typeof.case_34 x_a0, EoCases.__smtx_typeof.case_35 x_a0, EoCases.__smtx_typeof.case_36 x_a0, EoCases.__smtx_typeof.case_37 x_a0, EoCases.__smtx_typeof.case_38 x_a0, EoCases.__smtx_typeof.case_39 x_a0, EoCases.__smtx_typeof.case_40 x_a0, EoCases.__smtx_typeof.case_41 x_a0, EoCases.__smtx_typeof.case_42 x_a0, EoCases.__smtx_typeof.case_43 x_a0, EoCases.__smtx_typeof.case_44 x_a0, EoCases.__smtx_typeof.case_45 x_a0, EoCases.__smtx_typeof.case_46 x_a0, EoCases.__smtx_typeof.case_47 x_a0, EoCases.__smtx_typeof.case_48 x_a0, EoCases.__smtx_typeof.case_49 x_a0, EoCases.__smtx_typeof.case_50 x_a0, EoCases.__smtx_typeof.case_51 x_a0, EoCases.__smtx_typeof.case_52 x_a0, EoCases.__smtx_typeof.case_53 x_a0, EoCases.__smtx_typeof.case_54 x_a0, EoCases.__smtx_typeof.case_55 x_a0, EoCases.__smtx_typeof.case_56 x_a0, EoCases.__smtx_typeof.case_57 x_a0, EoCases.__smtx_typeof.case_58 x_a0, EoCases.__smtx_typeof.case_59 x_a0, EoCases.__smtx_typeof.case_60 x_a0, EoCases.__smtx_typeof.case_61 x_a0, EoCases.__smtx_typeof.case_62 x_a0, EoCases.__smtx_typeof.case_63 x_a0] from rfl)
    otherwise ⟨hl_0, hl_1, hl_2, hl_3, hl_4, hl_5, hl_6, hl_7, hl_8, hl_9, hl_10, hl_11, hl_12, hl_13, hl_14, hl_15⟩ using
  group_round_step with cases_1_1_eo__24smtx_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_0 x_a0, EoCases.__smtx_typeof.case_1 x_a0, EoCases.__smtx_typeof.case_2 x_a0, EoCases.__smtx_typeof.case_3 x_a0, EoCases.__smtx_typeof.case_4 x_a0, EoCases.__smtx_typeof.case_5 x_a0, EoCases.__smtx_typeof.case_6 x_a0, EoCases.__smtx_typeof.case_7 x_a0, EoCases.__smtx_typeof.case_8 x_a0, EoCases.__smtx_typeof.case_9 x_a0, EoCases.__smtx_typeof.case_10 x_a0, EoCases.__smtx_typeof.case_11 x_a0, EoCases.__smtx_typeof.case_12 x_a0, EoCases.__smtx_typeof.case_13 x_a0, EoCases.__smtx_typeof.case_14 x_a0, EoCases.__smtx_typeof.case_15 x_a0, EoCases.__smtx_typeof.case_16 x_a0, EoCases.__smtx_typeof.case_17 x_a0, EoCases.__smtx_typeof.case_18 x_a0, EoCases.__smtx_typeof.case_19 x_a0, EoCases.__smtx_typeof.case_20 x_a0, EoCases.__smtx_typeof.case_21 x_a0, EoCases.__smtx_typeof.case_22 x_a0, EoCases.__smtx_typeof.case_23 x_a0, EoCases.__smtx_typeof.case_24 x_a0, EoCases.__smtx_typeof.case_25 x_a0, EoCases.__smtx_typeof.case_26 x_a0, EoCases.__smtx_typeof.case_27 x_a0, EoCases.__smtx_typeof.case_28 x_a0, EoCases.__smtx_typeof.case_29 x_a0, EoCases.__smtx_typeof.case_30 x_a0, EoCases.__smtx_typeof.case_31 x_a0, EoCases.__smtx_typeof.case_32 x_a0, EoCases.__smtx_typeof.case_33 x_a0, EoCases.__smtx_typeof.case_34 x_a0, EoCases.__smtx_typeof.case_35 x_a0, EoCases.__smtx_typeof.case_36 x_a0, EoCases.__smtx_typeof.case_37 x_a0, EoCases.__smtx_typeof.case_38 x_a0, EoCases.__smtx_typeof.case_39 x_a0, EoCases.__smtx_typeof.case_40 x_a0, EoCases.__smtx_typeof.case_41 x_a0, EoCases.__smtx_typeof.case_42 x_a0, EoCases.__smtx_typeof.case_43 x_a0, EoCases.__smtx_typeof.case_44 x_a0, EoCases.__smtx_typeof.case_45 x_a0, EoCases.__smtx_typeof.case_46 x_a0, EoCases.__smtx_typeof.case_47 x_a0, EoCases.__smtx_typeof.case_48 x_a0, EoCases.__smtx_typeof.case_49 x_a0, EoCases.__smtx_typeof.case_50 x_a0, EoCases.__smtx_typeof.case_51 x_a0, EoCases.__smtx_typeof.case_52 x_a0, EoCases.__smtx_typeof.case_53 x_a0, EoCases.__smtx_typeof.case_54 x_a0, EoCases.__smtx_typeof.case_55 x_a0, EoCases.__smtx_typeof.case_56 x_a0, EoCases.__smtx_typeof.case_57 x_a0, EoCases.__smtx_typeof.case_58 x_a0, EoCases.__smtx_typeof.case_59 x_a0, EoCases.__smtx_typeof.case_60 x_a0, EoCases.__smtx_typeof.case_61 x_a0, EoCases.__smtx_typeof.case_62 x_a0, EoCases.__smtx_typeof.case_63 x_a0] = [EoCases.__smtx_typeof.case_0 x_a0, EoCases.__smtx_typeof.case_1 x_a0, EoCases.__smtx_typeof.case_2 x_a0, EoCases.__smtx_typeof.case_3 x_a0, EoCases.__smtx_typeof.case_4 x_a0, EoCases.__smtx_typeof.case_5 x_a0, EoCases.__smtx_typeof.case_6 x_a0, EoCases.__smtx_typeof.case_7 x_a0, EoCases.__smtx_typeof.case_8 x_a0, EoCases.__smtx_typeof.case_9 x_a0, EoCases.__smtx_typeof.case_10 x_a0, EoCases.__smtx_typeof.case_11 x_a0, EoCases.__smtx_typeof.case_12 x_a0, EoCases.__smtx_typeof.case_13 x_a0, EoCases.__smtx_typeof.case_14 x_a0, EoCases.__smtx_typeof.case_15 x_a0] ++ [EoCases.__smtx_typeof.case_16 x_a0, EoCases.__smtx_typeof.case_17 x_a0, EoCases.__smtx_typeof.case_18 x_a0, EoCases.__smtx_typeof.case_19 x_a0, EoCases.__smtx_typeof.case_20 x_a0, EoCases.__smtx_typeof.case_21 x_a0, EoCases.__smtx_typeof.case_22 x_a0, EoCases.__smtx_typeof.case_23 x_a0, EoCases.__smtx_typeof.case_24 x_a0, EoCases.__smtx_typeof.case_25 x_a0, EoCases.__smtx_typeof.case_26 x_a0, EoCases.__smtx_typeof.case_27 x_a0, EoCases.__smtx_typeof.case_28 x_a0, EoCases.__smtx_typeof.case_29 x_a0, EoCases.__smtx_typeof.case_30 x_a0, EoCases.__smtx_typeof.case_31 x_a0] ++ [EoCases.__smtx_typeof.case_32 x_a0, EoCases.__smtx_typeof.case_33 x_a0, EoCases.__smtx_typeof.case_34 x_a0, EoCases.__smtx_typeof.case_35 x_a0, EoCases.__smtx_typeof.case_36 x_a0, EoCases.__smtx_typeof.case_37 x_a0, EoCases.__smtx_typeof.case_38 x_a0, EoCases.__smtx_typeof.case_39 x_a0, EoCases.__smtx_typeof.case_40 x_a0, EoCases.__smtx_typeof.case_41 x_a0, EoCases.__smtx_typeof.case_42 x_a0, EoCases.__smtx_typeof.case_43 x_a0, EoCases.__smtx_typeof.case_44 x_a0, EoCases.__smtx_typeof.case_45 x_a0, EoCases.__smtx_typeof.case_46 x_a0, EoCases.__smtx_typeof.case_47 x_a0, EoCases.__smtx_typeof.case_48 x_a0, EoCases.__smtx_typeof.case_49 x_a0, EoCases.__smtx_typeof.case_50 x_a0, EoCases.__smtx_typeof.case_51 x_a0, EoCases.__smtx_typeof.case_52 x_a0, EoCases.__smtx_typeof.case_53 x_a0, EoCases.__smtx_typeof.case_54 x_a0, EoCases.__smtx_typeof.case_55 x_a0, EoCases.__smtx_typeof.case_56 x_a0, EoCases.__smtx_typeof.case_57 x_a0, EoCases.__smtx_typeof.case_58 x_a0, EoCases.__smtx_typeof.case_59 x_a0, EoCases.__smtx_typeof.case_60 x_a0, EoCases.__smtx_typeof.case_61 x_a0, EoCases.__smtx_typeof.case_62 x_a0, EoCases.__smtx_typeof.case_63 x_a0] from rfl)
    otherwise ⟨hl_16, hl_17, hl_18, hl_19, hl_20, hl_21, hl_22, hl_23, hl_24, hl_25, hl_26, hl_27, hl_28, hl_29, hl_30, hl_31⟩ using hl_0 hl_1 hl_2 hl_3 hl_4 hl_5 hl_6 hl_7 hl_8 hl_9 hl_10 hl_11 hl_12 hl_13 hl_14 hl_15
  group_round_step with cases_1_2_eo__24smtx_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_0 x_a0, EoCases.__smtx_typeof.case_1 x_a0, EoCases.__smtx_typeof.case_2 x_a0, EoCases.__smtx_typeof.case_3 x_a0, EoCases.__smtx_typeof.case_4 x_a0, EoCases.__smtx_typeof.case_5 x_a0, EoCases.__smtx_typeof.case_6 x_a0, EoCases.__smtx_typeof.case_7 x_a0, EoCases.__smtx_typeof.case_8 x_a0, EoCases.__smtx_typeof.case_9 x_a0, EoCases.__smtx_typeof.case_10 x_a0, EoCases.__smtx_typeof.case_11 x_a0, EoCases.__smtx_typeof.case_12 x_a0, EoCases.__smtx_typeof.case_13 x_a0, EoCases.__smtx_typeof.case_14 x_a0, EoCases.__smtx_typeof.case_15 x_a0, EoCases.__smtx_typeof.case_16 x_a0, EoCases.__smtx_typeof.case_17 x_a0, EoCases.__smtx_typeof.case_18 x_a0, EoCases.__smtx_typeof.case_19 x_a0, EoCases.__smtx_typeof.case_20 x_a0, EoCases.__smtx_typeof.case_21 x_a0, EoCases.__smtx_typeof.case_22 x_a0, EoCases.__smtx_typeof.case_23 x_a0, EoCases.__smtx_typeof.case_24 x_a0, EoCases.__smtx_typeof.case_25 x_a0, EoCases.__smtx_typeof.case_26 x_a0, EoCases.__smtx_typeof.case_27 x_a0, EoCases.__smtx_typeof.case_28 x_a0, EoCases.__smtx_typeof.case_29 x_a0, EoCases.__smtx_typeof.case_30 x_a0, EoCases.__smtx_typeof.case_31 x_a0, EoCases.__smtx_typeof.case_32 x_a0, EoCases.__smtx_typeof.case_33 x_a0, EoCases.__smtx_typeof.case_34 x_a0, EoCases.__smtx_typeof.case_35 x_a0, EoCases.__smtx_typeof.case_36 x_a0, EoCases.__smtx_typeof.case_37 x_a0, EoCases.__smtx_typeof.case_38 x_a0, EoCases.__smtx_typeof.case_39 x_a0, EoCases.__smtx_typeof.case_40 x_a0, EoCases.__smtx_typeof.case_41 x_a0, EoCases.__smtx_typeof.case_42 x_a0, EoCases.__smtx_typeof.case_43 x_a0, EoCases.__smtx_typeof.case_44 x_a0, EoCases.__smtx_typeof.case_45 x_a0, EoCases.__smtx_typeof.case_46 x_a0, EoCases.__smtx_typeof.case_47 x_a0, EoCases.__smtx_typeof.case_48 x_a0, EoCases.__smtx_typeof.case_49 x_a0, EoCases.__smtx_typeof.case_50 x_a0, EoCases.__smtx_typeof.case_51 x_a0, EoCases.__smtx_typeof.case_52 x_a0, EoCases.__smtx_typeof.case_53 x_a0, EoCases.__smtx_typeof.case_54 x_a0, EoCases.__smtx_typeof.case_55 x_a0, EoCases.__smtx_typeof.case_56 x_a0, EoCases.__smtx_typeof.case_57 x_a0, EoCases.__smtx_typeof.case_58 x_a0, EoCases.__smtx_typeof.case_59 x_a0, EoCases.__smtx_typeof.case_60 x_a0, EoCases.__smtx_typeof.case_61 x_a0, EoCases.__smtx_typeof.case_62 x_a0, EoCases.__smtx_typeof.case_63 x_a0] = [EoCases.__smtx_typeof.case_0 x_a0, EoCases.__smtx_typeof.case_1 x_a0, EoCases.__smtx_typeof.case_2 x_a0, EoCases.__smtx_typeof.case_3 x_a0, EoCases.__smtx_typeof.case_4 x_a0, EoCases.__smtx_typeof.case_5 x_a0, EoCases.__smtx_typeof.case_6 x_a0, EoCases.__smtx_typeof.case_7 x_a0, EoCases.__smtx_typeof.case_8 x_a0, EoCases.__smtx_typeof.case_9 x_a0, EoCases.__smtx_typeof.case_10 x_a0, EoCases.__smtx_typeof.case_11 x_a0, EoCases.__smtx_typeof.case_12 x_a0, EoCases.__smtx_typeof.case_13 x_a0, EoCases.__smtx_typeof.case_14 x_a0, EoCases.__smtx_typeof.case_15 x_a0, EoCases.__smtx_typeof.case_16 x_a0, EoCases.__smtx_typeof.case_17 x_a0, EoCases.__smtx_typeof.case_18 x_a0, EoCases.__smtx_typeof.case_19 x_a0, EoCases.__smtx_typeof.case_20 x_a0, EoCases.__smtx_typeof.case_21 x_a0, EoCases.__smtx_typeof.case_22 x_a0, EoCases.__smtx_typeof.case_23 x_a0, EoCases.__smtx_typeof.case_24 x_a0, EoCases.__smtx_typeof.case_25 x_a0, EoCases.__smtx_typeof.case_26 x_a0, EoCases.__smtx_typeof.case_27 x_a0, EoCases.__smtx_typeof.case_28 x_a0, EoCases.__smtx_typeof.case_29 x_a0, EoCases.__smtx_typeof.case_30 x_a0, EoCases.__smtx_typeof.case_31 x_a0] ++ [EoCases.__smtx_typeof.case_32 x_a0, EoCases.__smtx_typeof.case_33 x_a0, EoCases.__smtx_typeof.case_34 x_a0, EoCases.__smtx_typeof.case_35 x_a0, EoCases.__smtx_typeof.case_36 x_a0, EoCases.__smtx_typeof.case_37 x_a0, EoCases.__smtx_typeof.case_38 x_a0, EoCases.__smtx_typeof.case_39 x_a0, EoCases.__smtx_typeof.case_40 x_a0, EoCases.__smtx_typeof.case_41 x_a0, EoCases.__smtx_typeof.case_42 x_a0, EoCases.__smtx_typeof.case_43 x_a0, EoCases.__smtx_typeof.case_44 x_a0, EoCases.__smtx_typeof.case_45 x_a0, EoCases.__smtx_typeof.case_46 x_a0, EoCases.__smtx_typeof.case_47 x_a0] ++ [EoCases.__smtx_typeof.case_48 x_a0, EoCases.__smtx_typeof.case_49 x_a0, EoCases.__smtx_typeof.case_50 x_a0, EoCases.__smtx_typeof.case_51 x_a0, EoCases.__smtx_typeof.case_52 x_a0, EoCases.__smtx_typeof.case_53 x_a0, EoCases.__smtx_typeof.case_54 x_a0, EoCases.__smtx_typeof.case_55 x_a0, EoCases.__smtx_typeof.case_56 x_a0, EoCases.__smtx_typeof.case_57 x_a0, EoCases.__smtx_typeof.case_58 x_a0, EoCases.__smtx_typeof.case_59 x_a0, EoCases.__smtx_typeof.case_60 x_a0, EoCases.__smtx_typeof.case_61 x_a0, EoCases.__smtx_typeof.case_62 x_a0, EoCases.__smtx_typeof.case_63 x_a0] from rfl)
    otherwise ⟨hl_32, hl_33, hl_34, hl_35, hl_36, hl_37, hl_38, hl_39, hl_40, hl_41, hl_42, hl_43, hl_44, hl_45, hl_46, hl_47⟩ using hl_0 hl_1 hl_2 hl_3 hl_4 hl_5 hl_6 hl_7 hl_8 hl_9 hl_10 hl_11 hl_12 hl_13 hl_14 hl_15 hl_16 hl_17 hl_18 hl_19 hl_20 hl_21 hl_22 hl_23 hl_24 hl_25 hl_26 hl_27 hl_28 hl_29 hl_30 hl_31
  group_round_step with cases_1_3_eo__24smtx_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_0 x_a0, EoCases.__smtx_typeof.case_1 x_a0, EoCases.__smtx_typeof.case_2 x_a0, EoCases.__smtx_typeof.case_3 x_a0, EoCases.__smtx_typeof.case_4 x_a0, EoCases.__smtx_typeof.case_5 x_a0, EoCases.__smtx_typeof.case_6 x_a0, EoCases.__smtx_typeof.case_7 x_a0, EoCases.__smtx_typeof.case_8 x_a0, EoCases.__smtx_typeof.case_9 x_a0, EoCases.__smtx_typeof.case_10 x_a0, EoCases.__smtx_typeof.case_11 x_a0, EoCases.__smtx_typeof.case_12 x_a0, EoCases.__smtx_typeof.case_13 x_a0, EoCases.__smtx_typeof.case_14 x_a0, EoCases.__smtx_typeof.case_15 x_a0, EoCases.__smtx_typeof.case_16 x_a0, EoCases.__smtx_typeof.case_17 x_a0, EoCases.__smtx_typeof.case_18 x_a0, EoCases.__smtx_typeof.case_19 x_a0, EoCases.__smtx_typeof.case_20 x_a0, EoCases.__smtx_typeof.case_21 x_a0, EoCases.__smtx_typeof.case_22 x_a0, EoCases.__smtx_typeof.case_23 x_a0, EoCases.__smtx_typeof.case_24 x_a0, EoCases.__smtx_typeof.case_25 x_a0, EoCases.__smtx_typeof.case_26 x_a0, EoCases.__smtx_typeof.case_27 x_a0, EoCases.__smtx_typeof.case_28 x_a0, EoCases.__smtx_typeof.case_29 x_a0, EoCases.__smtx_typeof.case_30 x_a0, EoCases.__smtx_typeof.case_31 x_a0, EoCases.__smtx_typeof.case_32 x_a0, EoCases.__smtx_typeof.case_33 x_a0, EoCases.__smtx_typeof.case_34 x_a0, EoCases.__smtx_typeof.case_35 x_a0, EoCases.__smtx_typeof.case_36 x_a0, EoCases.__smtx_typeof.case_37 x_a0, EoCases.__smtx_typeof.case_38 x_a0, EoCases.__smtx_typeof.case_39 x_a0, EoCases.__smtx_typeof.case_40 x_a0, EoCases.__smtx_typeof.case_41 x_a0, EoCases.__smtx_typeof.case_42 x_a0, EoCases.__smtx_typeof.case_43 x_a0, EoCases.__smtx_typeof.case_44 x_a0, EoCases.__smtx_typeof.case_45 x_a0, EoCases.__smtx_typeof.case_46 x_a0, EoCases.__smtx_typeof.case_47 x_a0, EoCases.__smtx_typeof.case_48 x_a0, EoCases.__smtx_typeof.case_49 x_a0, EoCases.__smtx_typeof.case_50 x_a0, EoCases.__smtx_typeof.case_51 x_a0, EoCases.__smtx_typeof.case_52 x_a0, EoCases.__smtx_typeof.case_53 x_a0, EoCases.__smtx_typeof.case_54 x_a0, EoCases.__smtx_typeof.case_55 x_a0, EoCases.__smtx_typeof.case_56 x_a0, EoCases.__smtx_typeof.case_57 x_a0, EoCases.__smtx_typeof.case_58 x_a0, EoCases.__smtx_typeof.case_59 x_a0, EoCases.__smtx_typeof.case_60 x_a0, EoCases.__smtx_typeof.case_61 x_a0, EoCases.__smtx_typeof.case_62 x_a0, EoCases.__smtx_typeof.case_63 x_a0] = [EoCases.__smtx_typeof.case_0 x_a0, EoCases.__smtx_typeof.case_1 x_a0, EoCases.__smtx_typeof.case_2 x_a0, EoCases.__smtx_typeof.case_3 x_a0, EoCases.__smtx_typeof.case_4 x_a0, EoCases.__smtx_typeof.case_5 x_a0, EoCases.__smtx_typeof.case_6 x_a0, EoCases.__smtx_typeof.case_7 x_a0, EoCases.__smtx_typeof.case_8 x_a0, EoCases.__smtx_typeof.case_9 x_a0, EoCases.__smtx_typeof.case_10 x_a0, EoCases.__smtx_typeof.case_11 x_a0, EoCases.__smtx_typeof.case_12 x_a0, EoCases.__smtx_typeof.case_13 x_a0, EoCases.__smtx_typeof.case_14 x_a0, EoCases.__smtx_typeof.case_15 x_a0, EoCases.__smtx_typeof.case_16 x_a0, EoCases.__smtx_typeof.case_17 x_a0, EoCases.__smtx_typeof.case_18 x_a0, EoCases.__smtx_typeof.case_19 x_a0, EoCases.__smtx_typeof.case_20 x_a0, EoCases.__smtx_typeof.case_21 x_a0, EoCases.__smtx_typeof.case_22 x_a0, EoCases.__smtx_typeof.case_23 x_a0, EoCases.__smtx_typeof.case_24 x_a0, EoCases.__smtx_typeof.case_25 x_a0, EoCases.__smtx_typeof.case_26 x_a0, EoCases.__smtx_typeof.case_27 x_a0, EoCases.__smtx_typeof.case_28 x_a0, EoCases.__smtx_typeof.case_29 x_a0, EoCases.__smtx_typeof.case_30 x_a0, EoCases.__smtx_typeof.case_31 x_a0, EoCases.__smtx_typeof.case_32 x_a0, EoCases.__smtx_typeof.case_33 x_a0, EoCases.__smtx_typeof.case_34 x_a0, EoCases.__smtx_typeof.case_35 x_a0, EoCases.__smtx_typeof.case_36 x_a0, EoCases.__smtx_typeof.case_37 x_a0, EoCases.__smtx_typeof.case_38 x_a0, EoCases.__smtx_typeof.case_39 x_a0, EoCases.__smtx_typeof.case_40 x_a0, EoCases.__smtx_typeof.case_41 x_a0, EoCases.__smtx_typeof.case_42 x_a0, EoCases.__smtx_typeof.case_43 x_a0, EoCases.__smtx_typeof.case_44 x_a0, EoCases.__smtx_typeof.case_45 x_a0, EoCases.__smtx_typeof.case_46 x_a0, EoCases.__smtx_typeof.case_47 x_a0] ++ [EoCases.__smtx_typeof.case_48 x_a0, EoCases.__smtx_typeof.case_49 x_a0, EoCases.__smtx_typeof.case_50 x_a0, EoCases.__smtx_typeof.case_51 x_a0, EoCases.__smtx_typeof.case_52 x_a0, EoCases.__smtx_typeof.case_53 x_a0, EoCases.__smtx_typeof.case_54 x_a0, EoCases.__smtx_typeof.case_55 x_a0, EoCases.__smtx_typeof.case_56 x_a0, EoCases.__smtx_typeof.case_57 x_a0, EoCases.__smtx_typeof.case_58 x_a0, EoCases.__smtx_typeof.case_59 x_a0, EoCases.__smtx_typeof.case_60 x_a0, EoCases.__smtx_typeof.case_61 x_a0, EoCases.__smtx_typeof.case_62 x_a0, EoCases.__smtx_typeof.case_63 x_a0] ++ [] from rfl)
    otherwise ⟨hl_48, hl_49, hl_50, hl_51, hl_52, hl_53, hl_54, hl_55, hl_56, hl_57, hl_58, hl_59, hl_60, hl_61, hl_62, hl_63⟩ using hl_0 hl_1 hl_2 hl_3 hl_4 hl_5 hl_6 hl_7 hl_8 hl_9 hl_10 hl_11 hl_12 hl_13 hl_14 hl_15 hl_16 hl_17 hl_18 hl_19 hl_20 hl_21 hl_22 hl_23 hl_24 hl_25 hl_26 hl_27 hl_28 hl_29 hl_30 hl_31 hl_32 hl_33 hl_34 hl_35 hl_36 hl_37 hl_38 hl_39 hl_40 hl_41 hl_42 hl_43 hl_44 hl_45 hl_46 hl_47
  group_none hinv4 hG with ⟨hl_0, hl_1, hl_2, hl_3, hl_4, hl_5, hl_6, hl_7, hl_8, hl_9, hl_10, hl_11, hl_12, hl_13, hl_14, hl_15, hl_16, hl_17, hl_18, hl_19, hl_20, hl_21, hl_22, hl_23, hl_24, hl_25, hl_26, hl_27, hl_28, hl_29, hl_30, hl_31, hl_32, hl_33, hl_34, hl_35, hl_36, hl_37, hl_38, hl_39, hl_40, hl_41, hl_42, hl_43, hl_44, hl_45, hl_46, hl_47, hl_48, hl_49, hl_50, hl_51, hl_52, hl_53, hl_54, hl_55, hl_56, hl_57, hl_58, hl_59, hl_60, hl_61, hl_62, hl_63⟩

theorem cases_2_1_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_2_1_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, (∀ d, firstSome [EoCases.__smtx_typeof.case_64 x_a0, EoCases.__smtx_typeof.case_65 x_a0, EoCases.__smtx_typeof.case_66 x_a0, EoCases.__smtx_typeof.case_67 x_a0, EoCases.__smtx_typeof.case_68 x_a0, EoCases.__smtx_typeof.case_69 x_a0, EoCases.__smtx_typeof.case_70 x_a0, EoCases.__smtx_typeof.case_71 x_a0, EoCases.__smtx_typeof.case_72 x_a0, EoCases.__smtx_typeof.case_73 x_a0, EoCases.__smtx_typeof.case_74 x_a0, EoCases.__smtx_typeof.case_75 x_a0, EoCases.__smtx_typeof.case_76 x_a0, EoCases.__smtx_typeof.case_77 x_a0, EoCases.__smtx_typeof.case_78 x_a0, EoCases.__smtx_typeof.case_79 x_a0, EoCases.__smtx_typeof.case_80 x_a0, EoCases.__smtx_typeof.case_81 x_a0, EoCases.__smtx_typeof.case_82 x_a0, EoCases.__smtx_typeof.case_83 x_a0, EoCases.__smtx_typeof.case_84 x_a0, EoCases.__smtx_typeof.case_85 x_a0, EoCases.__smtx_typeof.case_86 x_a0, EoCases.__smtx_typeof.case_87 x_a0, EoCases.__smtx_typeof.case_88 x_a0, EoCases.__smtx_typeof.case_89 x_a0, EoCases.__smtx_typeof.case_90 x_a0, EoCases.__smtx_typeof.case_91 x_a0, EoCases.__smtx_typeof.case_92 x_a0, EoCases.__smtx_typeof.case_93 x_a0, EoCases.__smtx_typeof.case_94 x_a0, EoCases.__smtx_typeof.case_95 x_a0, EoCases.__smtx_typeof.case_96 x_a0, EoCases.__smtx_typeof.case_97 x_a0, EoCases.__smtx_typeof.case_98 x_a0, EoCases.__smtx_typeof.case_99 x_a0, EoCases.__smtx_typeof.case_100 x_a0, EoCases.__smtx_typeof.case_101 x_a0, EoCases.__smtx_typeof.case_102 x_a0, EoCases.__smtx_typeof.case_103 x_a0, EoCases.__smtx_typeof.case_104 x_a0, EoCases.__smtx_typeof.case_105 x_a0, EoCases.__smtx_typeof.case_106 x_a0, EoCases.__smtx_typeof.case_107 x_a0, EoCases.__smtx_typeof.case_108 x_a0, EoCases.__smtx_typeof.case_109 x_a0, EoCases.__smtx_typeof.case_110 x_a0, EoCases.__smtx_typeof.case_111 x_a0, EoCases.__smtx_typeof.case_112 x_a0, EoCases.__smtx_typeof.case_113 x_a0, EoCases.__smtx_typeof.case_114 x_a0, EoCases.__smtx_typeof.case_115 x_a0, EoCases.__smtx_typeof.case_116 x_a0, EoCases.__smtx_typeof.case_117 x_a0, EoCases.__smtx_typeof.case_118 x_a0, EoCases.__smtx_typeof.case_119 x_a0, EoCases.__smtx_typeof.case_120 x_a0, EoCases.__smtx_typeof.case_121 x_a0, EoCases.__smtx_typeof.case_122 x_a0, EoCases.__smtx_typeof.case_123 x_a0, EoCases.__smtx_typeof.case_124 x_a0, EoCases.__smtx_typeof.case_125 x_a0, EoCases.__smtx_typeof.case_126 x_a0, EoCases.__smtx_typeof.case_127 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          ∀ d, firstSome [EoCases.__smtx_typeof.case_64 x_a0, EoCases.__smtx_typeof.case_65 x_a0, EoCases.__smtx_typeof.case_66 x_a0, EoCases.__smtx_typeof.case_67 x_a0, EoCases.__smtx_typeof.case_68 x_a0, EoCases.__smtx_typeof.case_69 x_a0, EoCases.__smtx_typeof.case_70 x_a0, EoCases.__smtx_typeof.case_71 x_a0, EoCases.__smtx_typeof.case_72 x_a0, EoCases.__smtx_typeof.case_73 x_a0, EoCases.__smtx_typeof.case_74 x_a0, EoCases.__smtx_typeof.case_75 x_a0, EoCases.__smtx_typeof.case_76 x_a0, EoCases.__smtx_typeof.case_77 x_a0, EoCases.__smtx_typeof.case_78 x_a0, EoCases.__smtx_typeof.case_79 x_a0, EoCases.__smtx_typeof.case_80 x_a0, EoCases.__smtx_typeof.case_81 x_a0, EoCases.__smtx_typeof.case_82 x_a0, EoCases.__smtx_typeof.case_83 x_a0, EoCases.__smtx_typeof.case_84 x_a0, EoCases.__smtx_typeof.case_85 x_a0, EoCases.__smtx_typeof.case_86 x_a0, EoCases.__smtx_typeof.case_87 x_a0, EoCases.__smtx_typeof.case_88 x_a0, EoCases.__smtx_typeof.case_89 x_a0, EoCases.__smtx_typeof.case_90 x_a0, EoCases.__smtx_typeof.case_91 x_a0, EoCases.__smtx_typeof.case_92 x_a0, EoCases.__smtx_typeof.case_93 x_a0, EoCases.__smtx_typeof.case_94 x_a0, EoCases.__smtx_typeof.case_95 x_a0, EoCases.__smtx_typeof.case_96 x_a0, EoCases.__smtx_typeof.case_97 x_a0, EoCases.__smtx_typeof.case_98 x_a0, EoCases.__smtx_typeof.case_99 x_a0, EoCases.__smtx_typeof.case_100 x_a0, EoCases.__smtx_typeof.case_101 x_a0, EoCases.__smtx_typeof.case_102 x_a0, EoCases.__smtx_typeof.case_103 x_a0, EoCases.__smtx_typeof.case_104 x_a0, EoCases.__smtx_typeof.case_105 x_a0, EoCases.__smtx_typeof.case_106 x_a0, EoCases.__smtx_typeof.case_107 x_a0, EoCases.__smtx_typeof.case_108 x_a0, EoCases.__smtx_typeof.case_109 x_a0, EoCases.__smtx_typeof.case_110 x_a0, EoCases.__smtx_typeof.case_111 x_a0, EoCases.__smtx_typeof.case_112 x_a0, EoCases.__smtx_typeof.case_113 x_a0, EoCases.__smtx_typeof.case_114 x_a0, EoCases.__smtx_typeof.case_115 x_a0, EoCases.__smtx_typeof.case_116 x_a0, EoCases.__smtx_typeof.case_117 x_a0, EoCases.__smtx_typeof.case_118 x_a0, EoCases.__smtx_typeof.case_119 x_a0, EoCases.__smtx_typeof.case_120 x_a0, EoCases.__smtx_typeof.case_121 x_a0, EoCases.__smtx_typeof.case_122 x_a0, EoCases.__smtx_typeof.case_123 x_a0, EoCases.__smtx_typeof.case_124 x_a0, EoCases.__smtx_typeof.case_125 x_a0, EoCases.__smtx_typeof.case_126 x_a0, EoCases.__smtx_typeof.case_127 x_a0] d = __smtx_typeof y0
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_64 x_a0 = none ∧ EoCases.__smtx_typeof.case_65 x_a0 = none ∧ EoCases.__smtx_typeof.case_66 x_a0 = none ∧ EoCases.__smtx_typeof.case_67 x_a0 = none ∧ EoCases.__smtx_typeof.case_68 x_a0 = none ∧ EoCases.__smtx_typeof.case_69 x_a0 = none ∧ EoCases.__smtx_typeof.case_70 x_a0 = none ∧ EoCases.__smtx_typeof.case_71 x_a0 = none ∧ EoCases.__smtx_typeof.case_72 x_a0 = none ∧ EoCases.__smtx_typeof.case_73 x_a0 = none ∧ EoCases.__smtx_typeof.case_74 x_a0 = none ∧ EoCases.__smtx_typeof.case_75 x_a0 = none ∧ EoCases.__smtx_typeof.case_76 x_a0 = none ∧ EoCases.__smtx_typeof.case_77 x_a0 = none ∧ EoCases.__smtx_typeof.case_78 x_a0 = none ∧ EoCases.__smtx_typeof.case_79 x_a0 = none ∧ EoCases.__smtx_typeof.case_80 x_a0 = none ∧ EoCases.__smtx_typeof.case_81 x_a0 = none ∧ EoCases.__smtx_typeof.case_82 x_a0 = none ∧ EoCases.__smtx_typeof.case_83 x_a0 = none ∧ EoCases.__smtx_typeof.case_84 x_a0 = none ∧ EoCases.__smtx_typeof.case_85 x_a0 = none ∧ EoCases.__smtx_typeof.case_86 x_a0 = none ∧ EoCases.__smtx_typeof.case_87 x_a0 = none ∧ EoCases.__smtx_typeof.case_88 x_a0 = none ∧ EoCases.__smtx_typeof.case_89 x_a0 = none ∧ EoCases.__smtx_typeof.case_90 x_a0 = none ∧ EoCases.__smtx_typeof.case_91 x_a0 = none ∧ EoCases.__smtx_typeof.case_92 x_a0 = none ∧ EoCases.__smtx_typeof.case_93 x_a0 = none ∧ EoCases.__smtx_typeof.case_94 x_a0 = none ∧ EoCases.__smtx_typeof.case_95 x_a0 = none ∧ EoCases.__smtx_typeof.case_96 x_a0 = none ∧ EoCases.__smtx_typeof.case_97 x_a0 = none ∧ EoCases.__smtx_typeof.case_98 x_a0 = none ∧ EoCases.__smtx_typeof.case_99 x_a0 = none ∧ EoCases.__smtx_typeof.case_100 x_a0 = none ∧ EoCases.__smtx_typeof.case_101 x_a0 = none ∧ EoCases.__smtx_typeof.case_102 x_a0 = none ∧ EoCases.__smtx_typeof.case_103 x_a0 = none ∧ EoCases.__smtx_typeof.case_104 x_a0 = none ∧ EoCases.__smtx_typeof.case_105 x_a0 = none ∧ EoCases.__smtx_typeof.case_106 x_a0 = none ∧ EoCases.__smtx_typeof.case_107 x_a0 = none ∧ EoCases.__smtx_typeof.case_108 x_a0 = none ∧ EoCases.__smtx_typeof.case_109 x_a0 = none ∧ EoCases.__smtx_typeof.case_110 x_a0 = none ∧ EoCases.__smtx_typeof.case_111 x_a0 = none ∧ EoCases.__smtx_typeof.case_112 x_a0 = none ∧ EoCases.__smtx_typeof.case_113 x_a0 = none ∧ EoCases.__smtx_typeof.case_114 x_a0 = none ∧ EoCases.__smtx_typeof.case_115 x_a0 = none ∧ EoCases.__smtx_typeof.case_116 x_a0 = none ∧ EoCases.__smtx_typeof.case_117 x_a0 = none ∧ EoCases.__smtx_typeof.case_118 x_a0 = none ∧ EoCases.__smtx_typeof.case_119 x_a0 = none ∧ EoCases.__smtx_typeof.case_120 x_a0 = none ∧ EoCases.__smtx_typeof.case_121 x_a0 = none ∧ EoCases.__smtx_typeof.case_122 x_a0 = none ∧ EoCases.__smtx_typeof.case_123 x_a0 = none ∧ EoCases.__smtx_typeof.case_124 x_a0 = none ∧ EoCases.__smtx_typeof.case_125 x_a0 = none ∧ EoCases.__smtx_typeof.case_126 x_a0 = none ∧ EoCases.__smtx_typeof.case_127 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_2_1_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  group_round_step with cases_1_4_eo__24smtx_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_64 x_a0, EoCases.__smtx_typeof.case_65 x_a0, EoCases.__smtx_typeof.case_66 x_a0, EoCases.__smtx_typeof.case_67 x_a0, EoCases.__smtx_typeof.case_68 x_a0, EoCases.__smtx_typeof.case_69 x_a0, EoCases.__smtx_typeof.case_70 x_a0, EoCases.__smtx_typeof.case_71 x_a0, EoCases.__smtx_typeof.case_72 x_a0, EoCases.__smtx_typeof.case_73 x_a0, EoCases.__smtx_typeof.case_74 x_a0, EoCases.__smtx_typeof.case_75 x_a0, EoCases.__smtx_typeof.case_76 x_a0, EoCases.__smtx_typeof.case_77 x_a0, EoCases.__smtx_typeof.case_78 x_a0, EoCases.__smtx_typeof.case_79 x_a0, EoCases.__smtx_typeof.case_80 x_a0, EoCases.__smtx_typeof.case_81 x_a0, EoCases.__smtx_typeof.case_82 x_a0, EoCases.__smtx_typeof.case_83 x_a0, EoCases.__smtx_typeof.case_84 x_a0, EoCases.__smtx_typeof.case_85 x_a0, EoCases.__smtx_typeof.case_86 x_a0, EoCases.__smtx_typeof.case_87 x_a0, EoCases.__smtx_typeof.case_88 x_a0, EoCases.__smtx_typeof.case_89 x_a0, EoCases.__smtx_typeof.case_90 x_a0, EoCases.__smtx_typeof.case_91 x_a0, EoCases.__smtx_typeof.case_92 x_a0, EoCases.__smtx_typeof.case_93 x_a0, EoCases.__smtx_typeof.case_94 x_a0, EoCases.__smtx_typeof.case_95 x_a0, EoCases.__smtx_typeof.case_96 x_a0, EoCases.__smtx_typeof.case_97 x_a0, EoCases.__smtx_typeof.case_98 x_a0, EoCases.__smtx_typeof.case_99 x_a0, EoCases.__smtx_typeof.case_100 x_a0, EoCases.__smtx_typeof.case_101 x_a0, EoCases.__smtx_typeof.case_102 x_a0, EoCases.__smtx_typeof.case_103 x_a0, EoCases.__smtx_typeof.case_104 x_a0, EoCases.__smtx_typeof.case_105 x_a0, EoCases.__smtx_typeof.case_106 x_a0, EoCases.__smtx_typeof.case_107 x_a0, EoCases.__smtx_typeof.case_108 x_a0, EoCases.__smtx_typeof.case_109 x_a0, EoCases.__smtx_typeof.case_110 x_a0, EoCases.__smtx_typeof.case_111 x_a0, EoCases.__smtx_typeof.case_112 x_a0, EoCases.__smtx_typeof.case_113 x_a0, EoCases.__smtx_typeof.case_114 x_a0, EoCases.__smtx_typeof.case_115 x_a0, EoCases.__smtx_typeof.case_116 x_a0, EoCases.__smtx_typeof.case_117 x_a0, EoCases.__smtx_typeof.case_118 x_a0, EoCases.__smtx_typeof.case_119 x_a0, EoCases.__smtx_typeof.case_120 x_a0, EoCases.__smtx_typeof.case_121 x_a0, EoCases.__smtx_typeof.case_122 x_a0, EoCases.__smtx_typeof.case_123 x_a0, EoCases.__smtx_typeof.case_124 x_a0, EoCases.__smtx_typeof.case_125 x_a0, EoCases.__smtx_typeof.case_126 x_a0, EoCases.__smtx_typeof.case_127 x_a0] = [] ++ [EoCases.__smtx_typeof.case_64 x_a0, EoCases.__smtx_typeof.case_65 x_a0, EoCases.__smtx_typeof.case_66 x_a0, EoCases.__smtx_typeof.case_67 x_a0, EoCases.__smtx_typeof.case_68 x_a0, EoCases.__smtx_typeof.case_69 x_a0, EoCases.__smtx_typeof.case_70 x_a0, EoCases.__smtx_typeof.case_71 x_a0, EoCases.__smtx_typeof.case_72 x_a0, EoCases.__smtx_typeof.case_73 x_a0, EoCases.__smtx_typeof.case_74 x_a0, EoCases.__smtx_typeof.case_75 x_a0, EoCases.__smtx_typeof.case_76 x_a0, EoCases.__smtx_typeof.case_77 x_a0, EoCases.__smtx_typeof.case_78 x_a0, EoCases.__smtx_typeof.case_79 x_a0] ++ [EoCases.__smtx_typeof.case_80 x_a0, EoCases.__smtx_typeof.case_81 x_a0, EoCases.__smtx_typeof.case_82 x_a0, EoCases.__smtx_typeof.case_83 x_a0, EoCases.__smtx_typeof.case_84 x_a0, EoCases.__smtx_typeof.case_85 x_a0, EoCases.__smtx_typeof.case_86 x_a0, EoCases.__smtx_typeof.case_87 x_a0, EoCases.__smtx_typeof.case_88 x_a0, EoCases.__smtx_typeof.case_89 x_a0, EoCases.__smtx_typeof.case_90 x_a0, EoCases.__smtx_typeof.case_91 x_a0, EoCases.__smtx_typeof.case_92 x_a0, EoCases.__smtx_typeof.case_93 x_a0, EoCases.__smtx_typeof.case_94 x_a0, EoCases.__smtx_typeof.case_95 x_a0, EoCases.__smtx_typeof.case_96 x_a0, EoCases.__smtx_typeof.case_97 x_a0, EoCases.__smtx_typeof.case_98 x_a0, EoCases.__smtx_typeof.case_99 x_a0, EoCases.__smtx_typeof.case_100 x_a0, EoCases.__smtx_typeof.case_101 x_a0, EoCases.__smtx_typeof.case_102 x_a0, EoCases.__smtx_typeof.case_103 x_a0, EoCases.__smtx_typeof.case_104 x_a0, EoCases.__smtx_typeof.case_105 x_a0, EoCases.__smtx_typeof.case_106 x_a0, EoCases.__smtx_typeof.case_107 x_a0, EoCases.__smtx_typeof.case_108 x_a0, EoCases.__smtx_typeof.case_109 x_a0, EoCases.__smtx_typeof.case_110 x_a0, EoCases.__smtx_typeof.case_111 x_a0, EoCases.__smtx_typeof.case_112 x_a0, EoCases.__smtx_typeof.case_113 x_a0, EoCases.__smtx_typeof.case_114 x_a0, EoCases.__smtx_typeof.case_115 x_a0, EoCases.__smtx_typeof.case_116 x_a0, EoCases.__smtx_typeof.case_117 x_a0, EoCases.__smtx_typeof.case_118 x_a0, EoCases.__smtx_typeof.case_119 x_a0, EoCases.__smtx_typeof.case_120 x_a0, EoCases.__smtx_typeof.case_121 x_a0, EoCases.__smtx_typeof.case_122 x_a0, EoCases.__smtx_typeof.case_123 x_a0, EoCases.__smtx_typeof.case_124 x_a0, EoCases.__smtx_typeof.case_125 x_a0, EoCases.__smtx_typeof.case_126 x_a0, EoCases.__smtx_typeof.case_127 x_a0] from rfl)
    otherwise ⟨hl_64, hl_65, hl_66, hl_67, hl_68, hl_69, hl_70, hl_71, hl_72, hl_73, hl_74, hl_75, hl_76, hl_77, hl_78, hl_79⟩ using
  group_round_step with cases_1_5_eo__24smtx_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_64 x_a0, EoCases.__smtx_typeof.case_65 x_a0, EoCases.__smtx_typeof.case_66 x_a0, EoCases.__smtx_typeof.case_67 x_a0, EoCases.__smtx_typeof.case_68 x_a0, EoCases.__smtx_typeof.case_69 x_a0, EoCases.__smtx_typeof.case_70 x_a0, EoCases.__smtx_typeof.case_71 x_a0, EoCases.__smtx_typeof.case_72 x_a0, EoCases.__smtx_typeof.case_73 x_a0, EoCases.__smtx_typeof.case_74 x_a0, EoCases.__smtx_typeof.case_75 x_a0, EoCases.__smtx_typeof.case_76 x_a0, EoCases.__smtx_typeof.case_77 x_a0, EoCases.__smtx_typeof.case_78 x_a0, EoCases.__smtx_typeof.case_79 x_a0, EoCases.__smtx_typeof.case_80 x_a0, EoCases.__smtx_typeof.case_81 x_a0, EoCases.__smtx_typeof.case_82 x_a0, EoCases.__smtx_typeof.case_83 x_a0, EoCases.__smtx_typeof.case_84 x_a0, EoCases.__smtx_typeof.case_85 x_a0, EoCases.__smtx_typeof.case_86 x_a0, EoCases.__smtx_typeof.case_87 x_a0, EoCases.__smtx_typeof.case_88 x_a0, EoCases.__smtx_typeof.case_89 x_a0, EoCases.__smtx_typeof.case_90 x_a0, EoCases.__smtx_typeof.case_91 x_a0, EoCases.__smtx_typeof.case_92 x_a0, EoCases.__smtx_typeof.case_93 x_a0, EoCases.__smtx_typeof.case_94 x_a0, EoCases.__smtx_typeof.case_95 x_a0, EoCases.__smtx_typeof.case_96 x_a0, EoCases.__smtx_typeof.case_97 x_a0, EoCases.__smtx_typeof.case_98 x_a0, EoCases.__smtx_typeof.case_99 x_a0, EoCases.__smtx_typeof.case_100 x_a0, EoCases.__smtx_typeof.case_101 x_a0, EoCases.__smtx_typeof.case_102 x_a0, EoCases.__smtx_typeof.case_103 x_a0, EoCases.__smtx_typeof.case_104 x_a0, EoCases.__smtx_typeof.case_105 x_a0, EoCases.__smtx_typeof.case_106 x_a0, EoCases.__smtx_typeof.case_107 x_a0, EoCases.__smtx_typeof.case_108 x_a0, EoCases.__smtx_typeof.case_109 x_a0, EoCases.__smtx_typeof.case_110 x_a0, EoCases.__smtx_typeof.case_111 x_a0, EoCases.__smtx_typeof.case_112 x_a0, EoCases.__smtx_typeof.case_113 x_a0, EoCases.__smtx_typeof.case_114 x_a0, EoCases.__smtx_typeof.case_115 x_a0, EoCases.__smtx_typeof.case_116 x_a0, EoCases.__smtx_typeof.case_117 x_a0, EoCases.__smtx_typeof.case_118 x_a0, EoCases.__smtx_typeof.case_119 x_a0, EoCases.__smtx_typeof.case_120 x_a0, EoCases.__smtx_typeof.case_121 x_a0, EoCases.__smtx_typeof.case_122 x_a0, EoCases.__smtx_typeof.case_123 x_a0, EoCases.__smtx_typeof.case_124 x_a0, EoCases.__smtx_typeof.case_125 x_a0, EoCases.__smtx_typeof.case_126 x_a0, EoCases.__smtx_typeof.case_127 x_a0] = [EoCases.__smtx_typeof.case_64 x_a0, EoCases.__smtx_typeof.case_65 x_a0, EoCases.__smtx_typeof.case_66 x_a0, EoCases.__smtx_typeof.case_67 x_a0, EoCases.__smtx_typeof.case_68 x_a0, EoCases.__smtx_typeof.case_69 x_a0, EoCases.__smtx_typeof.case_70 x_a0, EoCases.__smtx_typeof.case_71 x_a0, EoCases.__smtx_typeof.case_72 x_a0, EoCases.__smtx_typeof.case_73 x_a0, EoCases.__smtx_typeof.case_74 x_a0, EoCases.__smtx_typeof.case_75 x_a0, EoCases.__smtx_typeof.case_76 x_a0, EoCases.__smtx_typeof.case_77 x_a0, EoCases.__smtx_typeof.case_78 x_a0, EoCases.__smtx_typeof.case_79 x_a0] ++ [EoCases.__smtx_typeof.case_80 x_a0, EoCases.__smtx_typeof.case_81 x_a0, EoCases.__smtx_typeof.case_82 x_a0, EoCases.__smtx_typeof.case_83 x_a0, EoCases.__smtx_typeof.case_84 x_a0, EoCases.__smtx_typeof.case_85 x_a0, EoCases.__smtx_typeof.case_86 x_a0, EoCases.__smtx_typeof.case_87 x_a0, EoCases.__smtx_typeof.case_88 x_a0, EoCases.__smtx_typeof.case_89 x_a0, EoCases.__smtx_typeof.case_90 x_a0, EoCases.__smtx_typeof.case_91 x_a0, EoCases.__smtx_typeof.case_92 x_a0, EoCases.__smtx_typeof.case_93 x_a0, EoCases.__smtx_typeof.case_94 x_a0, EoCases.__smtx_typeof.case_95 x_a0] ++ [EoCases.__smtx_typeof.case_96 x_a0, EoCases.__smtx_typeof.case_97 x_a0, EoCases.__smtx_typeof.case_98 x_a0, EoCases.__smtx_typeof.case_99 x_a0, EoCases.__smtx_typeof.case_100 x_a0, EoCases.__smtx_typeof.case_101 x_a0, EoCases.__smtx_typeof.case_102 x_a0, EoCases.__smtx_typeof.case_103 x_a0, EoCases.__smtx_typeof.case_104 x_a0, EoCases.__smtx_typeof.case_105 x_a0, EoCases.__smtx_typeof.case_106 x_a0, EoCases.__smtx_typeof.case_107 x_a0, EoCases.__smtx_typeof.case_108 x_a0, EoCases.__smtx_typeof.case_109 x_a0, EoCases.__smtx_typeof.case_110 x_a0, EoCases.__smtx_typeof.case_111 x_a0, EoCases.__smtx_typeof.case_112 x_a0, EoCases.__smtx_typeof.case_113 x_a0, EoCases.__smtx_typeof.case_114 x_a0, EoCases.__smtx_typeof.case_115 x_a0, EoCases.__smtx_typeof.case_116 x_a0, EoCases.__smtx_typeof.case_117 x_a0, EoCases.__smtx_typeof.case_118 x_a0, EoCases.__smtx_typeof.case_119 x_a0, EoCases.__smtx_typeof.case_120 x_a0, EoCases.__smtx_typeof.case_121 x_a0, EoCases.__smtx_typeof.case_122 x_a0, EoCases.__smtx_typeof.case_123 x_a0, EoCases.__smtx_typeof.case_124 x_a0, EoCases.__smtx_typeof.case_125 x_a0, EoCases.__smtx_typeof.case_126 x_a0, EoCases.__smtx_typeof.case_127 x_a0] from rfl)
    otherwise ⟨hl_80, hl_81, hl_82, hl_83, hl_84, hl_85, hl_86, hl_87, hl_88, hl_89, hl_90, hl_91, hl_92, hl_93, hl_94, hl_95⟩ using hl_64 hl_65 hl_66 hl_67 hl_68 hl_69 hl_70 hl_71 hl_72 hl_73 hl_74 hl_75 hl_76 hl_77 hl_78 hl_79
  group_round_step with cases_1_6_eo__24smtx_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_64 x_a0, EoCases.__smtx_typeof.case_65 x_a0, EoCases.__smtx_typeof.case_66 x_a0, EoCases.__smtx_typeof.case_67 x_a0, EoCases.__smtx_typeof.case_68 x_a0, EoCases.__smtx_typeof.case_69 x_a0, EoCases.__smtx_typeof.case_70 x_a0, EoCases.__smtx_typeof.case_71 x_a0, EoCases.__smtx_typeof.case_72 x_a0, EoCases.__smtx_typeof.case_73 x_a0, EoCases.__smtx_typeof.case_74 x_a0, EoCases.__smtx_typeof.case_75 x_a0, EoCases.__smtx_typeof.case_76 x_a0, EoCases.__smtx_typeof.case_77 x_a0, EoCases.__smtx_typeof.case_78 x_a0, EoCases.__smtx_typeof.case_79 x_a0, EoCases.__smtx_typeof.case_80 x_a0, EoCases.__smtx_typeof.case_81 x_a0, EoCases.__smtx_typeof.case_82 x_a0, EoCases.__smtx_typeof.case_83 x_a0, EoCases.__smtx_typeof.case_84 x_a0, EoCases.__smtx_typeof.case_85 x_a0, EoCases.__smtx_typeof.case_86 x_a0, EoCases.__smtx_typeof.case_87 x_a0, EoCases.__smtx_typeof.case_88 x_a0, EoCases.__smtx_typeof.case_89 x_a0, EoCases.__smtx_typeof.case_90 x_a0, EoCases.__smtx_typeof.case_91 x_a0, EoCases.__smtx_typeof.case_92 x_a0, EoCases.__smtx_typeof.case_93 x_a0, EoCases.__smtx_typeof.case_94 x_a0, EoCases.__smtx_typeof.case_95 x_a0, EoCases.__smtx_typeof.case_96 x_a0, EoCases.__smtx_typeof.case_97 x_a0, EoCases.__smtx_typeof.case_98 x_a0, EoCases.__smtx_typeof.case_99 x_a0, EoCases.__smtx_typeof.case_100 x_a0, EoCases.__smtx_typeof.case_101 x_a0, EoCases.__smtx_typeof.case_102 x_a0, EoCases.__smtx_typeof.case_103 x_a0, EoCases.__smtx_typeof.case_104 x_a0, EoCases.__smtx_typeof.case_105 x_a0, EoCases.__smtx_typeof.case_106 x_a0, EoCases.__smtx_typeof.case_107 x_a0, EoCases.__smtx_typeof.case_108 x_a0, EoCases.__smtx_typeof.case_109 x_a0, EoCases.__smtx_typeof.case_110 x_a0, EoCases.__smtx_typeof.case_111 x_a0, EoCases.__smtx_typeof.case_112 x_a0, EoCases.__smtx_typeof.case_113 x_a0, EoCases.__smtx_typeof.case_114 x_a0, EoCases.__smtx_typeof.case_115 x_a0, EoCases.__smtx_typeof.case_116 x_a0, EoCases.__smtx_typeof.case_117 x_a0, EoCases.__smtx_typeof.case_118 x_a0, EoCases.__smtx_typeof.case_119 x_a0, EoCases.__smtx_typeof.case_120 x_a0, EoCases.__smtx_typeof.case_121 x_a0, EoCases.__smtx_typeof.case_122 x_a0, EoCases.__smtx_typeof.case_123 x_a0, EoCases.__smtx_typeof.case_124 x_a0, EoCases.__smtx_typeof.case_125 x_a0, EoCases.__smtx_typeof.case_126 x_a0, EoCases.__smtx_typeof.case_127 x_a0] = [EoCases.__smtx_typeof.case_64 x_a0, EoCases.__smtx_typeof.case_65 x_a0, EoCases.__smtx_typeof.case_66 x_a0, EoCases.__smtx_typeof.case_67 x_a0, EoCases.__smtx_typeof.case_68 x_a0, EoCases.__smtx_typeof.case_69 x_a0, EoCases.__smtx_typeof.case_70 x_a0, EoCases.__smtx_typeof.case_71 x_a0, EoCases.__smtx_typeof.case_72 x_a0, EoCases.__smtx_typeof.case_73 x_a0, EoCases.__smtx_typeof.case_74 x_a0, EoCases.__smtx_typeof.case_75 x_a0, EoCases.__smtx_typeof.case_76 x_a0, EoCases.__smtx_typeof.case_77 x_a0, EoCases.__smtx_typeof.case_78 x_a0, EoCases.__smtx_typeof.case_79 x_a0, EoCases.__smtx_typeof.case_80 x_a0, EoCases.__smtx_typeof.case_81 x_a0, EoCases.__smtx_typeof.case_82 x_a0, EoCases.__smtx_typeof.case_83 x_a0, EoCases.__smtx_typeof.case_84 x_a0, EoCases.__smtx_typeof.case_85 x_a0, EoCases.__smtx_typeof.case_86 x_a0, EoCases.__smtx_typeof.case_87 x_a0, EoCases.__smtx_typeof.case_88 x_a0, EoCases.__smtx_typeof.case_89 x_a0, EoCases.__smtx_typeof.case_90 x_a0, EoCases.__smtx_typeof.case_91 x_a0, EoCases.__smtx_typeof.case_92 x_a0, EoCases.__smtx_typeof.case_93 x_a0, EoCases.__smtx_typeof.case_94 x_a0, EoCases.__smtx_typeof.case_95 x_a0] ++ [EoCases.__smtx_typeof.case_96 x_a0, EoCases.__smtx_typeof.case_97 x_a0, EoCases.__smtx_typeof.case_98 x_a0, EoCases.__smtx_typeof.case_99 x_a0, EoCases.__smtx_typeof.case_100 x_a0, EoCases.__smtx_typeof.case_101 x_a0, EoCases.__smtx_typeof.case_102 x_a0, EoCases.__smtx_typeof.case_103 x_a0, EoCases.__smtx_typeof.case_104 x_a0, EoCases.__smtx_typeof.case_105 x_a0, EoCases.__smtx_typeof.case_106 x_a0, EoCases.__smtx_typeof.case_107 x_a0, EoCases.__smtx_typeof.case_108 x_a0, EoCases.__smtx_typeof.case_109 x_a0, EoCases.__smtx_typeof.case_110 x_a0, EoCases.__smtx_typeof.case_111 x_a0] ++ [EoCases.__smtx_typeof.case_112 x_a0, EoCases.__smtx_typeof.case_113 x_a0, EoCases.__smtx_typeof.case_114 x_a0, EoCases.__smtx_typeof.case_115 x_a0, EoCases.__smtx_typeof.case_116 x_a0, EoCases.__smtx_typeof.case_117 x_a0, EoCases.__smtx_typeof.case_118 x_a0, EoCases.__smtx_typeof.case_119 x_a0, EoCases.__smtx_typeof.case_120 x_a0, EoCases.__smtx_typeof.case_121 x_a0, EoCases.__smtx_typeof.case_122 x_a0, EoCases.__smtx_typeof.case_123 x_a0, EoCases.__smtx_typeof.case_124 x_a0, EoCases.__smtx_typeof.case_125 x_a0, EoCases.__smtx_typeof.case_126 x_a0, EoCases.__smtx_typeof.case_127 x_a0] from rfl)
    otherwise ⟨hl_96, hl_97, hl_98, hl_99, hl_100, hl_101, hl_102, hl_103, hl_104, hl_105, hl_106, hl_107, hl_108, hl_109, hl_110, hl_111⟩ using hl_64 hl_65 hl_66 hl_67 hl_68 hl_69 hl_70 hl_71 hl_72 hl_73 hl_74 hl_75 hl_76 hl_77 hl_78 hl_79 hl_80 hl_81 hl_82 hl_83 hl_84 hl_85 hl_86 hl_87 hl_88 hl_89 hl_90 hl_91 hl_92 hl_93 hl_94 hl_95
  group_round_step with cases_1_7_eo__24smtx_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_64 x_a0, EoCases.__smtx_typeof.case_65 x_a0, EoCases.__smtx_typeof.case_66 x_a0, EoCases.__smtx_typeof.case_67 x_a0, EoCases.__smtx_typeof.case_68 x_a0, EoCases.__smtx_typeof.case_69 x_a0, EoCases.__smtx_typeof.case_70 x_a0, EoCases.__smtx_typeof.case_71 x_a0, EoCases.__smtx_typeof.case_72 x_a0, EoCases.__smtx_typeof.case_73 x_a0, EoCases.__smtx_typeof.case_74 x_a0, EoCases.__smtx_typeof.case_75 x_a0, EoCases.__smtx_typeof.case_76 x_a0, EoCases.__smtx_typeof.case_77 x_a0, EoCases.__smtx_typeof.case_78 x_a0, EoCases.__smtx_typeof.case_79 x_a0, EoCases.__smtx_typeof.case_80 x_a0, EoCases.__smtx_typeof.case_81 x_a0, EoCases.__smtx_typeof.case_82 x_a0, EoCases.__smtx_typeof.case_83 x_a0, EoCases.__smtx_typeof.case_84 x_a0, EoCases.__smtx_typeof.case_85 x_a0, EoCases.__smtx_typeof.case_86 x_a0, EoCases.__smtx_typeof.case_87 x_a0, EoCases.__smtx_typeof.case_88 x_a0, EoCases.__smtx_typeof.case_89 x_a0, EoCases.__smtx_typeof.case_90 x_a0, EoCases.__smtx_typeof.case_91 x_a0, EoCases.__smtx_typeof.case_92 x_a0, EoCases.__smtx_typeof.case_93 x_a0, EoCases.__smtx_typeof.case_94 x_a0, EoCases.__smtx_typeof.case_95 x_a0, EoCases.__smtx_typeof.case_96 x_a0, EoCases.__smtx_typeof.case_97 x_a0, EoCases.__smtx_typeof.case_98 x_a0, EoCases.__smtx_typeof.case_99 x_a0, EoCases.__smtx_typeof.case_100 x_a0, EoCases.__smtx_typeof.case_101 x_a0, EoCases.__smtx_typeof.case_102 x_a0, EoCases.__smtx_typeof.case_103 x_a0, EoCases.__smtx_typeof.case_104 x_a0, EoCases.__smtx_typeof.case_105 x_a0, EoCases.__smtx_typeof.case_106 x_a0, EoCases.__smtx_typeof.case_107 x_a0, EoCases.__smtx_typeof.case_108 x_a0, EoCases.__smtx_typeof.case_109 x_a0, EoCases.__smtx_typeof.case_110 x_a0, EoCases.__smtx_typeof.case_111 x_a0, EoCases.__smtx_typeof.case_112 x_a0, EoCases.__smtx_typeof.case_113 x_a0, EoCases.__smtx_typeof.case_114 x_a0, EoCases.__smtx_typeof.case_115 x_a0, EoCases.__smtx_typeof.case_116 x_a0, EoCases.__smtx_typeof.case_117 x_a0, EoCases.__smtx_typeof.case_118 x_a0, EoCases.__smtx_typeof.case_119 x_a0, EoCases.__smtx_typeof.case_120 x_a0, EoCases.__smtx_typeof.case_121 x_a0, EoCases.__smtx_typeof.case_122 x_a0, EoCases.__smtx_typeof.case_123 x_a0, EoCases.__smtx_typeof.case_124 x_a0, EoCases.__smtx_typeof.case_125 x_a0, EoCases.__smtx_typeof.case_126 x_a0, EoCases.__smtx_typeof.case_127 x_a0] = [EoCases.__smtx_typeof.case_64 x_a0, EoCases.__smtx_typeof.case_65 x_a0, EoCases.__smtx_typeof.case_66 x_a0, EoCases.__smtx_typeof.case_67 x_a0, EoCases.__smtx_typeof.case_68 x_a0, EoCases.__smtx_typeof.case_69 x_a0, EoCases.__smtx_typeof.case_70 x_a0, EoCases.__smtx_typeof.case_71 x_a0, EoCases.__smtx_typeof.case_72 x_a0, EoCases.__smtx_typeof.case_73 x_a0, EoCases.__smtx_typeof.case_74 x_a0, EoCases.__smtx_typeof.case_75 x_a0, EoCases.__smtx_typeof.case_76 x_a0, EoCases.__smtx_typeof.case_77 x_a0, EoCases.__smtx_typeof.case_78 x_a0, EoCases.__smtx_typeof.case_79 x_a0, EoCases.__smtx_typeof.case_80 x_a0, EoCases.__smtx_typeof.case_81 x_a0, EoCases.__smtx_typeof.case_82 x_a0, EoCases.__smtx_typeof.case_83 x_a0, EoCases.__smtx_typeof.case_84 x_a0, EoCases.__smtx_typeof.case_85 x_a0, EoCases.__smtx_typeof.case_86 x_a0, EoCases.__smtx_typeof.case_87 x_a0, EoCases.__smtx_typeof.case_88 x_a0, EoCases.__smtx_typeof.case_89 x_a0, EoCases.__smtx_typeof.case_90 x_a0, EoCases.__smtx_typeof.case_91 x_a0, EoCases.__smtx_typeof.case_92 x_a0, EoCases.__smtx_typeof.case_93 x_a0, EoCases.__smtx_typeof.case_94 x_a0, EoCases.__smtx_typeof.case_95 x_a0, EoCases.__smtx_typeof.case_96 x_a0, EoCases.__smtx_typeof.case_97 x_a0, EoCases.__smtx_typeof.case_98 x_a0, EoCases.__smtx_typeof.case_99 x_a0, EoCases.__smtx_typeof.case_100 x_a0, EoCases.__smtx_typeof.case_101 x_a0, EoCases.__smtx_typeof.case_102 x_a0, EoCases.__smtx_typeof.case_103 x_a0, EoCases.__smtx_typeof.case_104 x_a0, EoCases.__smtx_typeof.case_105 x_a0, EoCases.__smtx_typeof.case_106 x_a0, EoCases.__smtx_typeof.case_107 x_a0, EoCases.__smtx_typeof.case_108 x_a0, EoCases.__smtx_typeof.case_109 x_a0, EoCases.__smtx_typeof.case_110 x_a0, EoCases.__smtx_typeof.case_111 x_a0] ++ [EoCases.__smtx_typeof.case_112 x_a0, EoCases.__smtx_typeof.case_113 x_a0, EoCases.__smtx_typeof.case_114 x_a0, EoCases.__smtx_typeof.case_115 x_a0, EoCases.__smtx_typeof.case_116 x_a0, EoCases.__smtx_typeof.case_117 x_a0, EoCases.__smtx_typeof.case_118 x_a0, EoCases.__smtx_typeof.case_119 x_a0, EoCases.__smtx_typeof.case_120 x_a0, EoCases.__smtx_typeof.case_121 x_a0, EoCases.__smtx_typeof.case_122 x_a0, EoCases.__smtx_typeof.case_123 x_a0, EoCases.__smtx_typeof.case_124 x_a0, EoCases.__smtx_typeof.case_125 x_a0, EoCases.__smtx_typeof.case_126 x_a0, EoCases.__smtx_typeof.case_127 x_a0] ++ [] from rfl)
    otherwise ⟨hl_112, hl_113, hl_114, hl_115, hl_116, hl_117, hl_118, hl_119, hl_120, hl_121, hl_122, hl_123, hl_124, hl_125, hl_126, hl_127⟩ using hl_64 hl_65 hl_66 hl_67 hl_68 hl_69 hl_70 hl_71 hl_72 hl_73 hl_74 hl_75 hl_76 hl_77 hl_78 hl_79 hl_80 hl_81 hl_82 hl_83 hl_84 hl_85 hl_86 hl_87 hl_88 hl_89 hl_90 hl_91 hl_92 hl_93 hl_94 hl_95 hl_96 hl_97 hl_98 hl_99 hl_100 hl_101 hl_102 hl_103 hl_104 hl_105 hl_106 hl_107 hl_108 hl_109 hl_110 hl_111
  group_none hinv4 hG with ⟨hl_64, hl_65, hl_66, hl_67, hl_68, hl_69, hl_70, hl_71, hl_72, hl_73, hl_74, hl_75, hl_76, hl_77, hl_78, hl_79, hl_80, hl_81, hl_82, hl_83, hl_84, hl_85, hl_86, hl_87, hl_88, hl_89, hl_90, hl_91, hl_92, hl_93, hl_94, hl_95, hl_96, hl_97, hl_98, hl_99, hl_100, hl_101, hl_102, hl_103, hl_104, hl_105, hl_106, hl_107, hl_108, hl_109, hl_110, hl_111, hl_112, hl_113, hl_114, hl_115, hl_116, hl_117, hl_118, hl_119, hl_120, hl_121, hl_122, hl_123, hl_124, hl_125, hl_126, hl_127⟩

theorem cases_2_2_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_2_2_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, (∀ d, firstSome [EoCases.__smtx_typeof.case_128 x_a0, EoCases.__smtx_typeof.case_129 x_a0, EoCases.__smtx_typeof.case_130 x_a0, EoCases.__smtx_typeof.case_131 x_a0, EoCases.__smtx_typeof.case_132 x_a0, EoCases.__smtx_typeof.case_133 x_a0, EoCases.__smtx_typeof.case_134 x_a0, EoCases.__smtx_typeof.case_135 x_a0, EoCases.__smtx_typeof.case_136 x_a0, EoCases.__smtx_typeof.case_137 x_a0, EoCases.__smtx_typeof.case_138 x_a0, EoCases.__smtx_typeof.case_139 x_a0, EoCases.__smtx_typeof.case_140 x_a0, EoCases.__smtx_typeof.case_141 x_a0, EoCases.__smtx_typeof.case_142 x_a0, EoCases.__smtx_typeof.case_143 x_a0, EoCases.__smtx_typeof.case_144 x_a0, EoCases.__smtx_typeof.case_145 x_a0, EoCases.__smtx_typeof.case_146 x_a0, EoCases.__smtx_typeof.case_147 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          ∀ d, firstSome [EoCases.__smtx_typeof.case_128 x_a0, EoCases.__smtx_typeof.case_129 x_a0, EoCases.__smtx_typeof.case_130 x_a0, EoCases.__smtx_typeof.case_131 x_a0, EoCases.__smtx_typeof.case_132 x_a0, EoCases.__smtx_typeof.case_133 x_a0, EoCases.__smtx_typeof.case_134 x_a0, EoCases.__smtx_typeof.case_135 x_a0, EoCases.__smtx_typeof.case_136 x_a0, EoCases.__smtx_typeof.case_137 x_a0, EoCases.__smtx_typeof.case_138 x_a0, EoCases.__smtx_typeof.case_139 x_a0, EoCases.__smtx_typeof.case_140 x_a0, EoCases.__smtx_typeof.case_141 x_a0, EoCases.__smtx_typeof.case_142 x_a0, EoCases.__smtx_typeof.case_143 x_a0, EoCases.__smtx_typeof.case_144 x_a0, EoCases.__smtx_typeof.case_145 x_a0, EoCases.__smtx_typeof.case_146 x_a0, EoCases.__smtx_typeof.case_147 x_a0] d = __smtx_typeof y0
      | core.result.Result.Ok none => EoCases.__smtx_typeof.case_128 x_a0 = none ∧ EoCases.__smtx_typeof.case_129 x_a0 = none ∧ EoCases.__smtx_typeof.case_130 x_a0 = none ∧ EoCases.__smtx_typeof.case_131 x_a0 = none ∧ EoCases.__smtx_typeof.case_132 x_a0 = none ∧ EoCases.__smtx_typeof.case_133 x_a0 = none ∧ EoCases.__smtx_typeof.case_134 x_a0 = none ∧ EoCases.__smtx_typeof.case_135 x_a0 = none ∧ EoCases.__smtx_typeof.case_136 x_a0 = none ∧ EoCases.__smtx_typeof.case_137 x_a0 = none ∧ EoCases.__smtx_typeof.case_138 x_a0 = none ∧ EoCases.__smtx_typeof.case_139 x_a0 = none ∧ EoCases.__smtx_typeof.case_140 x_a0 = none ∧ EoCases.__smtx_typeof.case_141 x_a0 = none ∧ EoCases.__smtx_typeof.case_142 x_a0 = none ∧ EoCases.__smtx_typeof.case_143 x_a0 = none ∧ EoCases.__smtx_typeof.case_144 x_a0 = none ∧ EoCases.__smtx_typeof.case_145 x_a0 = none ∧ EoCases.__smtx_typeof.case_146 x_a0 = none ∧ EoCases.__smtx_typeof.case_147 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_2_2_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  group_round_step with cases_1_8_eo__24smtx_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_128 x_a0, EoCases.__smtx_typeof.case_129 x_a0, EoCases.__smtx_typeof.case_130 x_a0, EoCases.__smtx_typeof.case_131 x_a0, EoCases.__smtx_typeof.case_132 x_a0, EoCases.__smtx_typeof.case_133 x_a0, EoCases.__smtx_typeof.case_134 x_a0, EoCases.__smtx_typeof.case_135 x_a0, EoCases.__smtx_typeof.case_136 x_a0, EoCases.__smtx_typeof.case_137 x_a0, EoCases.__smtx_typeof.case_138 x_a0, EoCases.__smtx_typeof.case_139 x_a0, EoCases.__smtx_typeof.case_140 x_a0, EoCases.__smtx_typeof.case_141 x_a0, EoCases.__smtx_typeof.case_142 x_a0, EoCases.__smtx_typeof.case_143 x_a0, EoCases.__smtx_typeof.case_144 x_a0, EoCases.__smtx_typeof.case_145 x_a0, EoCases.__smtx_typeof.case_146 x_a0, EoCases.__smtx_typeof.case_147 x_a0] = [] ++ [EoCases.__smtx_typeof.case_128 x_a0, EoCases.__smtx_typeof.case_129 x_a0, EoCases.__smtx_typeof.case_130 x_a0, EoCases.__smtx_typeof.case_131 x_a0, EoCases.__smtx_typeof.case_132 x_a0, EoCases.__smtx_typeof.case_133 x_a0, EoCases.__smtx_typeof.case_134 x_a0, EoCases.__smtx_typeof.case_135 x_a0, EoCases.__smtx_typeof.case_136 x_a0, EoCases.__smtx_typeof.case_137 x_a0, EoCases.__smtx_typeof.case_138 x_a0, EoCases.__smtx_typeof.case_139 x_a0, EoCases.__smtx_typeof.case_140 x_a0, EoCases.__smtx_typeof.case_141 x_a0, EoCases.__smtx_typeof.case_142 x_a0, EoCases.__smtx_typeof.case_143 x_a0] ++ [EoCases.__smtx_typeof.case_144 x_a0, EoCases.__smtx_typeof.case_145 x_a0, EoCases.__smtx_typeof.case_146 x_a0, EoCases.__smtx_typeof.case_147 x_a0] from rfl)
    otherwise ⟨hl_128, hl_129, hl_130, hl_131, hl_132, hl_133, hl_134, hl_135, hl_136, hl_137, hl_138, hl_139, hl_140, hl_141, hl_142, hl_143⟩ using
  group_round_step with cases_1_9_eo__24smtx_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_typeof.case_128 x_a0, EoCases.__smtx_typeof.case_129 x_a0, EoCases.__smtx_typeof.case_130 x_a0, EoCases.__smtx_typeof.case_131 x_a0, EoCases.__smtx_typeof.case_132 x_a0, EoCases.__smtx_typeof.case_133 x_a0, EoCases.__smtx_typeof.case_134 x_a0, EoCases.__smtx_typeof.case_135 x_a0, EoCases.__smtx_typeof.case_136 x_a0, EoCases.__smtx_typeof.case_137 x_a0, EoCases.__smtx_typeof.case_138 x_a0, EoCases.__smtx_typeof.case_139 x_a0, EoCases.__smtx_typeof.case_140 x_a0, EoCases.__smtx_typeof.case_141 x_a0, EoCases.__smtx_typeof.case_142 x_a0, EoCases.__smtx_typeof.case_143 x_a0, EoCases.__smtx_typeof.case_144 x_a0, EoCases.__smtx_typeof.case_145 x_a0, EoCases.__smtx_typeof.case_146 x_a0, EoCases.__smtx_typeof.case_147 x_a0] = [EoCases.__smtx_typeof.case_128 x_a0, EoCases.__smtx_typeof.case_129 x_a0, EoCases.__smtx_typeof.case_130 x_a0, EoCases.__smtx_typeof.case_131 x_a0, EoCases.__smtx_typeof.case_132 x_a0, EoCases.__smtx_typeof.case_133 x_a0, EoCases.__smtx_typeof.case_134 x_a0, EoCases.__smtx_typeof.case_135 x_a0, EoCases.__smtx_typeof.case_136 x_a0, EoCases.__smtx_typeof.case_137 x_a0, EoCases.__smtx_typeof.case_138 x_a0, EoCases.__smtx_typeof.case_139 x_a0, EoCases.__smtx_typeof.case_140 x_a0, EoCases.__smtx_typeof.case_141 x_a0, EoCases.__smtx_typeof.case_142 x_a0, EoCases.__smtx_typeof.case_143 x_a0] ++ [EoCases.__smtx_typeof.case_144 x_a0, EoCases.__smtx_typeof.case_145 x_a0, EoCases.__smtx_typeof.case_146 x_a0, EoCases.__smtx_typeof.case_147 x_a0] ++ [] from rfl)
    otherwise ⟨hl_144, hl_145, hl_146, hl_147⟩ using hl_128 hl_129 hl_130 hl_131 hl_132 hl_133 hl_134 hl_135 hl_136 hl_137 hl_138 hl_139 hl_140 hl_141 hl_142 hl_143
  group_none hinv2 hG with ⟨hl_128, hl_129, hl_130, hl_131, hl_132, hl_133, hl_134, hl_135, hl_136, hl_137, hl_138, hl_139, hl_140, hl_141, hl_142, hl_143, hl_144, hl_145, hl_146, hl_147⟩

/-- logos's `__smtx_typeof` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24smtx_5ftypeof.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __smtx_typeof x_a0 =
      (firstSome [EoCases.__smtx_typeof.case_0 x_a0, EoCases.__smtx_typeof.case_1 x_a0, EoCases.__smtx_typeof.case_2 x_a0, EoCases.__smtx_typeof.case_3 x_a0, EoCases.__smtx_typeof.case_4 x_a0, EoCases.__smtx_typeof.case_5 x_a0, EoCases.__smtx_typeof.case_6 x_a0, EoCases.__smtx_typeof.case_7 x_a0, EoCases.__smtx_typeof.case_8 x_a0, EoCases.__smtx_typeof.case_9 x_a0, EoCases.__smtx_typeof.case_10 x_a0, EoCases.__smtx_typeof.case_11 x_a0, EoCases.__smtx_typeof.case_12 x_a0, EoCases.__smtx_typeof.case_13 x_a0, EoCases.__smtx_typeof.case_14 x_a0, EoCases.__smtx_typeof.case_15 x_a0, EoCases.__smtx_typeof.case_16 x_a0, EoCases.__smtx_typeof.case_17 x_a0, EoCases.__smtx_typeof.case_18 x_a0, EoCases.__smtx_typeof.case_19 x_a0, EoCases.__smtx_typeof.case_20 x_a0, EoCases.__smtx_typeof.case_21 x_a0, EoCases.__smtx_typeof.case_22 x_a0, EoCases.__smtx_typeof.case_23 x_a0, EoCases.__smtx_typeof.case_24 x_a0, EoCases.__smtx_typeof.case_25 x_a0, EoCases.__smtx_typeof.case_26 x_a0, EoCases.__smtx_typeof.case_27 x_a0, EoCases.__smtx_typeof.case_28 x_a0, EoCases.__smtx_typeof.case_29 x_a0, EoCases.__smtx_typeof.case_30 x_a0, EoCases.__smtx_typeof.case_31 x_a0, EoCases.__smtx_typeof.case_32 x_a0, EoCases.__smtx_typeof.case_33 x_a0, EoCases.__smtx_typeof.case_34 x_a0, EoCases.__smtx_typeof.case_35 x_a0, EoCases.__smtx_typeof.case_36 x_a0, EoCases.__smtx_typeof.case_37 x_a0, EoCases.__smtx_typeof.case_38 x_a0, EoCases.__smtx_typeof.case_39 x_a0, EoCases.__smtx_typeof.case_40 x_a0, EoCases.__smtx_typeof.case_41 x_a0, EoCases.__smtx_typeof.case_42 x_a0, EoCases.__smtx_typeof.case_43 x_a0, EoCases.__smtx_typeof.case_44 x_a0, EoCases.__smtx_typeof.case_45 x_a0, EoCases.__smtx_typeof.case_46 x_a0, EoCases.__smtx_typeof.case_47 x_a0, EoCases.__smtx_typeof.case_48 x_a0, EoCases.__smtx_typeof.case_49 x_a0, EoCases.__smtx_typeof.case_50 x_a0, EoCases.__smtx_typeof.case_51 x_a0, EoCases.__smtx_typeof.case_52 x_a0, EoCases.__smtx_typeof.case_53 x_a0, EoCases.__smtx_typeof.case_54 x_a0, EoCases.__smtx_typeof.case_55 x_a0, EoCases.__smtx_typeof.case_56 x_a0, EoCases.__smtx_typeof.case_57 x_a0, EoCases.__smtx_typeof.case_58 x_a0, EoCases.__smtx_typeof.case_59 x_a0, EoCases.__smtx_typeof.case_60 x_a0, EoCases.__smtx_typeof.case_61 x_a0, EoCases.__smtx_typeof.case_62 x_a0, EoCases.__smtx_typeof.case_63 x_a0, EoCases.__smtx_typeof.case_64 x_a0, EoCases.__smtx_typeof.case_65 x_a0, EoCases.__smtx_typeof.case_66 x_a0, EoCases.__smtx_typeof.case_67 x_a0, EoCases.__smtx_typeof.case_68 x_a0, EoCases.__smtx_typeof.case_69 x_a0, EoCases.__smtx_typeof.case_70 x_a0, EoCases.__smtx_typeof.case_71 x_a0, EoCases.__smtx_typeof.case_72 x_a0, EoCases.__smtx_typeof.case_73 x_a0, EoCases.__smtx_typeof.case_74 x_a0, EoCases.__smtx_typeof.case_75 x_a0, EoCases.__smtx_typeof.case_76 x_a0, EoCases.__smtx_typeof.case_77 x_a0, EoCases.__smtx_typeof.case_78 x_a0, EoCases.__smtx_typeof.case_79 x_a0, EoCases.__smtx_typeof.case_80 x_a0, EoCases.__smtx_typeof.case_81 x_a0, EoCases.__smtx_typeof.case_82 x_a0, EoCases.__smtx_typeof.case_83 x_a0, EoCases.__smtx_typeof.case_84 x_a0, EoCases.__smtx_typeof.case_85 x_a0, EoCases.__smtx_typeof.case_86 x_a0, EoCases.__smtx_typeof.case_87 x_a0, EoCases.__smtx_typeof.case_88 x_a0, EoCases.__smtx_typeof.case_89 x_a0, EoCases.__smtx_typeof.case_90 x_a0, EoCases.__smtx_typeof.case_91 x_a0, EoCases.__smtx_typeof.case_92 x_a0, EoCases.__smtx_typeof.case_93 x_a0, EoCases.__smtx_typeof.case_94 x_a0, EoCases.__smtx_typeof.case_95 x_a0, EoCases.__smtx_typeof.case_96 x_a0, EoCases.__smtx_typeof.case_97 x_a0, EoCases.__smtx_typeof.case_98 x_a0, EoCases.__smtx_typeof.case_99 x_a0, EoCases.__smtx_typeof.case_100 x_a0, EoCases.__smtx_typeof.case_101 x_a0, EoCases.__smtx_typeof.case_102 x_a0, EoCases.__smtx_typeof.case_103 x_a0, EoCases.__smtx_typeof.case_104 x_a0, EoCases.__smtx_typeof.case_105 x_a0, EoCases.__smtx_typeof.case_106 x_a0, EoCases.__smtx_typeof.case_107 x_a0, EoCases.__smtx_typeof.case_108 x_a0, EoCases.__smtx_typeof.case_109 x_a0, EoCases.__smtx_typeof.case_110 x_a0, EoCases.__smtx_typeof.case_111 x_a0, EoCases.__smtx_typeof.case_112 x_a0, EoCases.__smtx_typeof.case_113 x_a0, EoCases.__smtx_typeof.case_114 x_a0, EoCases.__smtx_typeof.case_115 x_a0, EoCases.__smtx_typeof.case_116 x_a0, EoCases.__smtx_typeof.case_117 x_a0, EoCases.__smtx_typeof.case_118 x_a0, EoCases.__smtx_typeof.case_119 x_a0, EoCases.__smtx_typeof.case_120 x_a0, EoCases.__smtx_typeof.case_121 x_a0, EoCases.__smtx_typeof.case_122 x_a0, EoCases.__smtx_typeof.case_123 x_a0, EoCases.__smtx_typeof.case_124 x_a0, EoCases.__smtx_typeof.case_125 x_a0, EoCases.__smtx_typeof.case_126 x_a0, EoCases.__smtx_typeof.case_127 x_a0, EoCases.__smtx_typeof.case_128 x_a0, EoCases.__smtx_typeof.case_129 x_a0, EoCases.__smtx_typeof.case_130 x_a0, EoCases.__smtx_typeof.case_131 x_a0, EoCases.__smtx_typeof.case_132 x_a0, EoCases.__smtx_typeof.case_133 x_a0, EoCases.__smtx_typeof.case_134 x_a0, EoCases.__smtx_typeof.case_135 x_a0, EoCases.__smtx_typeof.case_136 x_a0, EoCases.__smtx_typeof.case_137 x_a0, EoCases.__smtx_typeof.case_138 x_a0, EoCases.__smtx_typeof.case_139 x_a0, EoCases.__smtx_typeof.case_140 x_a0, EoCases.__smtx_typeof.case_141 x_a0, EoCases.__smtx_typeof.case_142 x_a0, EoCases.__smtx_typeof.case_143 x_a0, EoCases.__smtx_typeof.case_144 x_a0, EoCases.__smtx_typeof.case_145 x_a0, EoCases.__smtx_typeof.case_146 x_a0, EoCases.__smtx_typeof.case_147 x_a0] default) := by
  logos_eq_large

theorem step_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    step_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (Next.Done t) => Represents.rep s' t (__smtx_typeof x_a0)
      | core.result.Result.Ok (Next.Again arr) =>
        s'.budget < s.budget ∧ ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          __smtx_typeof x_a0 = __smtx_typeof y0
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24smtx_5ftypeof.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold step_eo__24smtx_5ftypeof
  have hG := Store.Grows.refl s
  tick_step as ⟨s1, hinv1⟩ growing hG carrying h_a0
  body_group_round_step with cases_2_0_eo__24smtx_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 hbud
    split (show [EoCases.__smtx_typeof.case_0 x_a0, EoCases.__smtx_typeof.case_1 x_a0, EoCases.__smtx_typeof.case_2 x_a0, EoCases.__smtx_typeof.case_3 x_a0, EoCases.__smtx_typeof.case_4 x_a0, EoCases.__smtx_typeof.case_5 x_a0, EoCases.__smtx_typeof.case_6 x_a0, EoCases.__smtx_typeof.case_7 x_a0, EoCases.__smtx_typeof.case_8 x_a0, EoCases.__smtx_typeof.case_9 x_a0, EoCases.__smtx_typeof.case_10 x_a0, EoCases.__smtx_typeof.case_11 x_a0, EoCases.__smtx_typeof.case_12 x_a0, EoCases.__smtx_typeof.case_13 x_a0, EoCases.__smtx_typeof.case_14 x_a0, EoCases.__smtx_typeof.case_15 x_a0, EoCases.__smtx_typeof.case_16 x_a0, EoCases.__smtx_typeof.case_17 x_a0, EoCases.__smtx_typeof.case_18 x_a0, EoCases.__smtx_typeof.case_19 x_a0, EoCases.__smtx_typeof.case_20 x_a0, EoCases.__smtx_typeof.case_21 x_a0, EoCases.__smtx_typeof.case_22 x_a0, EoCases.__smtx_typeof.case_23 x_a0, EoCases.__smtx_typeof.case_24 x_a0, EoCases.__smtx_typeof.case_25 x_a0, EoCases.__smtx_typeof.case_26 x_a0, EoCases.__smtx_typeof.case_27 x_a0, EoCases.__smtx_typeof.case_28 x_a0, EoCases.__smtx_typeof.case_29 x_a0, EoCases.__smtx_typeof.case_30 x_a0, EoCases.__smtx_typeof.case_31 x_a0, EoCases.__smtx_typeof.case_32 x_a0, EoCases.__smtx_typeof.case_33 x_a0, EoCases.__smtx_typeof.case_34 x_a0, EoCases.__smtx_typeof.case_35 x_a0, EoCases.__smtx_typeof.case_36 x_a0, EoCases.__smtx_typeof.case_37 x_a0, EoCases.__smtx_typeof.case_38 x_a0, EoCases.__smtx_typeof.case_39 x_a0, EoCases.__smtx_typeof.case_40 x_a0, EoCases.__smtx_typeof.case_41 x_a0, EoCases.__smtx_typeof.case_42 x_a0, EoCases.__smtx_typeof.case_43 x_a0, EoCases.__smtx_typeof.case_44 x_a0, EoCases.__smtx_typeof.case_45 x_a0, EoCases.__smtx_typeof.case_46 x_a0, EoCases.__smtx_typeof.case_47 x_a0, EoCases.__smtx_typeof.case_48 x_a0, EoCases.__smtx_typeof.case_49 x_a0, EoCases.__smtx_typeof.case_50 x_a0, EoCases.__smtx_typeof.case_51 x_a0, EoCases.__smtx_typeof.case_52 x_a0, EoCases.__smtx_typeof.case_53 x_a0, EoCases.__smtx_typeof.case_54 x_a0, EoCases.__smtx_typeof.case_55 x_a0, EoCases.__smtx_typeof.case_56 x_a0, EoCases.__smtx_typeof.case_57 x_a0, EoCases.__smtx_typeof.case_58 x_a0, EoCases.__smtx_typeof.case_59 x_a0, EoCases.__smtx_typeof.case_60 x_a0, EoCases.__smtx_typeof.case_61 x_a0, EoCases.__smtx_typeof.case_62 x_a0, EoCases.__smtx_typeof.case_63 x_a0, EoCases.__smtx_typeof.case_64 x_a0, EoCases.__smtx_typeof.case_65 x_a0, EoCases.__smtx_typeof.case_66 x_a0, EoCases.__smtx_typeof.case_67 x_a0, EoCases.__smtx_typeof.case_68 x_a0, EoCases.__smtx_typeof.case_69 x_a0, EoCases.__smtx_typeof.case_70 x_a0, EoCases.__smtx_typeof.case_71 x_a0, EoCases.__smtx_typeof.case_72 x_a0, EoCases.__smtx_typeof.case_73 x_a0, EoCases.__smtx_typeof.case_74 x_a0, EoCases.__smtx_typeof.case_75 x_a0, EoCases.__smtx_typeof.case_76 x_a0, EoCases.__smtx_typeof.case_77 x_a0, EoCases.__smtx_typeof.case_78 x_a0, EoCases.__smtx_typeof.case_79 x_a0, EoCases.__smtx_typeof.case_80 x_a0, EoCases.__smtx_typeof.case_81 x_a0, EoCases.__smtx_typeof.case_82 x_a0, EoCases.__smtx_typeof.case_83 x_a0, EoCases.__smtx_typeof.case_84 x_a0, EoCases.__smtx_typeof.case_85 x_a0, EoCases.__smtx_typeof.case_86 x_a0, EoCases.__smtx_typeof.case_87 x_a0, EoCases.__smtx_typeof.case_88 x_a0, EoCases.__smtx_typeof.case_89 x_a0, EoCases.__smtx_typeof.case_90 x_a0, EoCases.__smtx_typeof.case_91 x_a0, EoCases.__smtx_typeof.case_92 x_a0, EoCases.__smtx_typeof.case_93 x_a0, EoCases.__smtx_typeof.case_94 x_a0, EoCases.__smtx_typeof.case_95 x_a0, EoCases.__smtx_typeof.case_96 x_a0, EoCases.__smtx_typeof.case_97 x_a0, EoCases.__smtx_typeof.case_98 x_a0, EoCases.__smtx_typeof.case_99 x_a0, EoCases.__smtx_typeof.case_100 x_a0, EoCases.__smtx_typeof.case_101 x_a0, EoCases.__smtx_typeof.case_102 x_a0, EoCases.__smtx_typeof.case_103 x_a0, EoCases.__smtx_typeof.case_104 x_a0, EoCases.__smtx_typeof.case_105 x_a0, EoCases.__smtx_typeof.case_106 x_a0, EoCases.__smtx_typeof.case_107 x_a0, EoCases.__smtx_typeof.case_108 x_a0, EoCases.__smtx_typeof.case_109 x_a0, EoCases.__smtx_typeof.case_110 x_a0, EoCases.__smtx_typeof.case_111 x_a0, EoCases.__smtx_typeof.case_112 x_a0, EoCases.__smtx_typeof.case_113 x_a0, EoCases.__smtx_typeof.case_114 x_a0, EoCases.__smtx_typeof.case_115 x_a0, EoCases.__smtx_typeof.case_116 x_a0, EoCases.__smtx_typeof.case_117 x_a0, EoCases.__smtx_typeof.case_118 x_a0, EoCases.__smtx_typeof.case_119 x_a0, EoCases.__smtx_typeof.case_120 x_a0, EoCases.__smtx_typeof.case_121 x_a0, EoCases.__smtx_typeof.case_122 x_a0, EoCases.__smtx_typeof.case_123 x_a0, EoCases.__smtx_typeof.case_124 x_a0, EoCases.__smtx_typeof.case_125 x_a0, EoCases.__smtx_typeof.case_126 x_a0, EoCases.__smtx_typeof.case_127 x_a0, EoCases.__smtx_typeof.case_128 x_a0, EoCases.__smtx_typeof.case_129 x_a0, EoCases.__smtx_typeof.case_130 x_a0, EoCases.__smtx_typeof.case_131 x_a0, EoCases.__smtx_typeof.case_132 x_a0, EoCases.__smtx_typeof.case_133 x_a0, EoCases.__smtx_typeof.case_134 x_a0, EoCases.__smtx_typeof.case_135 x_a0, EoCases.__smtx_typeof.case_136 x_a0, EoCases.__smtx_typeof.case_137 x_a0, EoCases.__smtx_typeof.case_138 x_a0, EoCases.__smtx_typeof.case_139 x_a0, EoCases.__smtx_typeof.case_140 x_a0, EoCases.__smtx_typeof.case_141 x_a0, EoCases.__smtx_typeof.case_142 x_a0, EoCases.__smtx_typeof.case_143 x_a0, EoCases.__smtx_typeof.case_144 x_a0, EoCases.__smtx_typeof.case_145 x_a0, EoCases.__smtx_typeof.case_146 x_a0, EoCases.__smtx_typeof.case_147 x_a0] = [] ++ [EoCases.__smtx_typeof.case_0 x_a0, EoCases.__smtx_typeof.case_1 x_a0, EoCases.__smtx_typeof.case_2 x_a0, EoCases.__smtx_typeof.case_3 x_a0, EoCases.__smtx_typeof.case_4 x_a0, EoCases.__smtx_typeof.case_5 x_a0, EoCases.__smtx_typeof.case_6 x_a0, EoCases.__smtx_typeof.case_7 x_a0, EoCases.__smtx_typeof.case_8 x_a0, EoCases.__smtx_typeof.case_9 x_a0, EoCases.__smtx_typeof.case_10 x_a0, EoCases.__smtx_typeof.case_11 x_a0, EoCases.__smtx_typeof.case_12 x_a0, EoCases.__smtx_typeof.case_13 x_a0, EoCases.__smtx_typeof.case_14 x_a0, EoCases.__smtx_typeof.case_15 x_a0, EoCases.__smtx_typeof.case_16 x_a0, EoCases.__smtx_typeof.case_17 x_a0, EoCases.__smtx_typeof.case_18 x_a0, EoCases.__smtx_typeof.case_19 x_a0, EoCases.__smtx_typeof.case_20 x_a0, EoCases.__smtx_typeof.case_21 x_a0, EoCases.__smtx_typeof.case_22 x_a0, EoCases.__smtx_typeof.case_23 x_a0, EoCases.__smtx_typeof.case_24 x_a0, EoCases.__smtx_typeof.case_25 x_a0, EoCases.__smtx_typeof.case_26 x_a0, EoCases.__smtx_typeof.case_27 x_a0, EoCases.__smtx_typeof.case_28 x_a0, EoCases.__smtx_typeof.case_29 x_a0, EoCases.__smtx_typeof.case_30 x_a0, EoCases.__smtx_typeof.case_31 x_a0, EoCases.__smtx_typeof.case_32 x_a0, EoCases.__smtx_typeof.case_33 x_a0, EoCases.__smtx_typeof.case_34 x_a0, EoCases.__smtx_typeof.case_35 x_a0, EoCases.__smtx_typeof.case_36 x_a0, EoCases.__smtx_typeof.case_37 x_a0, EoCases.__smtx_typeof.case_38 x_a0, EoCases.__smtx_typeof.case_39 x_a0, EoCases.__smtx_typeof.case_40 x_a0, EoCases.__smtx_typeof.case_41 x_a0, EoCases.__smtx_typeof.case_42 x_a0, EoCases.__smtx_typeof.case_43 x_a0, EoCases.__smtx_typeof.case_44 x_a0, EoCases.__smtx_typeof.case_45 x_a0, EoCases.__smtx_typeof.case_46 x_a0, EoCases.__smtx_typeof.case_47 x_a0, EoCases.__smtx_typeof.case_48 x_a0, EoCases.__smtx_typeof.case_49 x_a0, EoCases.__smtx_typeof.case_50 x_a0, EoCases.__smtx_typeof.case_51 x_a0, EoCases.__smtx_typeof.case_52 x_a0, EoCases.__smtx_typeof.case_53 x_a0, EoCases.__smtx_typeof.case_54 x_a0, EoCases.__smtx_typeof.case_55 x_a0, EoCases.__smtx_typeof.case_56 x_a0, EoCases.__smtx_typeof.case_57 x_a0, EoCases.__smtx_typeof.case_58 x_a0, EoCases.__smtx_typeof.case_59 x_a0, EoCases.__smtx_typeof.case_60 x_a0, EoCases.__smtx_typeof.case_61 x_a0, EoCases.__smtx_typeof.case_62 x_a0, EoCases.__smtx_typeof.case_63 x_a0] ++ [EoCases.__smtx_typeof.case_64 x_a0, EoCases.__smtx_typeof.case_65 x_a0, EoCases.__smtx_typeof.case_66 x_a0, EoCases.__smtx_typeof.case_67 x_a0, EoCases.__smtx_typeof.case_68 x_a0, EoCases.__smtx_typeof.case_69 x_a0, EoCases.__smtx_typeof.case_70 x_a0, EoCases.__smtx_typeof.case_71 x_a0, EoCases.__smtx_typeof.case_72 x_a0, EoCases.__smtx_typeof.case_73 x_a0, EoCases.__smtx_typeof.case_74 x_a0, EoCases.__smtx_typeof.case_75 x_a0, EoCases.__smtx_typeof.case_76 x_a0, EoCases.__smtx_typeof.case_77 x_a0, EoCases.__smtx_typeof.case_78 x_a0, EoCases.__smtx_typeof.case_79 x_a0, EoCases.__smtx_typeof.case_80 x_a0, EoCases.__smtx_typeof.case_81 x_a0, EoCases.__smtx_typeof.case_82 x_a0, EoCases.__smtx_typeof.case_83 x_a0, EoCases.__smtx_typeof.case_84 x_a0, EoCases.__smtx_typeof.case_85 x_a0, EoCases.__smtx_typeof.case_86 x_a0, EoCases.__smtx_typeof.case_87 x_a0, EoCases.__smtx_typeof.case_88 x_a0, EoCases.__smtx_typeof.case_89 x_a0, EoCases.__smtx_typeof.case_90 x_a0, EoCases.__smtx_typeof.case_91 x_a0, EoCases.__smtx_typeof.case_92 x_a0, EoCases.__smtx_typeof.case_93 x_a0, EoCases.__smtx_typeof.case_94 x_a0, EoCases.__smtx_typeof.case_95 x_a0, EoCases.__smtx_typeof.case_96 x_a0, EoCases.__smtx_typeof.case_97 x_a0, EoCases.__smtx_typeof.case_98 x_a0, EoCases.__smtx_typeof.case_99 x_a0, EoCases.__smtx_typeof.case_100 x_a0, EoCases.__smtx_typeof.case_101 x_a0, EoCases.__smtx_typeof.case_102 x_a0, EoCases.__smtx_typeof.case_103 x_a0, EoCases.__smtx_typeof.case_104 x_a0, EoCases.__smtx_typeof.case_105 x_a0, EoCases.__smtx_typeof.case_106 x_a0, EoCases.__smtx_typeof.case_107 x_a0, EoCases.__smtx_typeof.case_108 x_a0, EoCases.__smtx_typeof.case_109 x_a0, EoCases.__smtx_typeof.case_110 x_a0, EoCases.__smtx_typeof.case_111 x_a0, EoCases.__smtx_typeof.case_112 x_a0, EoCases.__smtx_typeof.case_113 x_a0, EoCases.__smtx_typeof.case_114 x_a0, EoCases.__smtx_typeof.case_115 x_a0, EoCases.__smtx_typeof.case_116 x_a0, EoCases.__smtx_typeof.case_117 x_a0, EoCases.__smtx_typeof.case_118 x_a0, EoCases.__smtx_typeof.case_119 x_a0, EoCases.__smtx_typeof.case_120 x_a0, EoCases.__smtx_typeof.case_121 x_a0, EoCases.__smtx_typeof.case_122 x_a0, EoCases.__smtx_typeof.case_123 x_a0, EoCases.__smtx_typeof.case_124 x_a0, EoCases.__smtx_typeof.case_125 x_a0, EoCases.__smtx_typeof.case_126 x_a0, EoCases.__smtx_typeof.case_127 x_a0, EoCases.__smtx_typeof.case_128 x_a0, EoCases.__smtx_typeof.case_129 x_a0, EoCases.__smtx_typeof.case_130 x_a0, EoCases.__smtx_typeof.case_131 x_a0, EoCases.__smtx_typeof.case_132 x_a0, EoCases.__smtx_typeof.case_133 x_a0, EoCases.__smtx_typeof.case_134 x_a0, EoCases.__smtx_typeof.case_135 x_a0, EoCases.__smtx_typeof.case_136 x_a0, EoCases.__smtx_typeof.case_137 x_a0, EoCases.__smtx_typeof.case_138 x_a0, EoCases.__smtx_typeof.case_139 x_a0, EoCases.__smtx_typeof.case_140 x_a0, EoCases.__smtx_typeof.case_141 x_a0, EoCases.__smtx_typeof.case_142 x_a0, EoCases.__smtx_typeof.case_143 x_a0, EoCases.__smtx_typeof.case_144 x_a0, EoCases.__smtx_typeof.case_145 x_a0, EoCases.__smtx_typeof.case_146 x_a0, EoCases.__smtx_typeof.case_147 x_a0] from rfl)
    otherwise ⟨hl_0, hl_1, hl_2, hl_3, hl_4, hl_5, hl_6, hl_7, hl_8, hl_9, hl_10, hl_11, hl_12, hl_13, hl_14, hl_15, hl_16, hl_17, hl_18, hl_19, hl_20, hl_21, hl_22, hl_23, hl_24, hl_25, hl_26, hl_27, hl_28, hl_29, hl_30, hl_31, hl_32, hl_33, hl_34, hl_35, hl_36, hl_37, hl_38, hl_39, hl_40, hl_41, hl_42, hl_43, hl_44, hl_45, hl_46, hl_47, hl_48, hl_49, hl_50, hl_51, hl_52, hl_53, hl_54, hl_55, hl_56, hl_57, hl_58, hl_59, hl_60, hl_61, hl_62, hl_63⟩ using
  body_group_round_step with cases_2_1_eo__24smtx_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0 hbud
    split (show [EoCases.__smtx_typeof.case_0 x_a0, EoCases.__smtx_typeof.case_1 x_a0, EoCases.__smtx_typeof.case_2 x_a0, EoCases.__smtx_typeof.case_3 x_a0, EoCases.__smtx_typeof.case_4 x_a0, EoCases.__smtx_typeof.case_5 x_a0, EoCases.__smtx_typeof.case_6 x_a0, EoCases.__smtx_typeof.case_7 x_a0, EoCases.__smtx_typeof.case_8 x_a0, EoCases.__smtx_typeof.case_9 x_a0, EoCases.__smtx_typeof.case_10 x_a0, EoCases.__smtx_typeof.case_11 x_a0, EoCases.__smtx_typeof.case_12 x_a0, EoCases.__smtx_typeof.case_13 x_a0, EoCases.__smtx_typeof.case_14 x_a0, EoCases.__smtx_typeof.case_15 x_a0, EoCases.__smtx_typeof.case_16 x_a0, EoCases.__smtx_typeof.case_17 x_a0, EoCases.__smtx_typeof.case_18 x_a0, EoCases.__smtx_typeof.case_19 x_a0, EoCases.__smtx_typeof.case_20 x_a0, EoCases.__smtx_typeof.case_21 x_a0, EoCases.__smtx_typeof.case_22 x_a0, EoCases.__smtx_typeof.case_23 x_a0, EoCases.__smtx_typeof.case_24 x_a0, EoCases.__smtx_typeof.case_25 x_a0, EoCases.__smtx_typeof.case_26 x_a0, EoCases.__smtx_typeof.case_27 x_a0, EoCases.__smtx_typeof.case_28 x_a0, EoCases.__smtx_typeof.case_29 x_a0, EoCases.__smtx_typeof.case_30 x_a0, EoCases.__smtx_typeof.case_31 x_a0, EoCases.__smtx_typeof.case_32 x_a0, EoCases.__smtx_typeof.case_33 x_a0, EoCases.__smtx_typeof.case_34 x_a0, EoCases.__smtx_typeof.case_35 x_a0, EoCases.__smtx_typeof.case_36 x_a0, EoCases.__smtx_typeof.case_37 x_a0, EoCases.__smtx_typeof.case_38 x_a0, EoCases.__smtx_typeof.case_39 x_a0, EoCases.__smtx_typeof.case_40 x_a0, EoCases.__smtx_typeof.case_41 x_a0, EoCases.__smtx_typeof.case_42 x_a0, EoCases.__smtx_typeof.case_43 x_a0, EoCases.__smtx_typeof.case_44 x_a0, EoCases.__smtx_typeof.case_45 x_a0, EoCases.__smtx_typeof.case_46 x_a0, EoCases.__smtx_typeof.case_47 x_a0, EoCases.__smtx_typeof.case_48 x_a0, EoCases.__smtx_typeof.case_49 x_a0, EoCases.__smtx_typeof.case_50 x_a0, EoCases.__smtx_typeof.case_51 x_a0, EoCases.__smtx_typeof.case_52 x_a0, EoCases.__smtx_typeof.case_53 x_a0, EoCases.__smtx_typeof.case_54 x_a0, EoCases.__smtx_typeof.case_55 x_a0, EoCases.__smtx_typeof.case_56 x_a0, EoCases.__smtx_typeof.case_57 x_a0, EoCases.__smtx_typeof.case_58 x_a0, EoCases.__smtx_typeof.case_59 x_a0, EoCases.__smtx_typeof.case_60 x_a0, EoCases.__smtx_typeof.case_61 x_a0, EoCases.__smtx_typeof.case_62 x_a0, EoCases.__smtx_typeof.case_63 x_a0, EoCases.__smtx_typeof.case_64 x_a0, EoCases.__smtx_typeof.case_65 x_a0, EoCases.__smtx_typeof.case_66 x_a0, EoCases.__smtx_typeof.case_67 x_a0, EoCases.__smtx_typeof.case_68 x_a0, EoCases.__smtx_typeof.case_69 x_a0, EoCases.__smtx_typeof.case_70 x_a0, EoCases.__smtx_typeof.case_71 x_a0, EoCases.__smtx_typeof.case_72 x_a0, EoCases.__smtx_typeof.case_73 x_a0, EoCases.__smtx_typeof.case_74 x_a0, EoCases.__smtx_typeof.case_75 x_a0, EoCases.__smtx_typeof.case_76 x_a0, EoCases.__smtx_typeof.case_77 x_a0, EoCases.__smtx_typeof.case_78 x_a0, EoCases.__smtx_typeof.case_79 x_a0, EoCases.__smtx_typeof.case_80 x_a0, EoCases.__smtx_typeof.case_81 x_a0, EoCases.__smtx_typeof.case_82 x_a0, EoCases.__smtx_typeof.case_83 x_a0, EoCases.__smtx_typeof.case_84 x_a0, EoCases.__smtx_typeof.case_85 x_a0, EoCases.__smtx_typeof.case_86 x_a0, EoCases.__smtx_typeof.case_87 x_a0, EoCases.__smtx_typeof.case_88 x_a0, EoCases.__smtx_typeof.case_89 x_a0, EoCases.__smtx_typeof.case_90 x_a0, EoCases.__smtx_typeof.case_91 x_a0, EoCases.__smtx_typeof.case_92 x_a0, EoCases.__smtx_typeof.case_93 x_a0, EoCases.__smtx_typeof.case_94 x_a0, EoCases.__smtx_typeof.case_95 x_a0, EoCases.__smtx_typeof.case_96 x_a0, EoCases.__smtx_typeof.case_97 x_a0, EoCases.__smtx_typeof.case_98 x_a0, EoCases.__smtx_typeof.case_99 x_a0, EoCases.__smtx_typeof.case_100 x_a0, EoCases.__smtx_typeof.case_101 x_a0, EoCases.__smtx_typeof.case_102 x_a0, EoCases.__smtx_typeof.case_103 x_a0, EoCases.__smtx_typeof.case_104 x_a0, EoCases.__smtx_typeof.case_105 x_a0, EoCases.__smtx_typeof.case_106 x_a0, EoCases.__smtx_typeof.case_107 x_a0, EoCases.__smtx_typeof.case_108 x_a0, EoCases.__smtx_typeof.case_109 x_a0, EoCases.__smtx_typeof.case_110 x_a0, EoCases.__smtx_typeof.case_111 x_a0, EoCases.__smtx_typeof.case_112 x_a0, EoCases.__smtx_typeof.case_113 x_a0, EoCases.__smtx_typeof.case_114 x_a0, EoCases.__smtx_typeof.case_115 x_a0, EoCases.__smtx_typeof.case_116 x_a0, EoCases.__smtx_typeof.case_117 x_a0, EoCases.__smtx_typeof.case_118 x_a0, EoCases.__smtx_typeof.case_119 x_a0, EoCases.__smtx_typeof.case_120 x_a0, EoCases.__smtx_typeof.case_121 x_a0, EoCases.__smtx_typeof.case_122 x_a0, EoCases.__smtx_typeof.case_123 x_a0, EoCases.__smtx_typeof.case_124 x_a0, EoCases.__smtx_typeof.case_125 x_a0, EoCases.__smtx_typeof.case_126 x_a0, EoCases.__smtx_typeof.case_127 x_a0, EoCases.__smtx_typeof.case_128 x_a0, EoCases.__smtx_typeof.case_129 x_a0, EoCases.__smtx_typeof.case_130 x_a0, EoCases.__smtx_typeof.case_131 x_a0, EoCases.__smtx_typeof.case_132 x_a0, EoCases.__smtx_typeof.case_133 x_a0, EoCases.__smtx_typeof.case_134 x_a0, EoCases.__smtx_typeof.case_135 x_a0, EoCases.__smtx_typeof.case_136 x_a0, EoCases.__smtx_typeof.case_137 x_a0, EoCases.__smtx_typeof.case_138 x_a0, EoCases.__smtx_typeof.case_139 x_a0, EoCases.__smtx_typeof.case_140 x_a0, EoCases.__smtx_typeof.case_141 x_a0, EoCases.__smtx_typeof.case_142 x_a0, EoCases.__smtx_typeof.case_143 x_a0, EoCases.__smtx_typeof.case_144 x_a0, EoCases.__smtx_typeof.case_145 x_a0, EoCases.__smtx_typeof.case_146 x_a0, EoCases.__smtx_typeof.case_147 x_a0] = [EoCases.__smtx_typeof.case_0 x_a0, EoCases.__smtx_typeof.case_1 x_a0, EoCases.__smtx_typeof.case_2 x_a0, EoCases.__smtx_typeof.case_3 x_a0, EoCases.__smtx_typeof.case_4 x_a0, EoCases.__smtx_typeof.case_5 x_a0, EoCases.__smtx_typeof.case_6 x_a0, EoCases.__smtx_typeof.case_7 x_a0, EoCases.__smtx_typeof.case_8 x_a0, EoCases.__smtx_typeof.case_9 x_a0, EoCases.__smtx_typeof.case_10 x_a0, EoCases.__smtx_typeof.case_11 x_a0, EoCases.__smtx_typeof.case_12 x_a0, EoCases.__smtx_typeof.case_13 x_a0, EoCases.__smtx_typeof.case_14 x_a0, EoCases.__smtx_typeof.case_15 x_a0, EoCases.__smtx_typeof.case_16 x_a0, EoCases.__smtx_typeof.case_17 x_a0, EoCases.__smtx_typeof.case_18 x_a0, EoCases.__smtx_typeof.case_19 x_a0, EoCases.__smtx_typeof.case_20 x_a0, EoCases.__smtx_typeof.case_21 x_a0, EoCases.__smtx_typeof.case_22 x_a0, EoCases.__smtx_typeof.case_23 x_a0, EoCases.__smtx_typeof.case_24 x_a0, EoCases.__smtx_typeof.case_25 x_a0, EoCases.__smtx_typeof.case_26 x_a0, EoCases.__smtx_typeof.case_27 x_a0, EoCases.__smtx_typeof.case_28 x_a0, EoCases.__smtx_typeof.case_29 x_a0, EoCases.__smtx_typeof.case_30 x_a0, EoCases.__smtx_typeof.case_31 x_a0, EoCases.__smtx_typeof.case_32 x_a0, EoCases.__smtx_typeof.case_33 x_a0, EoCases.__smtx_typeof.case_34 x_a0, EoCases.__smtx_typeof.case_35 x_a0, EoCases.__smtx_typeof.case_36 x_a0, EoCases.__smtx_typeof.case_37 x_a0, EoCases.__smtx_typeof.case_38 x_a0, EoCases.__smtx_typeof.case_39 x_a0, EoCases.__smtx_typeof.case_40 x_a0, EoCases.__smtx_typeof.case_41 x_a0, EoCases.__smtx_typeof.case_42 x_a0, EoCases.__smtx_typeof.case_43 x_a0, EoCases.__smtx_typeof.case_44 x_a0, EoCases.__smtx_typeof.case_45 x_a0, EoCases.__smtx_typeof.case_46 x_a0, EoCases.__smtx_typeof.case_47 x_a0, EoCases.__smtx_typeof.case_48 x_a0, EoCases.__smtx_typeof.case_49 x_a0, EoCases.__smtx_typeof.case_50 x_a0, EoCases.__smtx_typeof.case_51 x_a0, EoCases.__smtx_typeof.case_52 x_a0, EoCases.__smtx_typeof.case_53 x_a0, EoCases.__smtx_typeof.case_54 x_a0, EoCases.__smtx_typeof.case_55 x_a0, EoCases.__smtx_typeof.case_56 x_a0, EoCases.__smtx_typeof.case_57 x_a0, EoCases.__smtx_typeof.case_58 x_a0, EoCases.__smtx_typeof.case_59 x_a0, EoCases.__smtx_typeof.case_60 x_a0, EoCases.__smtx_typeof.case_61 x_a0, EoCases.__smtx_typeof.case_62 x_a0, EoCases.__smtx_typeof.case_63 x_a0] ++ [EoCases.__smtx_typeof.case_64 x_a0, EoCases.__smtx_typeof.case_65 x_a0, EoCases.__smtx_typeof.case_66 x_a0, EoCases.__smtx_typeof.case_67 x_a0, EoCases.__smtx_typeof.case_68 x_a0, EoCases.__smtx_typeof.case_69 x_a0, EoCases.__smtx_typeof.case_70 x_a0, EoCases.__smtx_typeof.case_71 x_a0, EoCases.__smtx_typeof.case_72 x_a0, EoCases.__smtx_typeof.case_73 x_a0, EoCases.__smtx_typeof.case_74 x_a0, EoCases.__smtx_typeof.case_75 x_a0, EoCases.__smtx_typeof.case_76 x_a0, EoCases.__smtx_typeof.case_77 x_a0, EoCases.__smtx_typeof.case_78 x_a0, EoCases.__smtx_typeof.case_79 x_a0, EoCases.__smtx_typeof.case_80 x_a0, EoCases.__smtx_typeof.case_81 x_a0, EoCases.__smtx_typeof.case_82 x_a0, EoCases.__smtx_typeof.case_83 x_a0, EoCases.__smtx_typeof.case_84 x_a0, EoCases.__smtx_typeof.case_85 x_a0, EoCases.__smtx_typeof.case_86 x_a0, EoCases.__smtx_typeof.case_87 x_a0, EoCases.__smtx_typeof.case_88 x_a0, EoCases.__smtx_typeof.case_89 x_a0, EoCases.__smtx_typeof.case_90 x_a0, EoCases.__smtx_typeof.case_91 x_a0, EoCases.__smtx_typeof.case_92 x_a0, EoCases.__smtx_typeof.case_93 x_a0, EoCases.__smtx_typeof.case_94 x_a0, EoCases.__smtx_typeof.case_95 x_a0, EoCases.__smtx_typeof.case_96 x_a0, EoCases.__smtx_typeof.case_97 x_a0, EoCases.__smtx_typeof.case_98 x_a0, EoCases.__smtx_typeof.case_99 x_a0, EoCases.__smtx_typeof.case_100 x_a0, EoCases.__smtx_typeof.case_101 x_a0, EoCases.__smtx_typeof.case_102 x_a0, EoCases.__smtx_typeof.case_103 x_a0, EoCases.__smtx_typeof.case_104 x_a0, EoCases.__smtx_typeof.case_105 x_a0, EoCases.__smtx_typeof.case_106 x_a0, EoCases.__smtx_typeof.case_107 x_a0, EoCases.__smtx_typeof.case_108 x_a0, EoCases.__smtx_typeof.case_109 x_a0, EoCases.__smtx_typeof.case_110 x_a0, EoCases.__smtx_typeof.case_111 x_a0, EoCases.__smtx_typeof.case_112 x_a0, EoCases.__smtx_typeof.case_113 x_a0, EoCases.__smtx_typeof.case_114 x_a0, EoCases.__smtx_typeof.case_115 x_a0, EoCases.__smtx_typeof.case_116 x_a0, EoCases.__smtx_typeof.case_117 x_a0, EoCases.__smtx_typeof.case_118 x_a0, EoCases.__smtx_typeof.case_119 x_a0, EoCases.__smtx_typeof.case_120 x_a0, EoCases.__smtx_typeof.case_121 x_a0, EoCases.__smtx_typeof.case_122 x_a0, EoCases.__smtx_typeof.case_123 x_a0, EoCases.__smtx_typeof.case_124 x_a0, EoCases.__smtx_typeof.case_125 x_a0, EoCases.__smtx_typeof.case_126 x_a0, EoCases.__smtx_typeof.case_127 x_a0] ++ [EoCases.__smtx_typeof.case_128 x_a0, EoCases.__smtx_typeof.case_129 x_a0, EoCases.__smtx_typeof.case_130 x_a0, EoCases.__smtx_typeof.case_131 x_a0, EoCases.__smtx_typeof.case_132 x_a0, EoCases.__smtx_typeof.case_133 x_a0, EoCases.__smtx_typeof.case_134 x_a0, EoCases.__smtx_typeof.case_135 x_a0, EoCases.__smtx_typeof.case_136 x_a0, EoCases.__smtx_typeof.case_137 x_a0, EoCases.__smtx_typeof.case_138 x_a0, EoCases.__smtx_typeof.case_139 x_a0, EoCases.__smtx_typeof.case_140 x_a0, EoCases.__smtx_typeof.case_141 x_a0, EoCases.__smtx_typeof.case_142 x_a0, EoCases.__smtx_typeof.case_143 x_a0, EoCases.__smtx_typeof.case_144 x_a0, EoCases.__smtx_typeof.case_145 x_a0, EoCases.__smtx_typeof.case_146 x_a0, EoCases.__smtx_typeof.case_147 x_a0] from rfl)
    otherwise ⟨hl_64, hl_65, hl_66, hl_67, hl_68, hl_69, hl_70, hl_71, hl_72, hl_73, hl_74, hl_75, hl_76, hl_77, hl_78, hl_79, hl_80, hl_81, hl_82, hl_83, hl_84, hl_85, hl_86, hl_87, hl_88, hl_89, hl_90, hl_91, hl_92, hl_93, hl_94, hl_95, hl_96, hl_97, hl_98, hl_99, hl_100, hl_101, hl_102, hl_103, hl_104, hl_105, hl_106, hl_107, hl_108, hl_109, hl_110, hl_111, hl_112, hl_113, hl_114, hl_115, hl_116, hl_117, hl_118, hl_119, hl_120, hl_121, hl_122, hl_123, hl_124, hl_125, hl_126, hl_127⟩ using hl_0 hl_1 hl_2 hl_3 hl_4 hl_5 hl_6 hl_7 hl_8 hl_9 hl_10 hl_11 hl_12 hl_13 hl_14 hl_15 hl_16 hl_17 hl_18 hl_19 hl_20 hl_21 hl_22 hl_23 hl_24 hl_25 hl_26 hl_27 hl_28 hl_29 hl_30 hl_31 hl_32 hl_33 hl_34 hl_35 hl_36 hl_37 hl_38 hl_39 hl_40 hl_41 hl_42 hl_43 hl_44 hl_45 hl_46 hl_47 hl_48 hl_49 hl_50 hl_51 hl_52 hl_53 hl_54 hl_55 hl_56 hl_57 hl_58 hl_59 hl_60 hl_61 hl_62 hl_63
  body_group_round_step with cases_2_2_eo__24smtx_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0 hbud
    split (show [EoCases.__smtx_typeof.case_0 x_a0, EoCases.__smtx_typeof.case_1 x_a0, EoCases.__smtx_typeof.case_2 x_a0, EoCases.__smtx_typeof.case_3 x_a0, EoCases.__smtx_typeof.case_4 x_a0, EoCases.__smtx_typeof.case_5 x_a0, EoCases.__smtx_typeof.case_6 x_a0, EoCases.__smtx_typeof.case_7 x_a0, EoCases.__smtx_typeof.case_8 x_a0, EoCases.__smtx_typeof.case_9 x_a0, EoCases.__smtx_typeof.case_10 x_a0, EoCases.__smtx_typeof.case_11 x_a0, EoCases.__smtx_typeof.case_12 x_a0, EoCases.__smtx_typeof.case_13 x_a0, EoCases.__smtx_typeof.case_14 x_a0, EoCases.__smtx_typeof.case_15 x_a0, EoCases.__smtx_typeof.case_16 x_a0, EoCases.__smtx_typeof.case_17 x_a0, EoCases.__smtx_typeof.case_18 x_a0, EoCases.__smtx_typeof.case_19 x_a0, EoCases.__smtx_typeof.case_20 x_a0, EoCases.__smtx_typeof.case_21 x_a0, EoCases.__smtx_typeof.case_22 x_a0, EoCases.__smtx_typeof.case_23 x_a0, EoCases.__smtx_typeof.case_24 x_a0, EoCases.__smtx_typeof.case_25 x_a0, EoCases.__smtx_typeof.case_26 x_a0, EoCases.__smtx_typeof.case_27 x_a0, EoCases.__smtx_typeof.case_28 x_a0, EoCases.__smtx_typeof.case_29 x_a0, EoCases.__smtx_typeof.case_30 x_a0, EoCases.__smtx_typeof.case_31 x_a0, EoCases.__smtx_typeof.case_32 x_a0, EoCases.__smtx_typeof.case_33 x_a0, EoCases.__smtx_typeof.case_34 x_a0, EoCases.__smtx_typeof.case_35 x_a0, EoCases.__smtx_typeof.case_36 x_a0, EoCases.__smtx_typeof.case_37 x_a0, EoCases.__smtx_typeof.case_38 x_a0, EoCases.__smtx_typeof.case_39 x_a0, EoCases.__smtx_typeof.case_40 x_a0, EoCases.__smtx_typeof.case_41 x_a0, EoCases.__smtx_typeof.case_42 x_a0, EoCases.__smtx_typeof.case_43 x_a0, EoCases.__smtx_typeof.case_44 x_a0, EoCases.__smtx_typeof.case_45 x_a0, EoCases.__smtx_typeof.case_46 x_a0, EoCases.__smtx_typeof.case_47 x_a0, EoCases.__smtx_typeof.case_48 x_a0, EoCases.__smtx_typeof.case_49 x_a0, EoCases.__smtx_typeof.case_50 x_a0, EoCases.__smtx_typeof.case_51 x_a0, EoCases.__smtx_typeof.case_52 x_a0, EoCases.__smtx_typeof.case_53 x_a0, EoCases.__smtx_typeof.case_54 x_a0, EoCases.__smtx_typeof.case_55 x_a0, EoCases.__smtx_typeof.case_56 x_a0, EoCases.__smtx_typeof.case_57 x_a0, EoCases.__smtx_typeof.case_58 x_a0, EoCases.__smtx_typeof.case_59 x_a0, EoCases.__smtx_typeof.case_60 x_a0, EoCases.__smtx_typeof.case_61 x_a0, EoCases.__smtx_typeof.case_62 x_a0, EoCases.__smtx_typeof.case_63 x_a0, EoCases.__smtx_typeof.case_64 x_a0, EoCases.__smtx_typeof.case_65 x_a0, EoCases.__smtx_typeof.case_66 x_a0, EoCases.__smtx_typeof.case_67 x_a0, EoCases.__smtx_typeof.case_68 x_a0, EoCases.__smtx_typeof.case_69 x_a0, EoCases.__smtx_typeof.case_70 x_a0, EoCases.__smtx_typeof.case_71 x_a0, EoCases.__smtx_typeof.case_72 x_a0, EoCases.__smtx_typeof.case_73 x_a0, EoCases.__smtx_typeof.case_74 x_a0, EoCases.__smtx_typeof.case_75 x_a0, EoCases.__smtx_typeof.case_76 x_a0, EoCases.__smtx_typeof.case_77 x_a0, EoCases.__smtx_typeof.case_78 x_a0, EoCases.__smtx_typeof.case_79 x_a0, EoCases.__smtx_typeof.case_80 x_a0, EoCases.__smtx_typeof.case_81 x_a0, EoCases.__smtx_typeof.case_82 x_a0, EoCases.__smtx_typeof.case_83 x_a0, EoCases.__smtx_typeof.case_84 x_a0, EoCases.__smtx_typeof.case_85 x_a0, EoCases.__smtx_typeof.case_86 x_a0, EoCases.__smtx_typeof.case_87 x_a0, EoCases.__smtx_typeof.case_88 x_a0, EoCases.__smtx_typeof.case_89 x_a0, EoCases.__smtx_typeof.case_90 x_a0, EoCases.__smtx_typeof.case_91 x_a0, EoCases.__smtx_typeof.case_92 x_a0, EoCases.__smtx_typeof.case_93 x_a0, EoCases.__smtx_typeof.case_94 x_a0, EoCases.__smtx_typeof.case_95 x_a0, EoCases.__smtx_typeof.case_96 x_a0, EoCases.__smtx_typeof.case_97 x_a0, EoCases.__smtx_typeof.case_98 x_a0, EoCases.__smtx_typeof.case_99 x_a0, EoCases.__smtx_typeof.case_100 x_a0, EoCases.__smtx_typeof.case_101 x_a0, EoCases.__smtx_typeof.case_102 x_a0, EoCases.__smtx_typeof.case_103 x_a0, EoCases.__smtx_typeof.case_104 x_a0, EoCases.__smtx_typeof.case_105 x_a0, EoCases.__smtx_typeof.case_106 x_a0, EoCases.__smtx_typeof.case_107 x_a0, EoCases.__smtx_typeof.case_108 x_a0, EoCases.__smtx_typeof.case_109 x_a0, EoCases.__smtx_typeof.case_110 x_a0, EoCases.__smtx_typeof.case_111 x_a0, EoCases.__smtx_typeof.case_112 x_a0, EoCases.__smtx_typeof.case_113 x_a0, EoCases.__smtx_typeof.case_114 x_a0, EoCases.__smtx_typeof.case_115 x_a0, EoCases.__smtx_typeof.case_116 x_a0, EoCases.__smtx_typeof.case_117 x_a0, EoCases.__smtx_typeof.case_118 x_a0, EoCases.__smtx_typeof.case_119 x_a0, EoCases.__smtx_typeof.case_120 x_a0, EoCases.__smtx_typeof.case_121 x_a0, EoCases.__smtx_typeof.case_122 x_a0, EoCases.__smtx_typeof.case_123 x_a0, EoCases.__smtx_typeof.case_124 x_a0, EoCases.__smtx_typeof.case_125 x_a0, EoCases.__smtx_typeof.case_126 x_a0, EoCases.__smtx_typeof.case_127 x_a0, EoCases.__smtx_typeof.case_128 x_a0, EoCases.__smtx_typeof.case_129 x_a0, EoCases.__smtx_typeof.case_130 x_a0, EoCases.__smtx_typeof.case_131 x_a0, EoCases.__smtx_typeof.case_132 x_a0, EoCases.__smtx_typeof.case_133 x_a0, EoCases.__smtx_typeof.case_134 x_a0, EoCases.__smtx_typeof.case_135 x_a0, EoCases.__smtx_typeof.case_136 x_a0, EoCases.__smtx_typeof.case_137 x_a0, EoCases.__smtx_typeof.case_138 x_a0, EoCases.__smtx_typeof.case_139 x_a0, EoCases.__smtx_typeof.case_140 x_a0, EoCases.__smtx_typeof.case_141 x_a0, EoCases.__smtx_typeof.case_142 x_a0, EoCases.__smtx_typeof.case_143 x_a0, EoCases.__smtx_typeof.case_144 x_a0, EoCases.__smtx_typeof.case_145 x_a0, EoCases.__smtx_typeof.case_146 x_a0, EoCases.__smtx_typeof.case_147 x_a0] = [EoCases.__smtx_typeof.case_0 x_a0, EoCases.__smtx_typeof.case_1 x_a0, EoCases.__smtx_typeof.case_2 x_a0, EoCases.__smtx_typeof.case_3 x_a0, EoCases.__smtx_typeof.case_4 x_a0, EoCases.__smtx_typeof.case_5 x_a0, EoCases.__smtx_typeof.case_6 x_a0, EoCases.__smtx_typeof.case_7 x_a0, EoCases.__smtx_typeof.case_8 x_a0, EoCases.__smtx_typeof.case_9 x_a0, EoCases.__smtx_typeof.case_10 x_a0, EoCases.__smtx_typeof.case_11 x_a0, EoCases.__smtx_typeof.case_12 x_a0, EoCases.__smtx_typeof.case_13 x_a0, EoCases.__smtx_typeof.case_14 x_a0, EoCases.__smtx_typeof.case_15 x_a0, EoCases.__smtx_typeof.case_16 x_a0, EoCases.__smtx_typeof.case_17 x_a0, EoCases.__smtx_typeof.case_18 x_a0, EoCases.__smtx_typeof.case_19 x_a0, EoCases.__smtx_typeof.case_20 x_a0, EoCases.__smtx_typeof.case_21 x_a0, EoCases.__smtx_typeof.case_22 x_a0, EoCases.__smtx_typeof.case_23 x_a0, EoCases.__smtx_typeof.case_24 x_a0, EoCases.__smtx_typeof.case_25 x_a0, EoCases.__smtx_typeof.case_26 x_a0, EoCases.__smtx_typeof.case_27 x_a0, EoCases.__smtx_typeof.case_28 x_a0, EoCases.__smtx_typeof.case_29 x_a0, EoCases.__smtx_typeof.case_30 x_a0, EoCases.__smtx_typeof.case_31 x_a0, EoCases.__smtx_typeof.case_32 x_a0, EoCases.__smtx_typeof.case_33 x_a0, EoCases.__smtx_typeof.case_34 x_a0, EoCases.__smtx_typeof.case_35 x_a0, EoCases.__smtx_typeof.case_36 x_a0, EoCases.__smtx_typeof.case_37 x_a0, EoCases.__smtx_typeof.case_38 x_a0, EoCases.__smtx_typeof.case_39 x_a0, EoCases.__smtx_typeof.case_40 x_a0, EoCases.__smtx_typeof.case_41 x_a0, EoCases.__smtx_typeof.case_42 x_a0, EoCases.__smtx_typeof.case_43 x_a0, EoCases.__smtx_typeof.case_44 x_a0, EoCases.__smtx_typeof.case_45 x_a0, EoCases.__smtx_typeof.case_46 x_a0, EoCases.__smtx_typeof.case_47 x_a0, EoCases.__smtx_typeof.case_48 x_a0, EoCases.__smtx_typeof.case_49 x_a0, EoCases.__smtx_typeof.case_50 x_a0, EoCases.__smtx_typeof.case_51 x_a0, EoCases.__smtx_typeof.case_52 x_a0, EoCases.__smtx_typeof.case_53 x_a0, EoCases.__smtx_typeof.case_54 x_a0, EoCases.__smtx_typeof.case_55 x_a0, EoCases.__smtx_typeof.case_56 x_a0, EoCases.__smtx_typeof.case_57 x_a0, EoCases.__smtx_typeof.case_58 x_a0, EoCases.__smtx_typeof.case_59 x_a0, EoCases.__smtx_typeof.case_60 x_a0, EoCases.__smtx_typeof.case_61 x_a0, EoCases.__smtx_typeof.case_62 x_a0, EoCases.__smtx_typeof.case_63 x_a0, EoCases.__smtx_typeof.case_64 x_a0, EoCases.__smtx_typeof.case_65 x_a0, EoCases.__smtx_typeof.case_66 x_a0, EoCases.__smtx_typeof.case_67 x_a0, EoCases.__smtx_typeof.case_68 x_a0, EoCases.__smtx_typeof.case_69 x_a0, EoCases.__smtx_typeof.case_70 x_a0, EoCases.__smtx_typeof.case_71 x_a0, EoCases.__smtx_typeof.case_72 x_a0, EoCases.__smtx_typeof.case_73 x_a0, EoCases.__smtx_typeof.case_74 x_a0, EoCases.__smtx_typeof.case_75 x_a0, EoCases.__smtx_typeof.case_76 x_a0, EoCases.__smtx_typeof.case_77 x_a0, EoCases.__smtx_typeof.case_78 x_a0, EoCases.__smtx_typeof.case_79 x_a0, EoCases.__smtx_typeof.case_80 x_a0, EoCases.__smtx_typeof.case_81 x_a0, EoCases.__smtx_typeof.case_82 x_a0, EoCases.__smtx_typeof.case_83 x_a0, EoCases.__smtx_typeof.case_84 x_a0, EoCases.__smtx_typeof.case_85 x_a0, EoCases.__smtx_typeof.case_86 x_a0, EoCases.__smtx_typeof.case_87 x_a0, EoCases.__smtx_typeof.case_88 x_a0, EoCases.__smtx_typeof.case_89 x_a0, EoCases.__smtx_typeof.case_90 x_a0, EoCases.__smtx_typeof.case_91 x_a0, EoCases.__smtx_typeof.case_92 x_a0, EoCases.__smtx_typeof.case_93 x_a0, EoCases.__smtx_typeof.case_94 x_a0, EoCases.__smtx_typeof.case_95 x_a0, EoCases.__smtx_typeof.case_96 x_a0, EoCases.__smtx_typeof.case_97 x_a0, EoCases.__smtx_typeof.case_98 x_a0, EoCases.__smtx_typeof.case_99 x_a0, EoCases.__smtx_typeof.case_100 x_a0, EoCases.__smtx_typeof.case_101 x_a0, EoCases.__smtx_typeof.case_102 x_a0, EoCases.__smtx_typeof.case_103 x_a0, EoCases.__smtx_typeof.case_104 x_a0, EoCases.__smtx_typeof.case_105 x_a0, EoCases.__smtx_typeof.case_106 x_a0, EoCases.__smtx_typeof.case_107 x_a0, EoCases.__smtx_typeof.case_108 x_a0, EoCases.__smtx_typeof.case_109 x_a0, EoCases.__smtx_typeof.case_110 x_a0, EoCases.__smtx_typeof.case_111 x_a0, EoCases.__smtx_typeof.case_112 x_a0, EoCases.__smtx_typeof.case_113 x_a0, EoCases.__smtx_typeof.case_114 x_a0, EoCases.__smtx_typeof.case_115 x_a0, EoCases.__smtx_typeof.case_116 x_a0, EoCases.__smtx_typeof.case_117 x_a0, EoCases.__smtx_typeof.case_118 x_a0, EoCases.__smtx_typeof.case_119 x_a0, EoCases.__smtx_typeof.case_120 x_a0, EoCases.__smtx_typeof.case_121 x_a0, EoCases.__smtx_typeof.case_122 x_a0, EoCases.__smtx_typeof.case_123 x_a0, EoCases.__smtx_typeof.case_124 x_a0, EoCases.__smtx_typeof.case_125 x_a0, EoCases.__smtx_typeof.case_126 x_a0, EoCases.__smtx_typeof.case_127 x_a0] ++ [EoCases.__smtx_typeof.case_128 x_a0, EoCases.__smtx_typeof.case_129 x_a0, EoCases.__smtx_typeof.case_130 x_a0, EoCases.__smtx_typeof.case_131 x_a0, EoCases.__smtx_typeof.case_132 x_a0, EoCases.__smtx_typeof.case_133 x_a0, EoCases.__smtx_typeof.case_134 x_a0, EoCases.__smtx_typeof.case_135 x_a0, EoCases.__smtx_typeof.case_136 x_a0, EoCases.__smtx_typeof.case_137 x_a0, EoCases.__smtx_typeof.case_138 x_a0, EoCases.__smtx_typeof.case_139 x_a0, EoCases.__smtx_typeof.case_140 x_a0, EoCases.__smtx_typeof.case_141 x_a0, EoCases.__smtx_typeof.case_142 x_a0, EoCases.__smtx_typeof.case_143 x_a0, EoCases.__smtx_typeof.case_144 x_a0, EoCases.__smtx_typeof.case_145 x_a0, EoCases.__smtx_typeof.case_146 x_a0, EoCases.__smtx_typeof.case_147 x_a0] ++ [] from rfl)
    otherwise ⟨hl_128, hl_129, hl_130, hl_131, hl_132, hl_133, hl_134, hl_135, hl_136, hl_137, hl_138, hl_139, hl_140, hl_141, hl_142, hl_143, hl_144, hl_145, hl_146, hl_147⟩ using hl_0 hl_1 hl_2 hl_3 hl_4 hl_5 hl_6 hl_7 hl_8 hl_9 hl_10 hl_11 hl_12 hl_13 hl_14 hl_15 hl_16 hl_17 hl_18 hl_19 hl_20 hl_21 hl_22 hl_23 hl_24 hl_25 hl_26 hl_27 hl_28 hl_29 hl_30 hl_31 hl_32 hl_33 hl_34 hl_35 hl_36 hl_37 hl_38 hl_39 hl_40 hl_41 hl_42 hl_43 hl_44 hl_45 hl_46 hl_47 hl_48 hl_49 hl_50 hl_51 hl_52 hl_53 hl_54 hl_55 hl_56 hl_57 hl_58 hl_59 hl_60 hl_61 hl_62 hl_63 hl_64 hl_65 hl_66 hl_67 hl_68 hl_69 hl_70 hl_71 hl_72 hl_73 hl_74 hl_75 hl_76 hl_77 hl_78 hl_79 hl_80 hl_81 hl_82 hl_83 hl_84 hl_85 hl_86 hl_87 hl_88 hl_89 hl_90 hl_91 hl_92 hl_93 hl_94 hl_95 hl_96 hl_97 hl_98 hl_99 hl_100 hl_101 hl_102 hl_103 hl_104 hl_105 hl_106 hl_107 hl_108 hl_109 hl_110 hl_111 hl_112 hl_113 hl_114 hl_115 hl_116 hl_117 hl_118 hl_119 hl_120 hl_121 hl_122 hl_123 hl_124 hl_125 hl_126 hl_127
  round_stuck hinv4 hG using hl_0 hl_1 hl_2 hl_3 hl_4 hl_5 hl_6 hl_7 hl_8 hl_9 hl_10 hl_11 hl_12 hl_13 hl_14 hl_15 hl_16 hl_17 hl_18 hl_19 hl_20 hl_21 hl_22 hl_23 hl_24 hl_25 hl_26 hl_27 hl_28 hl_29 hl_30 hl_31 hl_32 hl_33 hl_34 hl_35 hl_36 hl_37 hl_38 hl_39 hl_40 hl_41 hl_42 hl_43 hl_44 hl_45 hl_46 hl_47 hl_48 hl_49 hl_50 hl_51 hl_52 hl_53 hl_54 hl_55 hl_56 hl_57 hl_58 hl_59 hl_60 hl_61 hl_62 hl_63 hl_64 hl_65 hl_66 hl_67 hl_68 hl_69 hl_70 hl_71 hl_72 hl_73 hl_74 hl_75 hl_76 hl_77 hl_78 hl_79 hl_80 hl_81 hl_82 hl_83 hl_84 hl_85 hl_86 hl_87 hl_88 hl_89 hl_90 hl_91 hl_92 hl_93 hl_94 hl_95 hl_96 hl_97 hl_98 hl_99 hl_100 hl_101 hl_102 hl_103 hl_104 hl_105 hl_106 hl_107 hl_108 hl_109 hl_110 hl_111 hl_112 hl_113 hl_114 hl_115 hl_116 hl_117 hl_118 hl_119 hl_120 hl_121 hl_122 hl_123 hl_124 hl_125 hl_126 hl_127 hl_128 hl_129 hl_130 hl_131 hl_132 hl_133 hl_134 hl_135 hl_136 hl_137 hl_138 hl_139 hl_140 hl_141 hl_142 hl_143 hl_144 hl_145 hl_146 hl_147 in EoCases.__smtx_typeof.case_0 EoCases.__smtx_typeof.case_1 EoCases.__smtx_typeof.case_2 EoCases.__smtx_typeof.case_3 EoCases.__smtx_typeof.case_4 EoCases.__smtx_typeof.case_5 EoCases.__smtx_typeof.case_6 EoCases.__smtx_typeof.case_7 EoCases.__smtx_typeof.case_8 EoCases.__smtx_typeof.case_9 EoCases.__smtx_typeof.case_10 EoCases.__smtx_typeof.case_11 EoCases.__smtx_typeof.case_12 EoCases.__smtx_typeof.case_13 EoCases.__smtx_typeof.case_14 EoCases.__smtx_typeof.case_15 EoCases.__smtx_typeof.case_16 EoCases.__smtx_typeof.case_17 EoCases.__smtx_typeof.case_18 EoCases.__smtx_typeof.case_19 EoCases.__smtx_typeof.case_20 EoCases.__smtx_typeof.case_21 EoCases.__smtx_typeof.case_22 EoCases.__smtx_typeof.case_23 EoCases.__smtx_typeof.case_24 EoCases.__smtx_typeof.case_25 EoCases.__smtx_typeof.case_26 EoCases.__smtx_typeof.case_27 EoCases.__smtx_typeof.case_28 EoCases.__smtx_typeof.case_29 EoCases.__smtx_typeof.case_30 EoCases.__smtx_typeof.case_31 EoCases.__smtx_typeof.case_32 EoCases.__smtx_typeof.case_33 EoCases.__smtx_typeof.case_34 EoCases.__smtx_typeof.case_35 EoCases.__smtx_typeof.case_36 EoCases.__smtx_typeof.case_37 EoCases.__smtx_typeof.case_38 EoCases.__smtx_typeof.case_39 EoCases.__smtx_typeof.case_40 EoCases.__smtx_typeof.case_41 EoCases.__smtx_typeof.case_42 EoCases.__smtx_typeof.case_43 EoCases.__smtx_typeof.case_44 EoCases.__smtx_typeof.case_45 EoCases.__smtx_typeof.case_46 EoCases.__smtx_typeof.case_47 EoCases.__smtx_typeof.case_48 EoCases.__smtx_typeof.case_49 EoCases.__smtx_typeof.case_50 EoCases.__smtx_typeof.case_51 EoCases.__smtx_typeof.case_52 EoCases.__smtx_typeof.case_53 EoCases.__smtx_typeof.case_54 EoCases.__smtx_typeof.case_55 EoCases.__smtx_typeof.case_56 EoCases.__smtx_typeof.case_57 EoCases.__smtx_typeof.case_58 EoCases.__smtx_typeof.case_59 EoCases.__smtx_typeof.case_60 EoCases.__smtx_typeof.case_61 EoCases.__smtx_typeof.case_62 EoCases.__smtx_typeof.case_63 EoCases.__smtx_typeof.case_64 EoCases.__smtx_typeof.case_65 EoCases.__smtx_typeof.case_66 EoCases.__smtx_typeof.case_67 EoCases.__smtx_typeof.case_68 EoCases.__smtx_typeof.case_69 EoCases.__smtx_typeof.case_70 EoCases.__smtx_typeof.case_71 EoCases.__smtx_typeof.case_72 EoCases.__smtx_typeof.case_73 EoCases.__smtx_typeof.case_74 EoCases.__smtx_typeof.case_75 EoCases.__smtx_typeof.case_76 EoCases.__smtx_typeof.case_77 EoCases.__smtx_typeof.case_78 EoCases.__smtx_typeof.case_79 EoCases.__smtx_typeof.case_80 EoCases.__smtx_typeof.case_81 EoCases.__smtx_typeof.case_82 EoCases.__smtx_typeof.case_83 EoCases.__smtx_typeof.case_84 EoCases.__smtx_typeof.case_85 EoCases.__smtx_typeof.case_86 EoCases.__smtx_typeof.case_87 EoCases.__smtx_typeof.case_88 EoCases.__smtx_typeof.case_89 EoCases.__smtx_typeof.case_90 EoCases.__smtx_typeof.case_91 EoCases.__smtx_typeof.case_92 EoCases.__smtx_typeof.case_93 EoCases.__smtx_typeof.case_94 EoCases.__smtx_typeof.case_95 EoCases.__smtx_typeof.case_96 EoCases.__smtx_typeof.case_97 EoCases.__smtx_typeof.case_98 EoCases.__smtx_typeof.case_99 EoCases.__smtx_typeof.case_100 EoCases.__smtx_typeof.case_101 EoCases.__smtx_typeof.case_102 EoCases.__smtx_typeof.case_103 EoCases.__smtx_typeof.case_104 EoCases.__smtx_typeof.case_105 EoCases.__smtx_typeof.case_106 EoCases.__smtx_typeof.case_107 EoCases.__smtx_typeof.case_108 EoCases.__smtx_typeof.case_109 EoCases.__smtx_typeof.case_110 EoCases.__smtx_typeof.case_111 EoCases.__smtx_typeof.case_112 EoCases.__smtx_typeof.case_113 EoCases.__smtx_typeof.case_114 EoCases.__smtx_typeof.case_115 EoCases.__smtx_typeof.case_116 EoCases.__smtx_typeof.case_117 EoCases.__smtx_typeof.case_118 EoCases.__smtx_typeof.case_119 EoCases.__smtx_typeof.case_120 EoCases.__smtx_typeof.case_121 EoCases.__smtx_typeof.case_122 EoCases.__smtx_typeof.case_123 EoCases.__smtx_typeof.case_124 EoCases.__smtx_typeof.case_125 EoCases.__smtx_typeof.case_126 EoCases.__smtx_typeof.case_127 EoCases.__smtx_typeof.case_128 EoCases.__smtx_typeof.case_129 EoCases.__smtx_typeof.case_130 EoCases.__smtx_typeof.case_131 EoCases.__smtx_typeof.case_132 EoCases.__smtx_typeof.case_133 EoCases.__smtx_typeof.case_134 EoCases.__smtx_typeof.case_135 EoCases.__smtx_typeof.case_136 EoCases.__smtx_typeof.case_137 EoCases.__smtx_typeof.case_138 EoCases.__smtx_typeof.case_139 EoCases.__smtx_typeof.case_140 EoCases.__smtx_typeof.case_141 EoCases.__smtx_typeof.case_142 EoCases.__smtx_typeof.case_143 EoCases.__smtx_typeof.case_144 EoCases.__smtx_typeof.case_145 EoCases.__smtx_typeof.case_146 EoCases.__smtx_typeof.case_147 splitting x_a0

theorem body_eo__24smtx_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_typeof x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  refine (?_ : ∀ (k : Nat) (a0 : Term) (s : Store) (x_a0 : _), s.budget ≤ k → s.Inv → s.remaining ≤ n →
      Represents.rep s a0 x_a0 →
      body_eo__24smtx_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_typeof x_a0)
      | core.result.Result.Err _ => True ⦄div) s.budget a0 s x_a0 le_rfl hinv hrem h_a0
  intro k
  refine Nat.strong_induction_on k ?_
  intro k ihl a0 s x_a0 hk hinv hrem h_a0
  unfold body_eo__24smtx_5ftypeof body_eo__24smtx_5ftypeof_loop
  step with step_eo__24smtx_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0 as ⟨r, s1, hinv1, hg1, hr⟩
  cases r with
  | Err e => simp only [WP.dspec_ok, WP.uncurry'_pair]; exact ⟨hinv1, hg1, trivial⟩
  | Ok nx =>
    cases nx with
    | Done value =>
      simp only [WP.dspec_ok, WP.uncurry'_pair]
      exact ⟨hinv1, hg1, hr⟩
    | Again next =>
      obtain ⟨hlt, u0, y0, hnext, hrep0, heq⟩ := hr
      simp only
      have hlen : next.length = 1 := by simp [Array.length, hnext]
      step as ⟨b0, hb0⟩
      obtain rfl : b0 = u0 := by simp [hb0, hnext]
      have hrec := ihl s1.budget (by omega) b0 s1 y0 le_rfl hinv1 (hg1.rem hrem)  hrep0
      unfold body_eo__24smtx_5ftypeof at hrec
      apply WP.dspec_mono hrec
      loop_close hg1 heq

theorem eo__24smtx_5ftypeof_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24smtx_5ftypeof.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24smtx_5ftypeof
  apply WP.dspec_mono (Store.framed_type_cached s hinv hrem h64 cache.TypeCacheKind.Smt a0
    (fun s1 => body_eo__24smtx_5ftypeof s1 a0) (fun s' t => Represents.rep s' t (__smtx_typeof x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, y0, hargs, hb0, hr⟩ := ProgramSem.of_4294967297 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_4294967297 ⟨a0, x_a0, rfl, Rep.mono hpre h_a0, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24smtx_5ftypeof_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

end pathos_compiled_checker
