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
  store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s e_v2 (by rw [he_v2]; exact empty_args) hinv h64 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying dropping h_a0 h_v1 he_v2 e_v2 v1
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
  store_step with CtorSpec.eo__24emb_5ftsm_2eInt.construct s e_v2 (by rw [he_v2]; exact empty_args) hinv h64 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying dropping h_a0 h_v1 he_v2 e_v2 v1
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
  store_step with CtorSpec.eo__24emb_5ftsm_2eReal.construct s e_v2 (by rw [he_v2]; exact empty_args) hinv h64 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying dropping h_a0 h_v1 he_v2 e_v2 v1
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
  store_step with Store.native_spec_string_valid s e_v2 (by rw [he_v2]; rfl) h_v1 hinv h64 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying dropping h_a0 h_v1 he_v2 e_v2 v1
  rw [← Bridge.native_string_valid] at h_v2
  have h_ite_v6 := (show if_0_eo__24smtx_5ftypeof s1 v2 ⦃ r s' => s'.Inv ∧ s1.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_0_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s1
    rcases Store.boolean_value_native h_v2 with ⟨hx_3, hbv_3⟩ | ⟨hx_3, hbv_3⟩
    · ite_branch hbv_3
      step as ⟨e_v3, he_v3⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eChar.construct s1 e_v3 (by rw [he_v3]; exact empty_args) hinv1 h64 as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying dropping h_v2 he_v3 e_v3 v2
      step as ⟨e_v4, he_v4⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eSeq.construct s2 e_v4 (by rw [he_v4]; rfl) h_v3 hinv2 h64 as ⟨v4, s3, hinv3, h_v4⟩ growing hG carrying dropping h_v3 he_v4 e_v4 v3
      ite_done hinv3 hG with (native_ite_true_rep _ hx_3 h_v4)
    · ite_branch hbv_3
      step as ⟨e_v5, he_v5⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s1 e_v5 (by rw [he_v5]; exact empty_args) hinv1 h64 as ⟨v5, s2, hinv2, h_v5⟩ growing hG carrying dropping h_v2 he_v5 hinv1 e_v5 s1 v2
      ite_done hinv2 hG with (native_ite_false_rep _ hx_3 h_v5))
  store_step with h_ite_v6 as ⟨v6, s2, hinv2, h_v6⟩ growing hG carrying dropping h_ite_v6 h_v2 hinv1 s1 v2
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
  store_step with Store.raw_int_u32_spec s 0#u32 (0) (by scalar_tac) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v1 h_v2 dropping h_a0
  step as ⟨e_v4, he_v4⟩
  store_step with Store.native_spec_zleq s1 e_v4 (by rw [he_v4]; rfl) h_v3 h_v1 hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v1 h_v2 dropping h_v3 he_v4 hinv1 e_v4 s1 v3
  rw [← Bridge.native_zleq] at h_v4
  step as ⟨e_v5, he_v5⟩
  store_step with Store.native_spec_int_pow2 s2 e_v5 (by rw [he_v5]; rfl) h_v1 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_v1 h_v2 h_v4 dropping he_v5 hinv2 e_v5 s2
  rw [← Bridge.native_int_pow2] at h_v5
  step as ⟨e_v6, he_v6⟩
  store_step with Store.native_spec_mod_total s3 e_v6 (by rw [he_v6]; rfl) h_v2 h_v5 hinv3 h64 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_v1 h_v2 h_v4 dropping h_v5 he_v6 hinv3 e_v6 s3 v5
  rw [← Bridge.native_mod_total] at h_v6
  step as ⟨e_v7, he_v7⟩
  store_step with Store.native_spec_zeq s4 e_v7 (by rw [he_v7]; rfl) h_v2 h_v6 hinv4 h64 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_v1 h_v4 dropping h_v2 h_v6 he_v7 hinv4 e_v7 s4 v2 v6
  rw [← Bridge.native_zeq] at h_v7
  step as ⟨e_v8, he_v8⟩
  store_step with Store.native_spec_and s5 e_v8 (by rw [he_v8]; rfl) h_v4 h_v7 hinv5 h64 as ⟨v8, s6, hinv6, h_v8⟩ growing hG carrying h_v1 dropping h_v4 h_v7 he_v8 hinv5 e_v8 s5 v4 v7
  rw [← Bridge.native_and] at h_v8
  have h_ite_v12 := (show if_1_eo__24smtx_5ftypeof s6 v8 v1 ⦃ r s' => s'.Inv ∧ s6.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_1_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s6
    rcases Store.boolean_value_native h_v8 with ⟨hx_9, hbv_9⟩ | ⟨hx_9, hbv_9⟩
    · ite_branch hbv_9
      step as ⟨e_v9, he_v9⟩
      store_step with Store.native_spec_int_to_nat s6 e_v9 (by rw [he_v9]; rfl) h_v1 hinv6 h64 as ⟨v9, s7, hinv7, h_v9⟩ growing hG carrying dropping h_v1 h_v8 he_v9 e_v9 v1 v8
      rw [← Bridge.native_int_to_nat] at h_v9
      step as ⟨e_v10, he_v10⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eBitVec.construct s7 e_v10 (by rw [he_v10]; rfl) h_v9 hinv7 h64 as ⟨v10, s8, hinv8, h_v10⟩ growing hG carrying dropping h_v9 he_v10 e_v10 v9
      ite_done hinv8 hG with (native_ite_true_rep _ hx_9 h_v10)
    · ite_branch hbv_9
      step as ⟨e_v11, he_v11⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s6 e_v11 (by rw [he_v11]; exact empty_args) hinv6 h64 as ⟨v11, s7, hinv7, h_v11⟩ growing hG carrying dropping h_v1 h_v8 he_v11 hinv6 e_v11 s6 v1 v8
      ite_done hinv7 hG with (native_ite_false_rep _ hx_9 h_v11))
  store_step with h_ite_v12 as ⟨v12, s7, hinv7, h_v12⟩ growing hG carrying dropping h_ite_v12 h_v1 h_v8 hinv6 s6 v1 v8
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v4, s1, hinv1, h_v4⟩ growing hG carrying h_v2 h_v3 dropping h_a0 h_v1 v1
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v5, s2, hinv2, h_v5⟩ growing hG carrying h_v3 h_v4 dropping h_v2 hinv1 s1 v2
  store_step with ih.eo__24smtx_5ftypeof s2 v3 _ hinv2 h64 (hG.rem hrem) h_v3 as ⟨v6, s3, hinv3, h_v6⟩ growing hG carrying h_v4 h_v5 dropping h_v3 hinv2 s2 v3
  store_step with ih.eo__24smtx_5ftypeof_5fite s3 v4 v5 v6 _ _ _ hinv3 h64 (hG.rem hrem) h_v4 h_v5 h_v6 as ⟨v7, s4, hinv4, h_v7⟩ growing hG carrying dropping h_v4 h_v5 h_v6 hinv3 s3 v4 v5 v6
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying dropping h_a0 h_v1 v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s1 e_v3 (by rw [he_v3]; exact empty_args) hinv1 h64 as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying h_v2 dropping he_v3 hinv1 e_v3 s1
  step as ⟨e_v4, he_v4⟩
  store_step with Store.native_spec_Teq s2 e_v4 (by rw [he_v4]; rfl) h_v2 h_v3 hinv2 h64 as ⟨v4, s3, hinv3, h_v4⟩ growing hG carrying dropping h_v2 h_v3 he_v4 hinv2 e_v4 s2 v2 v3
  have h_ite_v7 := (show if_2_eo__24smtx_5ftypeof s3 v4 ⦃ r s' => s'.Inv ∧ s3.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_2_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s3
    rcases Store.boolean_value_native h_v4 with ⟨hx_5, hbv_5⟩ | ⟨hx_5, hbv_5⟩
    · ite_branch hbv_5
      step as ⟨e_v5, he_v5⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s3 e_v5 (by rw [he_v5]; exact empty_args) hinv3 h64 as ⟨v5, s4, hinv4, h_v5⟩ growing hG carrying dropping h_v4 he_v5 e_v5 v4
      ite_done hinv4 hG with (native_ite_true_rep _ hx_5 h_v5)
    · ite_branch hbv_5
      step as ⟨e_v6, he_v6⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s3 e_v6 (by rw [he_v6]; exact empty_args) hinv3 h64 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying dropping h_v4 he_v6 hinv3 e_v6 s3 v4
      ite_done hinv4 hG with (native_ite_false_rep _ hx_5 h_v6))
  store_step with h_ite_v7 as ⟨v7, s4, hinv4, h_v7⟩ growing hG carrying dropping h_ite_v7 h_v4 hinv3 s3 v4
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v2 dropping h_a0 h_v1 v1
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s1 e_v4 (by rw [he_v4]; exact empty_args) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v2 h_v3 dropping he_v4 hinv1 e_v4 s1
  step as ⟨e_v5, he_v5⟩
  store_step with Store.native_spec_Teq s2 e_v5 (by rw [he_v5]; rfl) h_v3 h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_v2 dropping h_v3 h_v4 he_v5 hinv2 e_v5 s2 v3 v4
  have h_ite_v13 := (show if_4_eo__24smtx_5ftypeof s3 v5 v2 ⦃ r s' => s'.Inv ∧ s3.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_4_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s3
    rcases Store.boolean_value_native h_v5 with ⟨hx_6, hbv_6⟩ | ⟨hx_6, hbv_6⟩
    · ite_branch hbv_6
      store_step with ih.eo__24smtx_5ftypeof s3 v2 _ hinv3 h64 (hG.rem hrem) h_v2 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying dropping h_v2 h_v5 v2 v5
      step as ⟨e_v7, he_v7⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s4 e_v7 (by rw [he_v7]; exact empty_args) hinv4 h64 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_v6 dropping he_v7 e_v7
      step as ⟨e_v8, he_v8⟩
      store_step with Store.native_spec_Teq s5 e_v8 (by rw [he_v8]; rfl) h_v6 h_v7 hinv5 h64 as ⟨v8, s6, hinv6, h_v8⟩ growing hG carrying dropping h_v6 h_v7 he_v8 hinv5 e_v8 s5 v6 v7
      have h_ite_v11 := (show if_3_eo__24smtx_5ftypeof s6 v8 ⦃ r s' => s'.Inv ∧ s6.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_3_eo__24smtx_5ftypeof
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s6
        rcases Store.boolean_value_native h_v8 with ⟨hx_9, hbv_9⟩ | ⟨hx_9, hbv_9⟩
        · ite_branch hbv_9
          step as ⟨e_v9, he_v9⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s6 e_v9 (by rw [he_v9]; exact empty_args) hinv6 h64 as ⟨v9, s7, hinv7, h_v9⟩ growing hG carrying dropping h_v8 he_v9 e_v9 v8
          ite_done hinv7 hG with (native_ite_true_rep _ hx_9 h_v9)
        · ite_branch hbv_9
          step as ⟨e_v10, he_v10⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s6 e_v10 (by rw [he_v10]; exact empty_args) hinv6 h64 as ⟨v10, s7, hinv7, h_v10⟩ growing hG carrying dropping h_v8 he_v10 hinv6 e_v10 s6 v8
          ite_done hinv7 hG with (native_ite_false_rep _ hx_9 h_v10))
      store_step with h_ite_v11 as ⟨v11, s7, hinv7, h_v11⟩ growing hG carrying dropping h_ite_v11 h_v8 hinv6 s6 v8
      ite_done hinv7 hG with (native_ite_true_rep _ hx_6 h_v11)
    · ite_branch hbv_6
      step as ⟨e_v12, he_v12⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s3 e_v12 (by rw [he_v12]; exact empty_args) hinv3 h64 as ⟨v12, s4, hinv4, h_v12⟩ growing hG carrying dropping h_v2 h_v5 he_v12 hinv3 e_v12 s3 v2 v5
      ite_done hinv4 hG with (native_ite_false_rep _ hx_6 h_v12))
  store_step with h_ite_v13 as ⟨v13, s4, hinv4, h_v13⟩ growing hG carrying dropping h_ite_v13 h_v2 h_v5 hinv3 s3 v2 v5
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v2 dropping h_a0 h_v1 v1
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s1 e_v4 (by rw [he_v4]; exact empty_args) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v2 h_v3 dropping he_v4 hinv1 e_v4 s1
  step as ⟨e_v5, he_v5⟩
  store_step with Store.native_spec_Teq s2 e_v5 (by rw [he_v5]; rfl) h_v3 h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_v2 dropping h_v3 h_v4 he_v5 hinv2 e_v5 s2 v3 v4
  have h_ite_v13 := (show if_6_eo__24smtx_5ftypeof s3 v5 v2 ⦃ r s' => s'.Inv ∧ s3.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_6_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s3
    rcases Store.boolean_value_native h_v5 with ⟨hx_6, hbv_6⟩ | ⟨hx_6, hbv_6⟩
    · ite_branch hbv_6
      store_step with ih.eo__24smtx_5ftypeof s3 v2 _ hinv3 h64 (hG.rem hrem) h_v2 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying dropping h_v2 h_v5 v2 v5
      step as ⟨e_v7, he_v7⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s4 e_v7 (by rw [he_v7]; exact empty_args) hinv4 h64 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_v6 dropping he_v7 e_v7
      step as ⟨e_v8, he_v8⟩
      store_step with Store.native_spec_Teq s5 e_v8 (by rw [he_v8]; rfl) h_v6 h_v7 hinv5 h64 as ⟨v8, s6, hinv6, h_v8⟩ growing hG carrying dropping h_v6 h_v7 he_v8 hinv5 e_v8 s5 v6 v7
      have h_ite_v11 := (show if_5_eo__24smtx_5ftypeof s6 v8 ⦃ r s' => s'.Inv ∧ s6.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_5_eo__24smtx_5ftypeof
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s6
        rcases Store.boolean_value_native h_v8 with ⟨hx_9, hbv_9⟩ | ⟨hx_9, hbv_9⟩
        · ite_branch hbv_9
          step as ⟨e_v9, he_v9⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s6 e_v9 (by rw [he_v9]; exact empty_args) hinv6 h64 as ⟨v9, s7, hinv7, h_v9⟩ growing hG carrying dropping h_v8 he_v9 e_v9 v8
          ite_done hinv7 hG with (native_ite_true_rep _ hx_9 h_v9)
        · ite_branch hbv_9
          step as ⟨e_v10, he_v10⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s6 e_v10 (by rw [he_v10]; exact empty_args) hinv6 h64 as ⟨v10, s7, hinv7, h_v10⟩ growing hG carrying dropping h_v8 he_v10 hinv6 e_v10 s6 v8
          ite_done hinv7 hG with (native_ite_false_rep _ hx_9 h_v10))
      store_step with h_ite_v11 as ⟨v11, s7, hinv7, h_v11⟩ growing hG carrying dropping h_ite_v11 h_v8 hinv6 s6 v8
      ite_done hinv7 hG with (native_ite_true_rep _ hx_6 h_v11)
    · ite_branch hbv_6
      step as ⟨e_v12, he_v12⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s3 e_v12 (by rw [he_v12]; exact empty_args) hinv3 h64 as ⟨v12, s4, hinv4, h_v12⟩ growing hG carrying dropping h_v2 h_v5 he_v12 hinv3 e_v12 s3 v2 v5
      ite_done hinv4 hG with (native_ite_false_rep _ hx_6 h_v12))
  store_step with h_ite_v13 as ⟨v13, s4, hinv4, h_v13⟩ growing hG carrying dropping h_ite_v13 h_v2 h_v5 hinv3 s3 v2 v5
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v2 dropping h_a0 h_v1 v1
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s1 e_v4 (by rw [he_v4]; exact empty_args) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v2 h_v3 dropping he_v4 hinv1 e_v4 s1
  step as ⟨e_v5, he_v5⟩
  store_step with Store.native_spec_Teq s2 e_v5 (by rw [he_v5]; rfl) h_v3 h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_v2 dropping h_v3 h_v4 he_v5 hinv2 e_v5 s2 v3 v4
  have h_ite_v13 := (show if_8_eo__24smtx_5ftypeof s3 v5 v2 ⦃ r s' => s'.Inv ∧ s3.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_8_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s3
    rcases Store.boolean_value_native h_v5 with ⟨hx_6, hbv_6⟩ | ⟨hx_6, hbv_6⟩
    · ite_branch hbv_6
      store_step with ih.eo__24smtx_5ftypeof s3 v2 _ hinv3 h64 (hG.rem hrem) h_v2 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying dropping h_v2 h_v5 v2 v5
      step as ⟨e_v7, he_v7⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s4 e_v7 (by rw [he_v7]; exact empty_args) hinv4 h64 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_v6 dropping he_v7 e_v7
      step as ⟨e_v8, he_v8⟩
      store_step with Store.native_spec_Teq s5 e_v8 (by rw [he_v8]; rfl) h_v6 h_v7 hinv5 h64 as ⟨v8, s6, hinv6, h_v8⟩ growing hG carrying dropping h_v6 h_v7 he_v8 hinv5 e_v8 s5 v6 v7
      have h_ite_v11 := (show if_7_eo__24smtx_5ftypeof s6 v8 ⦃ r s' => s'.Inv ∧ s6.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_7_eo__24smtx_5ftypeof
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s6
        rcases Store.boolean_value_native h_v8 with ⟨hx_9, hbv_9⟩ | ⟨hx_9, hbv_9⟩
        · ite_branch hbv_9
          step as ⟨e_v9, he_v9⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s6 e_v9 (by rw [he_v9]; exact empty_args) hinv6 h64 as ⟨v9, s7, hinv7, h_v9⟩ growing hG carrying dropping h_v8 he_v9 e_v9 v8
          ite_done hinv7 hG with (native_ite_true_rep _ hx_9 h_v9)
        · ite_branch hbv_9
          step as ⟨e_v10, he_v10⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s6 e_v10 (by rw [he_v10]; exact empty_args) hinv6 h64 as ⟨v10, s7, hinv7, h_v10⟩ growing hG carrying dropping h_v8 he_v10 hinv6 e_v10 s6 v8
          ite_done hinv7 hG with (native_ite_false_rep _ hx_9 h_v10))
      store_step with h_ite_v11 as ⟨v11, s7, hinv7, h_v11⟩ growing hG carrying dropping h_ite_v11 h_v8 hinv6 s6 v8
      ite_done hinv7 hG with (native_ite_true_rep _ hx_6 h_v11)
    · ite_branch hbv_6
      step as ⟨e_v12, he_v12⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s3 e_v12 (by rw [he_v12]; exact empty_args) hinv3 h64 as ⟨v12, s4, hinv4, h_v12⟩ growing hG carrying dropping h_v2 h_v5 he_v12 hinv3 e_v12 s3 v2 v5
      ite_done hinv4 hG with (native_ite_false_rep _ hx_6 h_v12))
  store_step with h_ite_v13 as ⟨v13, s4, hinv4, h_v13⟩ growing hG carrying dropping h_ite_v13 h_v2 h_v5 hinv3 s3 v2 v5
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v2 dropping h_a0 h_v1 v1
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s1 e_v4 (by rw [he_v4]; exact empty_args) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v2 h_v3 dropping he_v4 hinv1 e_v4 s1
  step as ⟨e_v5, he_v5⟩
  store_step with Store.native_spec_Teq s2 e_v5 (by rw [he_v5]; rfl) h_v3 h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_v2 dropping h_v3 h_v4 he_v5 hinv2 e_v5 s2 v3 v4
  have h_ite_v13 := (show if_10_eo__24smtx_5ftypeof s3 v5 v2 ⦃ r s' => s'.Inv ∧ s3.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_10_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s3
    rcases Store.boolean_value_native h_v5 with ⟨hx_6, hbv_6⟩ | ⟨hx_6, hbv_6⟩
    · ite_branch hbv_6
      store_step with ih.eo__24smtx_5ftypeof s3 v2 _ hinv3 h64 (hG.rem hrem) h_v2 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying dropping h_v2 h_v5 v2 v5
      step as ⟨e_v7, he_v7⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s4 e_v7 (by rw [he_v7]; exact empty_args) hinv4 h64 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_v6 dropping he_v7 e_v7
      step as ⟨e_v8, he_v8⟩
      store_step with Store.native_spec_Teq s5 e_v8 (by rw [he_v8]; rfl) h_v6 h_v7 hinv5 h64 as ⟨v8, s6, hinv6, h_v8⟩ growing hG carrying dropping h_v6 h_v7 he_v8 hinv5 e_v8 s5 v6 v7
      have h_ite_v11 := (show if_9_eo__24smtx_5ftypeof s6 v8 ⦃ r s' => s'.Inv ∧ s6.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_9_eo__24smtx_5ftypeof
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s6
        rcases Store.boolean_value_native h_v8 with ⟨hx_9, hbv_9⟩ | ⟨hx_9, hbv_9⟩
        · ite_branch hbv_9
          step as ⟨e_v9, he_v9⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s6 e_v9 (by rw [he_v9]; exact empty_args) hinv6 h64 as ⟨v9, s7, hinv7, h_v9⟩ growing hG carrying dropping h_v8 he_v9 e_v9 v8
          ite_done hinv7 hG with (native_ite_true_rep _ hx_9 h_v9)
        · ite_branch hbv_9
          step as ⟨e_v10, he_v10⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s6 e_v10 (by rw [he_v10]; exact empty_args) hinv6 h64 as ⟨v10, s7, hinv7, h_v10⟩ growing hG carrying dropping h_v8 he_v10 hinv6 e_v10 s6 v8
          ite_done hinv7 hG with (native_ite_false_rep _ hx_9 h_v10))
      store_step with h_ite_v11 as ⟨v11, s7, hinv7, h_v11⟩ growing hG carrying dropping h_ite_v11 h_v8 hinv6 s6 v8
      ite_done hinv7 hG with (native_ite_true_rep _ hx_6 h_v11)
    · ite_branch hbv_6
      step as ⟨e_v12, he_v12⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s3 e_v12 (by rw [he_v12]; exact empty_args) hinv3 h64 as ⟨v12, s4, hinv4, h_v12⟩ growing hG carrying dropping h_v2 h_v5 he_v12 hinv3 e_v12 s3 v2 v5
      ite_done hinv4 hG with (native_ite_false_rep _ hx_6 h_v12))
  store_step with h_ite_v13 as ⟨v13, s4, hinv4, h_v13⟩ growing hG carrying dropping h_ite_v13 h_v2 h_v5 hinv3 s3 v2 v5
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v2 dropping h_a0 h_v1 v1
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v3 dropping h_v2 hinv1 s1 v2
  store_step with ih.eo__24smtx_5ftypeof_5f_3d s2 v3 v4 _ _ hinv2 h64 (hG.rem hrem) h_v3 h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying dropping h_v3 h_v4 hinv2 s2 v3 v4
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
  store_step with ih.eo__24smtx_5ftypeof s v2 _ hinv h64 hrem h_v2 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v1 dropping h_a0 h_v2 v2
  store_step with ih.eo__24smtx_5ftypeof_5fbindings s1 v1 v3 _ _ hinv1 h64 (hG.rem hrem) h_v1 h_v3 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying dropping h_v1 h_v3 hinv1 s1 v1 v3
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v2 dropping h_a0 h_v1 v1
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v3 dropping h_v2 hinv1 s1 v2
  store_step with ih.eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2 s2 v3 v4 _ _ hinv2 h64 (hG.rem hrem) h_v3 h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying dropping h_v3 h_v4 hinv2 s2 v3 v4
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v2 dropping h_a0 h_v1 v1
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v3 dropping h_v2 hinv1 s1 v2
  store_step with ih.eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2 s2 v3 v4 _ _ hinv2 h64 (hG.rem hrem) h_v3 h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying dropping h_v3 h_v4 hinv2 s2 v3 v4
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v2 dropping h_a0 h_v1 v1
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v3 dropping h_v2 hinv1 s1 v2
  store_step with ih.eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2 s2 v3 v4 _ _ hinv2 h64 (hG.rem hrem) h_v3 h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying dropping h_v3 h_v4 hinv2 s2 v3 v4
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v2 dropping h_a0 h_v1 v1
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v3 dropping h_v2 hinv1 s1 v2
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s2 e_v5 (by rw [he_v5]; exact empty_args) hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_v3 h_v4 dropping he_v5 hinv2 e_v5 s2
  store_step with ih.eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2_5fret s3 v3 v4 v5 _ _ _ hinv3 h64 (hG.rem hrem) h_v3 h_v4 h_v5 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying dropping h_v3 h_v4 h_v5 hinv3 s3 v3 v4 v5
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v2 dropping h_a0 h_v1 v1
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v3 dropping h_v2 hinv1 s1 v2
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s2 e_v5 (by rw [he_v5]; exact empty_args) hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_v3 h_v4 dropping he_v5 hinv2 e_v5 s2
  store_step with ih.eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2_5fret s3 v3 v4 v5 _ _ _ hinv3 h64 (hG.rem hrem) h_v3 h_v4 h_v5 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying dropping h_v3 h_v4 h_v5 hinv3 s3 v3 v4 v5
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v2 dropping h_a0 h_v1 v1
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v3 dropping h_v2 hinv1 s1 v2
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s2 e_v5 (by rw [he_v5]; exact empty_args) hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_v3 h_v4 dropping he_v5 hinv2 e_v5 s2
  store_step with ih.eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2_5fret s3 v3 v4 v5 _ _ _ hinv3 h64 (hG.rem hrem) h_v3 h_v4 h_v5 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying dropping h_v3 h_v4 h_v5 hinv3 s3 v3 v4 v5
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v2 dropping h_a0 h_v1 v1
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v3 dropping h_v2 hinv1 s1 v2
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s2 e_v5 (by rw [he_v5]; exact empty_args) hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_v3 h_v4 dropping he_v5 hinv2 e_v5 s2
  store_step with ih.eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2_5fret s3 v3 v4 v5 _ _ _ hinv3 h64 (hG.rem hrem) h_v3 h_v4 h_v5 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying dropping h_v3 h_v4 h_v5 hinv3 s3 v3 v4 v5
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying dropping h_a0 h_v1 v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eInt.construct s1 e_v3 (by rw [he_v3]; exact empty_args) hinv1 h64 as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying h_v2 dropping he_v3 hinv1 e_v3 s1
  step as ⟨e_v4, he_v4⟩
  store_step with Store.native_spec_Teq s2 e_v4 (by rw [he_v4]; rfl) h_v2 h_v3 hinv2 h64 as ⟨v4, s3, hinv3, h_v4⟩ growing hG carrying dropping h_v2 h_v3 he_v4 hinv2 e_v4 s2 v2 v3
  have h_ite_v7 := (show if_11_eo__24smtx_5ftypeof s3 v4 ⦃ r s' => s'.Inv ∧ s3.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_11_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s3
    rcases Store.boolean_value_native h_v4 with ⟨hx_5, hbv_5⟩ | ⟨hx_5, hbv_5⟩
    · ite_branch hbv_5
      step as ⟨e_v5, he_v5⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eReal.construct s3 e_v5 (by rw [he_v5]; exact empty_args) hinv3 h64 as ⟨v5, s4, hinv4, h_v5⟩ growing hG carrying dropping h_v4 he_v5 e_v5 v4
      ite_done hinv4 hG with (native_ite_true_rep _ hx_5 h_v5)
    · ite_branch hbv_5
      step as ⟨e_v6, he_v6⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s3 e_v6 (by rw [he_v6]; exact empty_args) hinv3 h64 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying dropping h_v4 he_v6 hinv3 e_v6 s3 v4
      ite_done hinv4 hG with (native_ite_false_rep _ hx_5 h_v6))
  store_step with h_ite_v7 as ⟨v7, s4, hinv4, h_v7⟩ growing hG carrying dropping h_ite_v7 h_v4 hinv3 s3 v4
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying dropping h_a0 h_v1 v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eReal.construct s1 e_v3 (by rw [he_v3]; exact empty_args) hinv1 h64 as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying h_v2 dropping he_v3 hinv1 e_v3 s1
  step as ⟨e_v4, he_v4⟩
  store_step with Store.native_spec_Teq s2 e_v4 (by rw [he_v4]; rfl) h_v2 h_v3 hinv2 h64 as ⟨v4, s3, hinv3, h_v4⟩ growing hG carrying dropping h_v2 h_v3 he_v4 hinv2 e_v4 s2 v2 v3
  have h_ite_v7 := (show if_12_eo__24smtx_5ftypeof s3 v4 ⦃ r s' => s'.Inv ∧ s3.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_12_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s3
    rcases Store.boolean_value_native h_v4 with ⟨hx_5, hbv_5⟩ | ⟨hx_5, hbv_5⟩
    · ite_branch hbv_5
      step as ⟨e_v5, he_v5⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eInt.construct s3 e_v5 (by rw [he_v5]; exact empty_args) hinv3 h64 as ⟨v5, s4, hinv4, h_v5⟩ growing hG carrying dropping h_v4 he_v5 e_v5 v4
      ite_done hinv4 hG with (native_ite_true_rep _ hx_5 h_v5)
    · ite_branch hbv_5
      step as ⟨e_v6, he_v6⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s3 e_v6 (by rw [he_v6]; exact empty_args) hinv3 h64 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying dropping h_v4 he_v6 hinv3 e_v6 s3 v4
      ite_done hinv4 hG with (native_ite_false_rep _ hx_5 h_v6))
  store_step with h_ite_v7 as ⟨v7, s4, hinv4, h_v7⟩ growing hG carrying dropping h_ite_v7 h_v4 hinv3 s3 v4
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying dropping h_a0 h_v1 v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eReal.construct s1 e_v3 (by rw [he_v3]; exact empty_args) hinv1 h64 as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying h_v2 dropping he_v3 hinv1 e_v3 s1
  step as ⟨e_v4, he_v4⟩
  store_step with Store.native_spec_Teq s2 e_v4 (by rw [he_v4]; rfl) h_v2 h_v3 hinv2 h64 as ⟨v4, s3, hinv3, h_v4⟩ growing hG carrying dropping h_v2 h_v3 he_v4 hinv2 e_v4 s2 v2 v3
  have h_ite_v7 := (show if_13_eo__24smtx_5ftypeof s3 v4 ⦃ r s' => s'.Inv ∧ s3.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_13_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s3
    rcases Store.boolean_value_native h_v4 with ⟨hx_5, hbv_5⟩ | ⟨hx_5, hbv_5⟩
    · ite_branch hbv_5
      step as ⟨e_v5, he_v5⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s3 e_v5 (by rw [he_v5]; exact empty_args) hinv3 h64 as ⟨v5, s4, hinv4, h_v5⟩ growing hG carrying dropping h_v4 he_v5 e_v5 v4
      ite_done hinv4 hG with (native_ite_true_rep _ hx_5 h_v5)
    · ite_branch hbv_5
      step as ⟨e_v6, he_v6⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s3 e_v6 (by rw [he_v6]; exact empty_args) hinv3 h64 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying dropping h_v4 he_v6 hinv3 e_v6 s3 v4
      ite_done hinv4 hG with (native_ite_false_rep _ hx_5 h_v6))
  store_step with h_ite_v7 as ⟨v7, s4, hinv4, h_v7⟩ growing hG carrying dropping h_ite_v7 h_v4 hinv3 s3 v4
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying dropping h_a0 h_v1 v1
  store_step with ih.eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f1 s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying dropping h_v2 hinv1 s1 v2
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying dropping h_a0 h_v1 v1
  store_step with ih.eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f1 s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying dropping h_v2 hinv1 s1 v2
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v2 dropping h_a0 h_v1 v1
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eInt.construct s1 e_v4 (by rw [he_v4]; exact empty_args) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v2 h_v3 dropping he_v4 hinv1 e_v4 s1
  step as ⟨e_v5, he_v5⟩
  store_step with Store.native_spec_Teq s2 e_v5 (by rw [he_v5]; rfl) h_v3 h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_v2 dropping h_v3 h_v4 he_v5 hinv2 e_v5 s2 v3 v4
  have h_ite_v13 := (show if_15_eo__24smtx_5ftypeof s3 v5 v2 ⦃ r s' => s'.Inv ∧ s3.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_15_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s3
    rcases Store.boolean_value_native h_v5 with ⟨hx_6, hbv_6⟩ | ⟨hx_6, hbv_6⟩
    · ite_branch hbv_6
      store_step with ih.eo__24smtx_5ftypeof s3 v2 _ hinv3 h64 (hG.rem hrem) h_v2 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying dropping h_v2 h_v5 v2 v5
      step as ⟨e_v7, he_v7⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eInt.construct s4 e_v7 (by rw [he_v7]; exact empty_args) hinv4 h64 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_v6 dropping he_v7 e_v7
      step as ⟨e_v8, he_v8⟩
      store_step with Store.native_spec_Teq s5 e_v8 (by rw [he_v8]; rfl) h_v6 h_v7 hinv5 h64 as ⟨v8, s6, hinv6, h_v8⟩ growing hG carrying dropping h_v6 h_v7 he_v8 hinv5 e_v8 s5 v6 v7
      have h_ite_v11 := (show if_14_eo__24smtx_5ftypeof s6 v8 ⦃ r s' => s'.Inv ∧ s6.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_14_eo__24smtx_5ftypeof
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s6
        rcases Store.boolean_value_native h_v8 with ⟨hx_9, hbv_9⟩ | ⟨hx_9, hbv_9⟩
        · ite_branch hbv_9
          step as ⟨e_v9, he_v9⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eInt.construct s6 e_v9 (by rw [he_v9]; exact empty_args) hinv6 h64 as ⟨v9, s7, hinv7, h_v9⟩ growing hG carrying dropping h_v8 he_v9 e_v9 v8
          ite_done hinv7 hG with (native_ite_true_rep _ hx_9 h_v9)
        · ite_branch hbv_9
          step as ⟨e_v10, he_v10⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s6 e_v10 (by rw [he_v10]; exact empty_args) hinv6 h64 as ⟨v10, s7, hinv7, h_v10⟩ growing hG carrying dropping h_v8 he_v10 hinv6 e_v10 s6 v8
          ite_done hinv7 hG with (native_ite_false_rep _ hx_9 h_v10))
      store_step with h_ite_v11 as ⟨v11, s7, hinv7, h_v11⟩ growing hG carrying dropping h_ite_v11 h_v8 hinv6 s6 v8
      ite_done hinv7 hG with (native_ite_true_rep _ hx_6 h_v11)
    · ite_branch hbv_6
      step as ⟨e_v12, he_v12⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s3 e_v12 (by rw [he_v12]; exact empty_args) hinv3 h64 as ⟨v12, s4, hinv4, h_v12⟩ growing hG carrying dropping h_v2 h_v5 he_v12 hinv3 e_v12 s3 v2 v5
      ite_done hinv4 hG with (native_ite_false_rep _ hx_6 h_v12))
  store_step with h_ite_v13 as ⟨v13, s4, hinv4, h_v13⟩ growing hG carrying dropping h_ite_v13 h_v2 h_v5 hinv3 s3 v2 v5
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v2 dropping h_a0 h_v1 v1
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eInt.construct s1 e_v4 (by rw [he_v4]; exact empty_args) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v2 h_v3 dropping he_v4 hinv1 e_v4 s1
  step as ⟨e_v5, he_v5⟩
  store_step with Store.native_spec_Teq s2 e_v5 (by rw [he_v5]; rfl) h_v3 h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_v2 dropping h_v3 h_v4 he_v5 hinv2 e_v5 s2 v3 v4
  have h_ite_v13 := (show if_17_eo__24smtx_5ftypeof s3 v5 v2 ⦃ r s' => s'.Inv ∧ s3.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_17_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s3
    rcases Store.boolean_value_native h_v5 with ⟨hx_6, hbv_6⟩ | ⟨hx_6, hbv_6⟩
    · ite_branch hbv_6
      store_step with ih.eo__24smtx_5ftypeof s3 v2 _ hinv3 h64 (hG.rem hrem) h_v2 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying dropping h_v2 h_v5 v2 v5
      step as ⟨e_v7, he_v7⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eInt.construct s4 e_v7 (by rw [he_v7]; exact empty_args) hinv4 h64 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_v6 dropping he_v7 e_v7
      step as ⟨e_v8, he_v8⟩
      store_step with Store.native_spec_Teq s5 e_v8 (by rw [he_v8]; rfl) h_v6 h_v7 hinv5 h64 as ⟨v8, s6, hinv6, h_v8⟩ growing hG carrying dropping h_v6 h_v7 he_v8 hinv5 e_v8 s5 v6 v7
      have h_ite_v11 := (show if_16_eo__24smtx_5ftypeof s6 v8 ⦃ r s' => s'.Inv ∧ s6.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_16_eo__24smtx_5ftypeof
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s6
        rcases Store.boolean_value_native h_v8 with ⟨hx_9, hbv_9⟩ | ⟨hx_9, hbv_9⟩
        · ite_branch hbv_9
          step as ⟨e_v9, he_v9⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eInt.construct s6 e_v9 (by rw [he_v9]; exact empty_args) hinv6 h64 as ⟨v9, s7, hinv7, h_v9⟩ growing hG carrying dropping h_v8 he_v9 e_v9 v8
          ite_done hinv7 hG with (native_ite_true_rep _ hx_9 h_v9)
        · ite_branch hbv_9
          step as ⟨e_v10, he_v10⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s6 e_v10 (by rw [he_v10]; exact empty_args) hinv6 h64 as ⟨v10, s7, hinv7, h_v10⟩ growing hG carrying dropping h_v8 he_v10 hinv6 e_v10 s6 v8
          ite_done hinv7 hG with (native_ite_false_rep _ hx_9 h_v10))
      store_step with h_ite_v11 as ⟨v11, s7, hinv7, h_v11⟩ growing hG carrying dropping h_ite_v11 h_v8 hinv6 s6 v8
      ite_done hinv7 hG with (native_ite_true_rep _ hx_6 h_v11)
    · ite_branch hbv_6
      step as ⟨e_v12, he_v12⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s3 e_v12 (by rw [he_v12]; exact empty_args) hinv3 h64 as ⟨v12, s4, hinv4, h_v12⟩ growing hG carrying dropping h_v2 h_v5 he_v12 hinv3 e_v12 s3 v2 v5
      ite_done hinv4 hG with (native_ite_false_rep _ hx_6 h_v12))
  store_step with h_ite_v13 as ⟨v13, s4, hinv4, h_v13⟩ growing hG carrying dropping h_ite_v13 h_v2 h_v5 hinv3 s3 v2 v5
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v2 dropping h_a0 h_v1 v1
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eInt.construct s1 e_v4 (by rw [he_v4]; exact empty_args) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v2 h_v3 dropping he_v4 hinv1 e_v4 s1
  step as ⟨e_v5, he_v5⟩
  store_step with Store.native_spec_Teq s2 e_v5 (by rw [he_v5]; rfl) h_v3 h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_v2 dropping h_v3 h_v4 he_v5 hinv2 e_v5 s2 v3 v4
  have h_ite_v13 := (show if_19_eo__24smtx_5ftypeof s3 v5 v2 ⦃ r s' => s'.Inv ∧ s3.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_19_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s3
    rcases Store.boolean_value_native h_v5 with ⟨hx_6, hbv_6⟩ | ⟨hx_6, hbv_6⟩
    · ite_branch hbv_6
      store_step with ih.eo__24smtx_5ftypeof s3 v2 _ hinv3 h64 (hG.rem hrem) h_v2 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying dropping h_v2 h_v5 v2 v5
      step as ⟨e_v7, he_v7⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eInt.construct s4 e_v7 (by rw [he_v7]; exact empty_args) hinv4 h64 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_v6 dropping he_v7 e_v7
      step as ⟨e_v8, he_v8⟩
      store_step with Store.native_spec_Teq s5 e_v8 (by rw [he_v8]; rfl) h_v6 h_v7 hinv5 h64 as ⟨v8, s6, hinv6, h_v8⟩ growing hG carrying dropping h_v6 h_v7 he_v8 hinv5 e_v8 s5 v6 v7
      have h_ite_v11 := (show if_18_eo__24smtx_5ftypeof s6 v8 ⦃ r s' => s'.Inv ∧ s6.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_18_eo__24smtx_5ftypeof
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s6
        rcases Store.boolean_value_native h_v8 with ⟨hx_9, hbv_9⟩ | ⟨hx_9, hbv_9⟩
        · ite_branch hbv_9
          step as ⟨e_v9, he_v9⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s6 e_v9 (by rw [he_v9]; exact empty_args) hinv6 h64 as ⟨v9, s7, hinv7, h_v9⟩ growing hG carrying dropping h_v8 he_v9 e_v9 v8
          ite_done hinv7 hG with (native_ite_true_rep _ hx_9 h_v9)
        · ite_branch hbv_9
          step as ⟨e_v10, he_v10⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s6 e_v10 (by rw [he_v10]; exact empty_args) hinv6 h64 as ⟨v10, s7, hinv7, h_v10⟩ growing hG carrying dropping h_v8 he_v10 hinv6 e_v10 s6 v8
          ite_done hinv7 hG with (native_ite_false_rep _ hx_9 h_v10))
      store_step with h_ite_v11 as ⟨v11, s7, hinv7, h_v11⟩ growing hG carrying dropping h_ite_v11 h_v8 hinv6 s6 v8
      ite_done hinv7 hG with (native_ite_true_rep _ hx_6 h_v11)
    · ite_branch hbv_6
      step as ⟨e_v12, he_v12⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s3 e_v12 (by rw [he_v12]; exact empty_args) hinv3 h64 as ⟨v12, s4, hinv4, h_v12⟩ growing hG carrying dropping h_v2 h_v5 he_v12 hinv3 e_v12 s3 v2 v5
      ite_done hinv4 hG with (native_ite_false_rep _ hx_6 h_v12))
  store_step with h_ite_v13 as ⟨v13, s4, hinv4, h_v13⟩ growing hG carrying dropping h_ite_v13 h_v2 h_v5 hinv3 s3 v2 v5
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying dropping h_a0 h_v1 v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eInt.construct s1 e_v3 (by rw [he_v3]; exact empty_args) hinv1 h64 as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying h_v2 dropping he_v3 hinv1 e_v3 s1
  step as ⟨e_v4, he_v4⟩
  store_step with Store.native_spec_Teq s2 e_v4 (by rw [he_v4]; rfl) h_v2 h_v3 hinv2 h64 as ⟨v4, s3, hinv3, h_v4⟩ growing hG carrying dropping h_v2 h_v3 he_v4 hinv2 e_v4 s2 v2 v3
  have h_ite_v7 := (show if_20_eo__24smtx_5ftypeof s3 v4 ⦃ r s' => s'.Inv ∧ s3.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_20_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s3
    rcases Store.boolean_value_native h_v4 with ⟨hx_5, hbv_5⟩ | ⟨hx_5, hbv_5⟩
    · ite_branch hbv_5
      step as ⟨e_v5, he_v5⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eInt.construct s3 e_v5 (by rw [he_v5]; exact empty_args) hinv3 h64 as ⟨v5, s4, hinv4, h_v5⟩ growing hG carrying dropping h_v4 he_v5 e_v5 v4
      ite_done hinv4 hG with (native_ite_true_rep _ hx_5 h_v5)
    · ite_branch hbv_5
      step as ⟨e_v6, he_v6⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s3 e_v6 (by rw [he_v6]; exact empty_args) hinv3 h64 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying dropping h_v4 he_v6 hinv3 e_v6 s3 v4
      ite_done hinv4 hG with (native_ite_false_rep _ hx_5 h_v6))
  store_step with h_ite_v7 as ⟨v7, s4, hinv4, h_v7⟩ growing hG carrying dropping h_ite_v7 h_v4 hinv3 s3 v4
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying dropping h_a0 h_v1 v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eInt.construct s1 e_v3 (by rw [he_v3]; exact empty_args) hinv1 h64 as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying h_v2 dropping he_v3 hinv1 e_v3 s1
  step as ⟨e_v4, he_v4⟩
  store_step with Store.native_spec_Teq s2 e_v4 (by rw [he_v4]; rfl) h_v2 h_v3 hinv2 h64 as ⟨v4, s3, hinv3, h_v4⟩ growing hG carrying dropping h_v2 h_v3 he_v4 hinv2 e_v4 s2 v2 v3
  have h_ite_v7 := (show if_21_eo__24smtx_5ftypeof s3 v4 ⦃ r s' => s'.Inv ∧ s3.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_21_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s3
    rcases Store.boolean_value_native h_v4 with ⟨hx_5, hbv_5⟩ | ⟨hx_5, hbv_5⟩
    · ite_branch hbv_5
      step as ⟨e_v5, he_v5⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eInt.construct s3 e_v5 (by rw [he_v5]; exact empty_args) hinv3 h64 as ⟨v5, s4, hinv4, h_v5⟩ growing hG carrying dropping h_v4 he_v5 e_v5 v4
      ite_done hinv4 hG with (native_ite_true_rep _ hx_5 h_v5)
    · ite_branch hbv_5
      step as ⟨e_v6, he_v6⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s3 e_v6 (by rw [he_v6]; exact empty_args) hinv3 h64 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying dropping h_v4 he_v6 hinv3 e_v6 s3 v4
      ite_done hinv4 hG with (native_ite_false_rep _ hx_5 h_v6))
  store_step with h_ite_v7 as ⟨v7, s4, hinv4, h_v7⟩ growing hG carrying dropping h_ite_v7 h_v4 hinv3 s3 v4
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v2 dropping h_a0 h_v1 v1
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eInt.construct s1 e_v4 (by rw [he_v4]; exact empty_args) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v2 h_v3 dropping he_v4 hinv1 e_v4 s1
  step as ⟨e_v5, he_v5⟩
  store_step with Store.native_spec_Teq s2 e_v5 (by rw [he_v5]; rfl) h_v3 h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_v2 dropping h_v3 h_v4 he_v5 hinv2 e_v5 s2 v3 v4
  have h_ite_v13 := (show if_23_eo__24smtx_5ftypeof s3 v5 v2 ⦃ r s' => s'.Inv ∧ s3.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_23_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s3
    rcases Store.boolean_value_native h_v5 with ⟨hx_6, hbv_6⟩ | ⟨hx_6, hbv_6⟩
    · ite_branch hbv_6
      store_step with ih.eo__24smtx_5ftypeof s3 v2 _ hinv3 h64 (hG.rem hrem) h_v2 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying dropping h_v2 h_v5 v2 v5
      step as ⟨e_v7, he_v7⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eInt.construct s4 e_v7 (by rw [he_v7]; exact empty_args) hinv4 h64 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_v6 dropping he_v7 e_v7
      step as ⟨e_v8, he_v8⟩
      store_step with Store.native_spec_Teq s5 e_v8 (by rw [he_v8]; rfl) h_v6 h_v7 hinv5 h64 as ⟨v8, s6, hinv6, h_v8⟩ growing hG carrying dropping h_v6 h_v7 he_v8 hinv5 e_v8 s5 v6 v7
      have h_ite_v11 := (show if_22_eo__24smtx_5ftypeof s6 v8 ⦃ r s' => s'.Inv ∧ s6.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_22_eo__24smtx_5ftypeof
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s6
        rcases Store.boolean_value_native h_v8 with ⟨hx_9, hbv_9⟩ | ⟨hx_9, hbv_9⟩
        · ite_branch hbv_9
          step as ⟨e_v9, he_v9⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eInt.construct s6 e_v9 (by rw [he_v9]; exact empty_args) hinv6 h64 as ⟨v9, s7, hinv7, h_v9⟩ growing hG carrying dropping h_v8 he_v9 e_v9 v8
          ite_done hinv7 hG with (native_ite_true_rep _ hx_9 h_v9)
        · ite_branch hbv_9
          step as ⟨e_v10, he_v10⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s6 e_v10 (by rw [he_v10]; exact empty_args) hinv6 h64 as ⟨v10, s7, hinv7, h_v10⟩ growing hG carrying dropping h_v8 he_v10 hinv6 e_v10 s6 v8
          ite_done hinv7 hG with (native_ite_false_rep _ hx_9 h_v10))
      store_step with h_ite_v11 as ⟨v11, s7, hinv7, h_v11⟩ growing hG carrying dropping h_ite_v11 h_v8 hinv6 s6 v8
      ite_done hinv7 hG with (native_ite_true_rep _ hx_6 h_v11)
    · ite_branch hbv_6
      step as ⟨e_v12, he_v12⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s3 e_v12 (by rw [he_v12]; exact empty_args) hinv3 h64 as ⟨v12, s4, hinv4, h_v12⟩ growing hG carrying dropping h_v2 h_v5 he_v12 hinv3 e_v12 s3 v2 v5
      ite_done hinv4 hG with (native_ite_false_rep _ hx_6 h_v12))
  store_step with h_ite_v13 as ⟨v13, s4, hinv4, h_v13⟩ growing hG carrying dropping h_ite_v13 h_v2 h_v5 hinv3 s3 v2 v5
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v2 dropping h_a0 h_v1 v1
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eInt.construct s1 e_v4 (by rw [he_v4]; exact empty_args) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v2 h_v3 dropping he_v4 hinv1 e_v4 s1
  step as ⟨e_v5, he_v5⟩
  store_step with Store.native_spec_Teq s2 e_v5 (by rw [he_v5]; rfl) h_v3 h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_v2 dropping h_v3 h_v4 he_v5 hinv2 e_v5 s2 v3 v4
  have h_ite_v13 := (show if_25_eo__24smtx_5ftypeof s3 v5 v2 ⦃ r s' => s'.Inv ∧ s3.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_25_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s3
    rcases Store.boolean_value_native h_v5 with ⟨hx_6, hbv_6⟩ | ⟨hx_6, hbv_6⟩
    · ite_branch hbv_6
      store_step with ih.eo__24smtx_5ftypeof s3 v2 _ hinv3 h64 (hG.rem hrem) h_v2 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying dropping h_v2 h_v5 v2 v5
      step as ⟨e_v7, he_v7⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eInt.construct s4 e_v7 (by rw [he_v7]; exact empty_args) hinv4 h64 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_v6 dropping he_v7 e_v7
      step as ⟨e_v8, he_v8⟩
      store_step with Store.native_spec_Teq s5 e_v8 (by rw [he_v8]; rfl) h_v6 h_v7 hinv5 h64 as ⟨v8, s6, hinv6, h_v8⟩ growing hG carrying dropping h_v6 h_v7 he_v8 hinv5 e_v8 s5 v6 v7
      have h_ite_v11 := (show if_24_eo__24smtx_5ftypeof s6 v8 ⦃ r s' => s'.Inv ∧ s6.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_24_eo__24smtx_5ftypeof
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s6
        rcases Store.boolean_value_native h_v8 with ⟨hx_9, hbv_9⟩ | ⟨hx_9, hbv_9⟩
        · ite_branch hbv_9
          step as ⟨e_v9, he_v9⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eInt.construct s6 e_v9 (by rw [he_v9]; exact empty_args) hinv6 h64 as ⟨v9, s7, hinv7, h_v9⟩ growing hG carrying dropping h_v8 he_v9 e_v9 v8
          ite_done hinv7 hG with (native_ite_true_rep _ hx_9 h_v9)
        · ite_branch hbv_9
          step as ⟨e_v10, he_v10⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s6 e_v10 (by rw [he_v10]; exact empty_args) hinv6 h64 as ⟨v10, s7, hinv7, h_v10⟩ growing hG carrying dropping h_v8 he_v10 hinv6 e_v10 s6 v8
          ite_done hinv7 hG with (native_ite_false_rep _ hx_9 h_v10))
      store_step with h_ite_v11 as ⟨v11, s7, hinv7, h_v11⟩ growing hG carrying dropping h_ite_v11 h_v8 hinv6 s6 v8
      ite_done hinv7 hG with (native_ite_true_rep _ hx_6 h_v11)
    · ite_branch hbv_6
      step as ⟨e_v12, he_v12⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s3 e_v12 (by rw [he_v12]; exact empty_args) hinv3 h64 as ⟨v12, s4, hinv4, h_v12⟩ growing hG carrying dropping h_v2 h_v5 he_v12 hinv3 e_v12 s3 v2 v5
      ite_done hinv4 hG with (native_ite_false_rep _ hx_6 h_v12))
  store_step with h_ite_v13 as ⟨v13, s4, hinv4, h_v13⟩ growing hG carrying dropping h_ite_v13 h_v2 h_v5 hinv3 s3 v2 v5
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v2 dropping h_a0 h_v1 v1
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v3 dropping h_v2 hinv1 s1 v2
  store_step with ih.eo__24smtx_5ftypeof_5fselect s2 v3 v4 _ _ hinv2 h64 (hG.rem hrem) h_v3 h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying dropping h_v3 h_v4 hinv2 s2 v3 v4
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v4, s1, hinv1, h_v4⟩ growing hG carrying h_v2 h_v3 dropping h_a0 h_v1 v1
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v5, s2, hinv2, h_v5⟩ growing hG carrying h_v3 h_v4 dropping h_v2 hinv1 s1 v2
  store_step with ih.eo__24smtx_5ftypeof s2 v3 _ hinv2 h64 (hG.rem hrem) h_v3 as ⟨v6, s3, hinv3, h_v6⟩ growing hG carrying h_v4 h_v5 dropping h_v3 hinv2 s2 v3
  store_step with ih.eo__24smtx_5ftypeof_5fstore s3 v4 v5 v6 _ _ _ hinv3 h64 (hG.rem hrem) h_v4 h_v5 h_v6 as ⟨v7, s4, hinv4, h_v7⟩ growing hG carrying dropping h_v4 h_v5 h_v6 hinv3 s3 v4 v5 v6
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v2 dropping h_a0 h_v1 v1
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v3 dropping h_v2 hinv1 s1 v2
  store_step with ih.eo__24smtx_5ftypeof_5fmap_5fdiff s2 v3 v4 _ _ hinv2 h64 (hG.rem hrem) h_v3 h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying dropping h_v3 h_v4 hinv2 s2 v3 v4
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v2 dropping h_a0 h_v1 v1
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v3 dropping h_v2 hinv1 s1 v2
  store_step with ih.eo__24smtx_5ftypeof_5fconcat s2 v3 v4 _ _ hinv2 h64 (hG.rem hrem) h_v3 h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying dropping h_v3 h_v4 hinv2 s2 v3 v4
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
  store_step with ih.eo__24smtx_5ftypeof s v3 _ hinv h64 hrem h_v3 as ⟨v4, s1, hinv1, h_v4⟩ growing hG carrying h_v1 h_v2 dropping h_a0 h_v3 v3
  store_step with ih.eo__24smtx_5ftypeof_5fextract s1 v1 v2 v4 _ _ _ hinv1 h64 (hG.rem hrem) h_v1 h_v2 h_v4 as ⟨v5, s2, hinv2, h_v5⟩ growing hG carrying dropping h_v1 h_v2 h_v4 hinv1 s1 v1 v2 v4
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
  store_step with ih.eo__24smtx_5ftypeof s v2 _ hinv h64 hrem h_v2 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v1 dropping h_a0 h_v2 v2
  store_step with ih.eo__24smtx_5ftypeof_5frepeat s1 v1 v3 _ _ hinv1 h64 (hG.rem hrem) h_v1 h_v3 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying dropping h_v1 h_v3 hinv1 s1 v1 v3
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying dropping h_a0 h_v1 v1
  store_step with ih.eo__24smtx_5ftypeof_5fbv_5fop_5f1 s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying dropping h_v2 hinv1 s1 v2
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v2 dropping h_a0 h_v1 v1
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v3 dropping h_v2 hinv1 s1 v2
  store_step with ih.eo__24smtx_5ftypeof_5fbv_5fop_5f2 s2 v3 v4 _ _ hinv2 h64 (hG.rem hrem) h_v3 h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying dropping h_v3 h_v4 hinv2 s2 v3 v4
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v2 dropping h_a0 h_v1 v1
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v3 dropping h_v2 hinv1 s1 v2
  store_step with ih.eo__24smtx_5ftypeof_5fbv_5fop_5f2 s2 v3 v4 _ _ hinv2 h64 (hG.rem hrem) h_v3 h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying dropping h_v3 h_v4 hinv2 s2 v3 v4
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v2 dropping h_a0 h_v1 v1
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v3 dropping h_v2 hinv1 s1 v2
  store_step with ih.eo__24smtx_5ftypeof_5fbv_5fop_5f2 s2 v3 v4 _ _ hinv2 h64 (hG.rem hrem) h_v3 h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying dropping h_v3 h_v4 hinv2 s2 v3 v4
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v2 dropping h_a0 h_v1 v1
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v3 dropping h_v2 hinv1 s1 v2
  store_step with ih.eo__24smtx_5ftypeof_5fbv_5fop_5f2 s2 v3 v4 _ _ hinv2 h64 (hG.rem hrem) h_v3 h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying dropping h_v3 h_v4 hinv2 s2 v3 v4
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v2 dropping h_a0 h_v1 v1
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v3 dropping h_v2 hinv1 s1 v2
  store_step with ih.eo__24smtx_5ftypeof_5fbv_5fop_5f2 s2 v3 v4 _ _ hinv2 h64 (hG.rem hrem) h_v3 h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying dropping h_v3 h_v4 hinv2 s2 v3 v4
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v2 dropping h_a0 h_v1 v1
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v3 dropping h_v2 hinv1 s1 v2
  store_step with ih.eo__24smtx_5ftypeof_5fbv_5fop_5f2 s2 v3 v4 _ _ hinv2 h64 (hG.rem hrem) h_v3 h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying dropping h_v3 h_v4 hinv2 s2 v3 v4
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v2 dropping h_a0 h_v1 v1
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v3 dropping h_v2 hinv1 s1 v2
  store_step with Store.native_nat_zero_spec s2 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_v3 h_v4 dropping hinv2 s2
  step as ⟨e_v6, he_v6⟩
  store_step with Store.native_spec_nat_succ s3 e_v6 (by rw [he_v6]; rfl) h_v5 hinv3 h64 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_v3 h_v4 dropping h_v5 he_v6 hinv3 e_v6 s3 v5
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eBitVec.construct s4 e_v7 (by rw [he_v7]; rfl) h_v6 hinv4 h64 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_v3 h_v4 dropping h_v6 he_v7 hinv4 e_v7 s4 v6
  store_step with ih.eo__24smtx_5ftypeof_5fbv_5fop_5f2_5fret s5 v3 v4 v7 _ _ _ hinv5 h64 (hG.rem hrem) h_v3 h_v4 h_v7 as ⟨v8, s6, hinv6, h_v8⟩ growing hG carrying dropping h_v3 h_v4 h_v7 hinv5 s5 v3 v4 v7
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying dropping h_a0 h_v1 v1
  store_step with ih.eo__24smtx_5ftypeof_5fbv_5fop_5f1 s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying dropping h_v2 hinv1 s1 v2
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v2 dropping h_a0 h_v1 v1
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v3 dropping h_v2 hinv1 s1 v2
  store_step with ih.eo__24smtx_5ftypeof_5fbv_5fop_5f2 s2 v3 v4 _ _ hinv2 h64 (hG.rem hrem) h_v3 h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying dropping h_v3 h_v4 hinv2 s2 v3 v4
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v2 dropping h_a0 h_v1 v1
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v3 dropping h_v2 hinv1 s1 v2
  store_step with ih.eo__24smtx_5ftypeof_5fbv_5fop_5f2 s2 v3 v4 _ _ hinv2 h64 (hG.rem hrem) h_v3 h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying dropping h_v3 h_v4 hinv2 s2 v3 v4
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v2 dropping h_a0 h_v1 v1
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v3 dropping h_v2 hinv1 s1 v2
  store_step with ih.eo__24smtx_5ftypeof_5fbv_5fop_5f2 s2 v3 v4 _ _ hinv2 h64 (hG.rem hrem) h_v3 h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying dropping h_v3 h_v4 hinv2 s2 v3 v4
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v2 dropping h_a0 h_v1 v1
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v3 dropping h_v2 hinv1 s1 v2
  store_step with ih.eo__24smtx_5ftypeof_5fbv_5fop_5f2 s2 v3 v4 _ _ hinv2 h64 (hG.rem hrem) h_v3 h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying dropping h_v3 h_v4 hinv2 s2 v3 v4
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v2 dropping h_a0 h_v1 v1
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v3 dropping h_v2 hinv1 s1 v2
  store_step with ih.eo__24smtx_5ftypeof_5fbv_5fop_5f2 s2 v3 v4 _ _ hinv2 h64 (hG.rem hrem) h_v3 h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying dropping h_v3 h_v4 hinv2 s2 v3 v4
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v2 dropping h_a0 h_v1 v1
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v3 dropping h_v2 hinv1 s1 v2
  store_step with ih.eo__24smtx_5ftypeof_5fbv_5fop_5f2 s2 v3 v4 _ _ hinv2 h64 (hG.rem hrem) h_v3 h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying dropping h_v3 h_v4 hinv2 s2 v3 v4
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v2 dropping h_a0 h_v1 v1
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v3 dropping h_v2 hinv1 s1 v2
  store_step with ih.eo__24smtx_5ftypeof_5fbv_5fop_5f2 s2 v3 v4 _ _ hinv2 h64 (hG.rem hrem) h_v3 h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying dropping h_v3 h_v4 hinv2 s2 v3 v4
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v2 dropping h_a0 h_v1 v1
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v3 dropping h_v2 hinv1 s1 v2
  store_step with ih.eo__24smtx_5ftypeof_5fbv_5fop_5f2 s2 v3 v4 _ _ hinv2 h64 (hG.rem hrem) h_v3 h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying dropping h_v3 h_v4 hinv2 s2 v3 v4
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v2 dropping h_a0 h_v1 v1
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v3 dropping h_v2 hinv1 s1 v2
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s2 e_v5 (by rw [he_v5]; exact empty_args) hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_v3 h_v4 dropping he_v5 hinv2 e_v5 s2
  store_step with ih.eo__24smtx_5ftypeof_5fbv_5fop_5f2_5fret s3 v3 v4 v5 _ _ _ hinv3 h64 (hG.rem hrem) h_v3 h_v4 h_v5 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying dropping h_v3 h_v4 h_v5 hinv3 s3 v3 v4 v5
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v2 dropping h_a0 h_v1 v1
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v3 dropping h_v2 hinv1 s1 v2
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s2 e_v5 (by rw [he_v5]; exact empty_args) hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_v3 h_v4 dropping he_v5 hinv2 e_v5 s2
  store_step with ih.eo__24smtx_5ftypeof_5fbv_5fop_5f2_5fret s3 v3 v4 v5 _ _ _ hinv3 h64 (hG.rem hrem) h_v3 h_v4 h_v5 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying dropping h_v3 h_v4 h_v5 hinv3 s3 v3 v4 v5
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v2 dropping h_a0 h_v1 v1
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v3 dropping h_v2 hinv1 s1 v2
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s2 e_v5 (by rw [he_v5]; exact empty_args) hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_v3 h_v4 dropping he_v5 hinv2 e_v5 s2
  store_step with ih.eo__24smtx_5ftypeof_5fbv_5fop_5f2_5fret s3 v3 v4 v5 _ _ _ hinv3 h64 (hG.rem hrem) h_v3 h_v4 h_v5 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying dropping h_v3 h_v4 h_v5 hinv3 s3 v3 v4 v5
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v2 dropping h_a0 h_v1 v1
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v3 dropping h_v2 hinv1 s1 v2
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s2 e_v5 (by rw [he_v5]; exact empty_args) hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_v3 h_v4 dropping he_v5 hinv2 e_v5 s2
  store_step with ih.eo__24smtx_5ftypeof_5fbv_5fop_5f2_5fret s3 v3 v4 v5 _ _ _ hinv3 h64 (hG.rem hrem) h_v3 h_v4 h_v5 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying dropping h_v3 h_v4 h_v5 hinv3 s3 v3 v4 v5
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v2 dropping h_a0 h_v1 v1
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v3 dropping h_v2 hinv1 s1 v2
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s2 e_v5 (by rw [he_v5]; exact empty_args) hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_v3 h_v4 dropping he_v5 hinv2 e_v5 s2
  store_step with ih.eo__24smtx_5ftypeof_5fbv_5fop_5f2_5fret s3 v3 v4 v5 _ _ _ hinv3 h64 (hG.rem hrem) h_v3 h_v4 h_v5 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying dropping h_v3 h_v4 h_v5 hinv3 s3 v3 v4 v5
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v2 dropping h_a0 h_v1 v1
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v3 dropping h_v2 hinv1 s1 v2
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s2 e_v5 (by rw [he_v5]; exact empty_args) hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_v3 h_v4 dropping he_v5 hinv2 e_v5 s2
  store_step with ih.eo__24smtx_5ftypeof_5fbv_5fop_5f2_5fret s3 v3 v4 v5 _ _ _ hinv3 h64 (hG.rem hrem) h_v3 h_v4 h_v5 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying dropping h_v3 h_v4 h_v5 hinv3 s3 v3 v4 v5
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v2 dropping h_a0 h_v1 v1
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v3 dropping h_v2 hinv1 s1 v2
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s2 e_v5 (by rw [he_v5]; exact empty_args) hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_v3 h_v4 dropping he_v5 hinv2 e_v5 s2
  store_step with ih.eo__24smtx_5ftypeof_5fbv_5fop_5f2_5fret s3 v3 v4 v5 _ _ _ hinv3 h64 (hG.rem hrem) h_v3 h_v4 h_v5 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying dropping h_v3 h_v4 h_v5 hinv3 s3 v3 v4 v5
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v2 dropping h_a0 h_v1 v1
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v3 dropping h_v2 hinv1 s1 v2
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s2 e_v5 (by rw [he_v5]; exact empty_args) hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_v3 h_v4 dropping he_v5 hinv2 e_v5 s2
  store_step with ih.eo__24smtx_5ftypeof_5fbv_5fop_5f2_5fret s3 v3 v4 v5 _ _ _ hinv3 h64 (hG.rem hrem) h_v3 h_v4 h_v5 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying dropping h_v3 h_v4 h_v5 hinv3 s3 v3 v4 v5
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v2 dropping h_a0 h_v1 v1
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v3 dropping h_v2 hinv1 s1 v2
  store_step with ih.eo__24smtx_5ftypeof_5fbv_5fop_5f2 s2 v3 v4 _ _ hinv2 h64 (hG.rem hrem) h_v3 h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying dropping h_v3 h_v4 hinv2 s2 v3 v4
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v2 dropping h_a0 h_v1 v1
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v3 dropping h_v2 hinv1 s1 v2
  store_step with ih.eo__24smtx_5ftypeof_5fbv_5fop_5f2 s2 v3 v4 _ _ hinv2 h64 (hG.rem hrem) h_v3 h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying dropping h_v3 h_v4 hinv2 s2 v3 v4
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v2 dropping h_a0 h_v1 v1
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v3 dropping h_v2 hinv1 s1 v2
  store_step with ih.eo__24smtx_5ftypeof_5fbv_5fop_5f2 s2 v3 v4 _ _ hinv2 h64 (hG.rem hrem) h_v3 h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying dropping h_v3 h_v4 hinv2 s2 v3 v4
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
  store_step with ih.eo__24smtx_5ftypeof s v2 _ hinv h64 hrem h_v2 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v1 dropping h_a0 h_v2 v2
  store_step with ih.eo__24smtx_5ftypeof_5fzero_5fextend s1 v1 v3 _ _ hinv1 h64 (hG.rem hrem) h_v1 h_v3 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying dropping h_v1 h_v3 hinv1 s1 v1 v3
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
  store_step with ih.eo__24smtx_5ftypeof s v2 _ hinv h64 hrem h_v2 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v1 dropping h_a0 h_v2 v2
  store_step with ih.eo__24smtx_5ftypeof_5fsign_5fextend s1 v1 v3 _ _ hinv1 h64 (hG.rem hrem) h_v1 h_v3 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying dropping h_v1 h_v3 hinv1 s1 v1 v3
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
  store_step with ih.eo__24smtx_5ftypeof s v2 _ hinv h64 hrem h_v2 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v1 dropping h_a0 h_v2 v2
  store_step with ih.eo__24smtx_5ftypeof_5frotate_5fleft s1 v1 v3 _ _ hinv1 h64 (hG.rem hrem) h_v1 h_v3 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying dropping h_v1 h_v3 hinv1 s1 v1 v3
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
  store_step with ih.eo__24smtx_5ftypeof s v2 _ hinv h64 hrem h_v2 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v1 dropping h_a0 h_v2 v2
  store_step with ih.eo__24smtx_5ftypeof_5frotate_5fright s1 v1 v3 _ _ hinv1 h64 (hG.rem hrem) h_v1 h_v3 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying dropping h_v1 h_v3 hinv1 s1 v1 v3
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v2 dropping h_a0 h_v1 v1
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v3 dropping h_v2 hinv1 s1 v2
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s2 e_v5 (by rw [he_v5]; exact empty_args) hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_v3 h_v4 dropping he_v5 hinv2 e_v5 s2
  store_step with ih.eo__24smtx_5ftypeof_5fbv_5fop_5f2_5fret s3 v3 v4 v5 _ _ _ hinv3 h64 (hG.rem hrem) h_v3 h_v4 h_v5 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying dropping h_v3 h_v4 h_v5 hinv3 s3 v3 v4 v5
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying dropping h_a0 h_v1 v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s1 e_v3 (by rw [he_v3]; exact empty_args) hinv1 h64 as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying h_v2 dropping he_v3 hinv1 e_v3 s1
  store_step with ih.eo__24smtx_5ftypeof_5fbv_5fop_5f1_5fret s2 v2 v3 _ _ hinv2 h64 (hG.rem hrem) h_v2 h_v3 as ⟨v4, s3, hinv3, h_v4⟩ growing hG carrying dropping h_v2 h_v3 hinv2 s2 v2 v3
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v2 dropping h_a0 h_v1 v1
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v3 dropping h_v2 hinv1 s1 v2
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s2 e_v5 (by rw [he_v5]; exact empty_args) hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_v3 h_v4 dropping he_v5 hinv2 e_v5 s2
  store_step with ih.eo__24smtx_5ftypeof_5fbv_5fop_5f2_5fret s3 v3 v4 v5 _ _ _ hinv3 h64 (hG.rem hrem) h_v3 h_v4 h_v5 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying dropping h_v3 h_v4 h_v5 hinv3 s3 v3 v4 v5
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v2 dropping h_a0 h_v1 v1
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v3 dropping h_v2 hinv1 s1 v2
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s2 e_v5 (by rw [he_v5]; exact empty_args) hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_v3 h_v4 dropping he_v5 hinv2 e_v5 s2
  store_step with ih.eo__24smtx_5ftypeof_5fbv_5fop_5f2_5fret s3 v3 v4 v5 _ _ _ hinv3 h64 (hG.rem hrem) h_v3 h_v4 h_v5 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying dropping h_v3 h_v4 h_v5 hinv3 s3 v3 v4 v5
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v2 dropping h_a0 h_v1 v1
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v3 dropping h_v2 hinv1 s1 v2
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s2 e_v5 (by rw [he_v5]; exact empty_args) hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_v3 h_v4 dropping he_v5 hinv2 e_v5 s2
  store_step with ih.eo__24smtx_5ftypeof_5fbv_5fop_5f2_5fret s3 v3 v4 v5 _ _ _ hinv3 h64 (hG.rem hrem) h_v3 h_v4 h_v5 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying dropping h_v3 h_v4 h_v5 hinv3 s3 v3 v4 v5
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v2 dropping h_a0 h_v1 v1
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v3 dropping h_v2 hinv1 s1 v2
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s2 e_v5 (by rw [he_v5]; exact empty_args) hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_v3 h_v4 dropping he_v5 hinv2 e_v5 s2
  store_step with ih.eo__24smtx_5ftypeof_5fbv_5fop_5f2_5fret s3 v3 v4 v5 _ _ _ hinv3 h64 (hG.rem hrem) h_v3 h_v4 h_v5 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying dropping h_v3 h_v4 h_v5 hinv3 s3 v3 v4 v5
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v2 dropping h_a0 h_v1 v1
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v3 dropping h_v2 hinv1 s1 v2
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s2 e_v5 (by rw [he_v5]; exact empty_args) hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_v3 h_v4 dropping he_v5 hinv2 e_v5 s2
  store_step with ih.eo__24smtx_5ftypeof_5fbv_5fop_5f2_5fret s3 v3 v4 v5 _ _ _ hinv3 h64 (hG.rem hrem) h_v3 h_v4 h_v5 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying dropping h_v3 h_v4 h_v5 hinv3 s3 v3 v4 v5
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v2 dropping h_a0 h_v1 v1
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v3 dropping h_v2 hinv1 s1 v2
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s2 e_v5 (by rw [he_v5]; exact empty_args) hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_v3 h_v4 dropping he_v5 hinv2 e_v5 s2
  store_step with ih.eo__24smtx_5ftypeof_5fbv_5fop_5f2_5fret s3 v3 v4 v5 _ _ _ hinv3 h64 (hG.rem hrem) h_v3 h_v4 h_v5 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying dropping h_v3 h_v4 h_v5 hinv3 s3 v3 v4 v5
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
  store_step with CtorSpec.eo__24emb_5ftsm_2eSeq.construct s e_v2 (by rw [he_v2]; rfl) h_v1 hinv h64 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying h_v1 dropping h_a0 he_v2 e_v2
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eSeq.construct s1 e_v3 (by rw [he_v3]; rfl) h_v1 hinv1 h64 as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying h_v2 dropping h_v1 he_v3 hinv1 e_v3 s1 v1
  store_step with ih.eo__24smtx_5ftypeof_5fguard_5fwf s2 v2 v3 _ _ hinv2 h64 (hG.rem hrem) h_v2 h_v3 as ⟨v4, s3, hinv3, h_v4⟩ growing hG carrying dropping h_v2 h_v3 hinv2 s2 v2 v3
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying dropping h_a0 h_v1 v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eInt.construct s1 e_v3 (by rw [he_v3]; exact empty_args) hinv1 h64 as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying h_v2 dropping he_v3 hinv1 e_v3 s1
  store_step with ih.eo__24smtx_5ftypeof_5fseq_5fop_5f1_5fret s2 v2 v3 _ _ hinv2 h64 (hG.rem hrem) h_v2 h_v3 as ⟨v4, s3, hinv3, h_v4⟩ growing hG carrying dropping h_v2 h_v3 hinv2 s2 v2 v3
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v2 dropping h_a0 h_v1 v1
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v3 dropping h_v2 hinv1 s1 v2
  store_step with ih.eo__24smtx_5ftypeof_5fseq_5fop_5f2 s2 v3 v4 _ _ hinv2 h64 (hG.rem hrem) h_v3 h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying dropping h_v3 h_v4 hinv2 s2 v3 v4
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v4, s1, hinv1, h_v4⟩ growing hG carrying h_v2 h_v3 dropping h_a0 h_v1 v1
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v5, s2, hinv2, h_v5⟩ growing hG carrying h_v3 h_v4 dropping h_v2 hinv1 s1 v2
  store_step with ih.eo__24smtx_5ftypeof s2 v3 _ hinv2 h64 (hG.rem hrem) h_v3 as ⟨v6, s3, hinv3, h_v6⟩ growing hG carrying h_v4 h_v5 dropping h_v3 hinv2 s2 v3
  store_step with ih.eo__24smtx_5ftypeof_5fstr_2esubstr s3 v4 v5 v6 _ _ _ hinv3 h64 (hG.rem hrem) h_v4 h_v5 h_v6 as ⟨v7, s4, hinv4, h_v7⟩ growing hG carrying dropping h_v4 h_v5 h_v6 hinv3 s3 v4 v5 v6
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v2 dropping h_a0 h_v1 v1
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v3 dropping h_v2 hinv1 s1 v2
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s2 e_v5 (by rw [he_v5]; exact empty_args) hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_v3 h_v4 dropping he_v5 hinv2 e_v5 s2
  store_step with ih.eo__24smtx_5ftypeof_5fseq_5fop_5f2_5fret s3 v3 v4 v5 _ _ _ hinv3 h64 (hG.rem hrem) h_v3 h_v4 h_v5 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying dropping h_v3 h_v4 h_v5 hinv3 s3 v3 v4 v5
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v4, s1, hinv1, h_v4⟩ growing hG carrying h_v2 h_v3 dropping h_a0 h_v1 v1
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v5, s2, hinv2, h_v5⟩ growing hG carrying h_v3 h_v4 dropping h_v2 hinv1 s1 v2
  store_step with ih.eo__24smtx_5ftypeof s2 v3 _ hinv2 h64 (hG.rem hrem) h_v3 as ⟨v6, s3, hinv3, h_v6⟩ growing hG carrying h_v4 h_v5 dropping h_v3 hinv2 s2 v3
  store_step with ih.eo__24smtx_5ftypeof_5fseq_5fop_5f3 s3 v4 v5 v6 _ _ _ hinv3 h64 (hG.rem hrem) h_v4 h_v5 h_v6 as ⟨v7, s4, hinv4, h_v7⟩ growing hG carrying dropping h_v4 h_v5 h_v6 hinv3 s3 v4 v5 v6
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v4, s1, hinv1, h_v4⟩ growing hG carrying h_v2 h_v3 dropping h_a0 h_v1 v1
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v5, s2, hinv2, h_v5⟩ growing hG carrying h_v3 h_v4 dropping h_v2 hinv1 s1 v2
  store_step with ih.eo__24smtx_5ftypeof s2 v3 _ hinv2 h64 (hG.rem hrem) h_v3 as ⟨v6, s3, hinv3, h_v6⟩ growing hG carrying h_v4 h_v5 dropping h_v3 hinv2 s2 v3
  store_step with ih.eo__24smtx_5ftypeof_5fstr_2eindexof s3 v4 v5 v6 _ _ _ hinv3 h64 (hG.rem hrem) h_v4 h_v5 h_v6 as ⟨v7, s4, hinv4, h_v7⟩ growing hG carrying dropping h_v4 h_v5 h_v6 hinv3 s3 v4 v5 v6
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v2 dropping h_a0 h_v1 v1
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v3 dropping h_v2 hinv1 s1 v2
  store_step with ih.eo__24smtx_5ftypeof_5fstr_2eat s2 v3 v4 _ _ hinv2 h64 (hG.rem hrem) h_v3 h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying dropping h_v3 h_v4 hinv2 s2 v3 v4
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v2 dropping h_a0 h_v1 v1
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v3 dropping h_v2 hinv1 s1 v2
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s2 e_v5 (by rw [he_v5]; exact empty_args) hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_v3 h_v4 dropping he_v5 hinv2 e_v5 s2
  store_step with ih.eo__24smtx_5ftypeof_5fseq_5fop_5f2_5fret s3 v3 v4 v5 _ _ _ hinv3 h64 (hG.rem hrem) h_v3 h_v4 h_v5 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying dropping h_v3 h_v4 h_v5 hinv3 s3 v3 v4 v5
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v2 dropping h_a0 h_v1 v1
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v3 dropping h_v2 hinv1 s1 v2
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s2 e_v5 (by rw [he_v5]; exact empty_args) hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_v3 h_v4 dropping he_v5 hinv2 e_v5 s2
  store_step with ih.eo__24smtx_5ftypeof_5fseq_5fop_5f2_5fret s3 v3 v4 v5 _ _ _ hinv3 h64 (hG.rem hrem) h_v3 h_v4 h_v5 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying dropping h_v3 h_v4 h_v5 hinv3 s3 v3 v4 v5
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying dropping h_a0 h_v1 v1
  store_step with ih.eo__24smtx_5ftypeof_5fseq_5fop_5f1 s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying dropping h_v2 hinv1 s1 v2
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v4, s1, hinv1, h_v4⟩ growing hG carrying h_v2 h_v3 dropping h_a0 h_v1 v1
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v5, s2, hinv2, h_v5⟩ growing hG carrying h_v3 h_v4 dropping h_v2 hinv1 s1 v2
  store_step with ih.eo__24smtx_5ftypeof s2 v3 _ hinv2 h64 (hG.rem hrem) h_v3 as ⟨v6, s3, hinv3, h_v6⟩ growing hG carrying h_v4 h_v5 dropping h_v3 hinv2 s2 v3
  store_step with ih.eo__24smtx_5ftypeof_5fstr_2eupdate s3 v4 v5 v6 _ _ _ hinv3 h64 (hG.rem hrem) h_v4 h_v5 h_v6 as ⟨v7, s4, hinv4, h_v7⟩ growing hG carrying dropping h_v4 h_v5 h_v6 hinv3 s3 v4 v5 v6
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying dropping h_a0 h_v1 v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eChar.construct s1 e_v3 (by rw [he_v3]; exact empty_args) hinv1 h64 as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying h_v2 dropping he_v3 hinv1 e_v3 s1
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eSeq.construct s2 e_v4 (by rw [he_v4]; rfl) h_v3 hinv2 h64 as ⟨v4, s3, hinv3, h_v4⟩ growing hG carrying h_v2 dropping h_v3 he_v4 hinv2 e_v4 s2 v3
  step as ⟨e_v5, he_v5⟩
  store_step with Store.native_spec_Teq s3 e_v5 (by rw [he_v5]; rfl) h_v2 h_v4 hinv3 h64 as ⟨v5, s4, hinv4, h_v5⟩ growing hG carrying dropping h_v2 h_v4 he_v5 hinv3 e_v5 s3 v2 v4
  have h_ite_v9 := (show if_26_eo__24smtx_5ftypeof s4 v5 ⦃ r s' => s'.Inv ∧ s4.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_26_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s4
    rcases Store.boolean_value_native h_v5 with ⟨hx_6, hbv_6⟩ | ⟨hx_6, hbv_6⟩
    · ite_branch hbv_6
      step as ⟨e_v6, he_v6⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eChar.construct s4 e_v6 (by rw [he_v6]; exact empty_args) hinv4 h64 as ⟨v6, s5, hinv5, h_v6⟩ growing hG carrying dropping h_v5 he_v6 e_v6 v5
      step as ⟨e_v7, he_v7⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eSeq.construct s5 e_v7 (by rw [he_v7]; rfl) h_v6 hinv5 h64 as ⟨v7, s6, hinv6, h_v7⟩ growing hG carrying dropping h_v6 he_v7 e_v7 v6
      ite_done hinv6 hG with (native_ite_true_rep _ hx_6 h_v7)
    · ite_branch hbv_6
      step as ⟨e_v8, he_v8⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s4 e_v8 (by rw [he_v8]; exact empty_args) hinv4 h64 as ⟨v8, s5, hinv5, h_v8⟩ growing hG carrying dropping h_v5 he_v8 hinv4 e_v8 s4 v5
      ite_done hinv5 hG with (native_ite_false_rep _ hx_6 h_v8))
  store_step with h_ite_v9 as ⟨v9, s5, hinv5, h_v9⟩ growing hG carrying dropping h_ite_v9 h_v5 hinv4 s4 v5
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying dropping h_a0 h_v1 v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eChar.construct s1 e_v3 (by rw [he_v3]; exact empty_args) hinv1 h64 as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying h_v2 dropping he_v3 hinv1 e_v3 s1
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eSeq.construct s2 e_v4 (by rw [he_v4]; rfl) h_v3 hinv2 h64 as ⟨v4, s3, hinv3, h_v4⟩ growing hG carrying h_v2 dropping h_v3 he_v4 hinv2 e_v4 s2 v3
  step as ⟨e_v5, he_v5⟩
  store_step with Store.native_spec_Teq s3 e_v5 (by rw [he_v5]; rfl) h_v2 h_v4 hinv3 h64 as ⟨v5, s4, hinv4, h_v5⟩ growing hG carrying dropping h_v2 h_v4 he_v5 hinv3 e_v5 s3 v2 v4
  have h_ite_v9 := (show if_27_eo__24smtx_5ftypeof s4 v5 ⦃ r s' => s'.Inv ∧ s4.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_27_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s4
    rcases Store.boolean_value_native h_v5 with ⟨hx_6, hbv_6⟩ | ⟨hx_6, hbv_6⟩
    · ite_branch hbv_6
      step as ⟨e_v6, he_v6⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eChar.construct s4 e_v6 (by rw [he_v6]; exact empty_args) hinv4 h64 as ⟨v6, s5, hinv5, h_v6⟩ growing hG carrying dropping h_v5 he_v6 e_v6 v5
      step as ⟨e_v7, he_v7⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eSeq.construct s5 e_v7 (by rw [he_v7]; rfl) h_v6 hinv5 h64 as ⟨v7, s6, hinv6, h_v7⟩ growing hG carrying dropping h_v6 he_v7 e_v7 v6
      ite_done hinv6 hG with (native_ite_true_rep _ hx_6 h_v7)
    · ite_branch hbv_6
      step as ⟨e_v8, he_v8⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s4 e_v8 (by rw [he_v8]; exact empty_args) hinv4 h64 as ⟨v8, s5, hinv5, h_v8⟩ growing hG carrying dropping h_v5 he_v8 hinv4 e_v8 s4 v5
      ite_done hinv5 hG with (native_ite_false_rep _ hx_6 h_v8))
  store_step with h_ite_v9 as ⟨v9, s5, hinv5, h_v9⟩ growing hG carrying dropping h_ite_v9 h_v5 hinv4 s4 v5
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying dropping h_a0 h_v1 v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eChar.construct s1 e_v3 (by rw [he_v3]; exact empty_args) hinv1 h64 as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying h_v2 dropping he_v3 hinv1 e_v3 s1
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eSeq.construct s2 e_v4 (by rw [he_v4]; rfl) h_v3 hinv2 h64 as ⟨v4, s3, hinv3, h_v4⟩ growing hG carrying h_v2 dropping h_v3 he_v4 hinv2 e_v4 s2 v3
  step as ⟨e_v5, he_v5⟩
  store_step with Store.native_spec_Teq s3 e_v5 (by rw [he_v5]; rfl) h_v2 h_v4 hinv3 h64 as ⟨v5, s4, hinv4, h_v5⟩ growing hG carrying dropping h_v2 h_v4 he_v5 hinv3 e_v5 s3 v2 v4
  have h_ite_v8 := (show if_28_eo__24smtx_5ftypeof s4 v5 ⦃ r s' => s'.Inv ∧ s4.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_28_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s4
    rcases Store.boolean_value_native h_v5 with ⟨hx_6, hbv_6⟩ | ⟨hx_6, hbv_6⟩
    · ite_branch hbv_6
      step as ⟨e_v6, he_v6⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eInt.construct s4 e_v6 (by rw [he_v6]; exact empty_args) hinv4 h64 as ⟨v6, s5, hinv5, h_v6⟩ growing hG carrying dropping h_v5 he_v6 e_v6 v5
      ite_done hinv5 hG with (native_ite_true_rep _ hx_6 h_v6)
    · ite_branch hbv_6
      step as ⟨e_v7, he_v7⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s4 e_v7 (by rw [he_v7]; exact empty_args) hinv4 h64 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying dropping h_v5 he_v7 hinv4 e_v7 s4 v5
      ite_done hinv5 hG with (native_ite_false_rep _ hx_6 h_v7))
  store_step with h_ite_v8 as ⟨v8, s5, hinv5, h_v8⟩ growing hG carrying dropping h_ite_v8 h_v5 hinv4 s4 v5
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying dropping h_a0 h_v1 v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eInt.construct s1 e_v3 (by rw [he_v3]; exact empty_args) hinv1 h64 as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying h_v2 dropping he_v3 hinv1 e_v3 s1
  step as ⟨e_v4, he_v4⟩
  store_step with Store.native_spec_Teq s2 e_v4 (by rw [he_v4]; rfl) h_v2 h_v3 hinv2 h64 as ⟨v4, s3, hinv3, h_v4⟩ growing hG carrying dropping h_v2 h_v3 he_v4 hinv2 e_v4 s2 v2 v3
  have h_ite_v8 := (show if_29_eo__24smtx_5ftypeof s3 v4 ⦃ r s' => s'.Inv ∧ s3.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_29_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s3
    rcases Store.boolean_value_native h_v4 with ⟨hx_5, hbv_5⟩ | ⟨hx_5, hbv_5⟩
    · ite_branch hbv_5
      step as ⟨e_v5, he_v5⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eChar.construct s3 e_v5 (by rw [he_v5]; exact empty_args) hinv3 h64 as ⟨v5, s4, hinv4, h_v5⟩ growing hG carrying dropping h_v4 he_v5 e_v5 v4
      step as ⟨e_v6, he_v6⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eSeq.construct s4 e_v6 (by rw [he_v6]; rfl) h_v5 hinv4 h64 as ⟨v6, s5, hinv5, h_v6⟩ growing hG carrying dropping h_v5 he_v6 e_v6 v5
      ite_done hinv5 hG with (native_ite_true_rep _ hx_5 h_v6)
    · ite_branch hbv_5
      step as ⟨e_v7, he_v7⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s3 e_v7 (by rw [he_v7]; exact empty_args) hinv3 h64 as ⟨v7, s4, hinv4, h_v7⟩ growing hG carrying dropping h_v4 he_v7 hinv3 e_v7 s3 v4
      ite_done hinv4 hG with (native_ite_false_rep _ hx_5 h_v7))
  store_step with h_ite_v8 as ⟨v8, s4, hinv4, h_v8⟩ growing hG carrying dropping h_ite_v8 h_v4 hinv3 s3 v4
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying dropping h_a0 h_v1 v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eChar.construct s1 e_v3 (by rw [he_v3]; exact empty_args) hinv1 h64 as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying h_v2 dropping he_v3 hinv1 e_v3 s1
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eSeq.construct s2 e_v4 (by rw [he_v4]; rfl) h_v3 hinv2 h64 as ⟨v4, s3, hinv3, h_v4⟩ growing hG carrying h_v2 dropping h_v3 he_v4 hinv2 e_v4 s2 v3
  step as ⟨e_v5, he_v5⟩
  store_step with Store.native_spec_Teq s3 e_v5 (by rw [he_v5]; rfl) h_v2 h_v4 hinv3 h64 as ⟨v5, s4, hinv4, h_v5⟩ growing hG carrying dropping h_v2 h_v4 he_v5 hinv3 e_v5 s3 v2 v4
  have h_ite_v8 := (show if_30_eo__24smtx_5ftypeof s4 v5 ⦃ r s' => s'.Inv ∧ s4.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_30_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s4
    rcases Store.boolean_value_native h_v5 with ⟨hx_6, hbv_6⟩ | ⟨hx_6, hbv_6⟩
    · ite_branch hbv_6
      step as ⟨e_v6, he_v6⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s4 e_v6 (by rw [he_v6]; exact empty_args) hinv4 h64 as ⟨v6, s5, hinv5, h_v6⟩ growing hG carrying dropping h_v5 he_v6 e_v6 v5
      ite_done hinv5 hG with (native_ite_true_rep _ hx_6 h_v6)
    · ite_branch hbv_6
      step as ⟨e_v7, he_v7⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s4 e_v7 (by rw [he_v7]; exact empty_args) hinv4 h64 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying dropping h_v5 he_v7 hinv4 e_v7 s4 v5
      ite_done hinv5 hG with (native_ite_false_rep _ hx_6 h_v7))
  store_step with h_ite_v8 as ⟨v8, s5, hinv5, h_v8⟩ growing hG carrying dropping h_ite_v8 h_v5 hinv4 s4 v5
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying dropping h_a0 h_v1 v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eChar.construct s1 e_v3 (by rw [he_v3]; exact empty_args) hinv1 h64 as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying h_v2 dropping he_v3 hinv1 e_v3 s1
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eSeq.construct s2 e_v4 (by rw [he_v4]; rfl) h_v3 hinv2 h64 as ⟨v4, s3, hinv3, h_v4⟩ growing hG carrying h_v2 dropping h_v3 he_v4 hinv2 e_v4 s2 v3
  step as ⟨e_v5, he_v5⟩
  store_step with Store.native_spec_Teq s3 e_v5 (by rw [he_v5]; rfl) h_v2 h_v4 hinv3 h64 as ⟨v5, s4, hinv4, h_v5⟩ growing hG carrying dropping h_v2 h_v4 he_v5 hinv3 e_v5 s3 v2 v4
  have h_ite_v8 := (show if_31_eo__24smtx_5ftypeof s4 v5 ⦃ r s' => s'.Inv ∧ s4.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_31_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s4
    rcases Store.boolean_value_native h_v5 with ⟨hx_6, hbv_6⟩ | ⟨hx_6, hbv_6⟩
    · ite_branch hbv_6
      step as ⟨e_v6, he_v6⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eInt.construct s4 e_v6 (by rw [he_v6]; exact empty_args) hinv4 h64 as ⟨v6, s5, hinv5, h_v6⟩ growing hG carrying dropping h_v5 he_v6 e_v6 v5
      ite_done hinv5 hG with (native_ite_true_rep _ hx_6 h_v6)
    · ite_branch hbv_6
      step as ⟨e_v7, he_v7⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s4 e_v7 (by rw [he_v7]; exact empty_args) hinv4 h64 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying dropping h_v5 he_v7 hinv4 e_v7 s4 v5
      ite_done hinv5 hG with (native_ite_false_rep _ hx_6 h_v7))
  store_step with h_ite_v8 as ⟨v8, s5, hinv5, h_v8⟩ growing hG carrying dropping h_ite_v8 h_v5 hinv4 s4 v5
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying dropping h_a0 h_v1 v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eInt.construct s1 e_v3 (by rw [he_v3]; exact empty_args) hinv1 h64 as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying h_v2 dropping he_v3 hinv1 e_v3 s1
  step as ⟨e_v4, he_v4⟩
  store_step with Store.native_spec_Teq s2 e_v4 (by rw [he_v4]; rfl) h_v2 h_v3 hinv2 h64 as ⟨v4, s3, hinv3, h_v4⟩ growing hG carrying dropping h_v2 h_v3 he_v4 hinv2 e_v4 s2 v2 v3
  have h_ite_v8 := (show if_32_eo__24smtx_5ftypeof s3 v4 ⦃ r s' => s'.Inv ∧ s3.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_32_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s3
    rcases Store.boolean_value_native h_v4 with ⟨hx_5, hbv_5⟩ | ⟨hx_5, hbv_5⟩
    · ite_branch hbv_5
      step as ⟨e_v5, he_v5⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eChar.construct s3 e_v5 (by rw [he_v5]; exact empty_args) hinv3 h64 as ⟨v5, s4, hinv4, h_v5⟩ growing hG carrying dropping h_v4 he_v5 e_v5 v4
      step as ⟨e_v6, he_v6⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eSeq.construct s4 e_v6 (by rw [he_v6]; rfl) h_v5 hinv4 h64 as ⟨v6, s5, hinv5, h_v6⟩ growing hG carrying dropping h_v5 he_v6 e_v6 v5
      ite_done hinv5 hG with (native_ite_true_rep _ hx_5 h_v6)
    · ite_branch hbv_5
      step as ⟨e_v7, he_v7⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s3 e_v7 (by rw [he_v7]; exact empty_args) hinv3 h64 as ⟨v7, s4, hinv4, h_v7⟩ growing hG carrying dropping h_v4 he_v7 hinv3 e_v7 s3 v4
      ite_done hinv4 hG with (native_ite_false_rep _ hx_5 h_v7))
  store_step with h_ite_v8 as ⟨v8, s4, hinv4, h_v8⟩ growing hG carrying dropping h_ite_v8 h_v4 hinv3 s3 v4
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v2 dropping h_a0 h_v1 v1
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eChar.construct s1 e_v4 (by rw [he_v4]; exact empty_args) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v2 h_v3 dropping he_v4 hinv1 e_v4 s1
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eSeq.construct s2 e_v5 (by rw [he_v5]; rfl) h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_v2 h_v3 dropping h_v4 he_v5 hinv2 e_v5 s2 v4
  step as ⟨e_v6, he_v6⟩
  store_step with Store.native_spec_Teq s3 e_v6 (by rw [he_v6]; rfl) h_v3 h_v5 hinv3 h64 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_v2 dropping h_v3 h_v5 he_v6 hinv3 e_v6 s3 v3 v5
  have h_ite_v15 := (show if_34_eo__24smtx_5ftypeof s4 v6 v2 ⦃ r s' => s'.Inv ∧ s4.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_34_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s4
    rcases Store.boolean_value_native h_v6 with ⟨hx_7, hbv_7⟩ | ⟨hx_7, hbv_7⟩
    · ite_branch hbv_7
      store_step with ih.eo__24smtx_5ftypeof s4 v2 _ hinv4 h64 (hG.rem hrem) h_v2 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying dropping h_v2 h_v6 v2 v6
      step as ⟨e_v8, he_v8⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eChar.construct s5 e_v8 (by rw [he_v8]; exact empty_args) hinv5 h64 as ⟨v8, s6, hinv6, h_v8⟩ growing hG carrying h_v7 dropping he_v8 e_v8
      step as ⟨e_v9, he_v9⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eSeq.construct s6 e_v9 (by rw [he_v9]; rfl) h_v8 hinv6 h64 as ⟨v9, s7, hinv7, h_v9⟩ growing hG carrying h_v7 dropping h_v8 he_v9 hinv6 e_v9 s6 v8
      step as ⟨e_v10, he_v10⟩
      store_step with Store.native_spec_Teq s7 e_v10 (by rw [he_v10]; rfl) h_v7 h_v9 hinv7 h64 as ⟨v10, s8, hinv8, h_v10⟩ growing hG carrying dropping h_v7 h_v9 he_v10 hinv7 e_v10 s7 v7 v9
      have h_ite_v13 := (show if_33_eo__24smtx_5ftypeof s8 v10 ⦃ r s' => s'.Inv ∧ s8.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_33_eo__24smtx_5ftypeof
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s8
        rcases Store.boolean_value_native h_v10 with ⟨hx_11, hbv_11⟩ | ⟨hx_11, hbv_11⟩
        · ite_branch hbv_11
          step as ⟨e_v11, he_v11⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s8 e_v11 (by rw [he_v11]; exact empty_args) hinv8 h64 as ⟨v11, s9, hinv9, h_v11⟩ growing hG carrying dropping h_v10 he_v11 e_v11 v10
          ite_done hinv9 hG with (native_ite_true_rep _ hx_11 h_v11)
        · ite_branch hbv_11
          step as ⟨e_v12, he_v12⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s8 e_v12 (by rw [he_v12]; exact empty_args) hinv8 h64 as ⟨v12, s9, hinv9, h_v12⟩ growing hG carrying dropping h_v10 he_v12 hinv8 e_v12 s8 v10
          ite_done hinv9 hG with (native_ite_false_rep _ hx_11 h_v12))
      store_step with h_ite_v13 as ⟨v13, s9, hinv9, h_v13⟩ growing hG carrying dropping h_ite_v13 h_v10 hinv8 s8 v10
      ite_done hinv9 hG with (native_ite_true_rep _ hx_7 h_v13)
    · ite_branch hbv_7
      step as ⟨e_v14, he_v14⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s4 e_v14 (by rw [he_v14]; exact empty_args) hinv4 h64 as ⟨v14, s5, hinv5, h_v14⟩ growing hG carrying dropping h_v2 h_v6 he_v14 hinv4 e_v14 s4 v2 v6
      ite_done hinv5 hG with (native_ite_false_rep _ hx_7 h_v14))
  store_step with h_ite_v15 as ⟨v15, s5, hinv5, h_v15⟩ growing hG carrying dropping h_ite_v15 h_v2 h_v6 hinv4 s4 v2 v6
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v2 dropping h_a0 h_v1 v1
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eChar.construct s1 e_v4 (by rw [he_v4]; exact empty_args) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v2 h_v3 dropping he_v4 hinv1 e_v4 s1
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eSeq.construct s2 e_v5 (by rw [he_v5]; rfl) h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_v2 h_v3 dropping h_v4 he_v5 hinv2 e_v5 s2 v4
  step as ⟨e_v6, he_v6⟩
  store_step with Store.native_spec_Teq s3 e_v6 (by rw [he_v6]; rfl) h_v3 h_v5 hinv3 h64 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_v2 dropping h_v3 h_v5 he_v6 hinv3 e_v6 s3 v3 v5
  have h_ite_v15 := (show if_36_eo__24smtx_5ftypeof s4 v6 v2 ⦃ r s' => s'.Inv ∧ s4.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_36_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s4
    rcases Store.boolean_value_native h_v6 with ⟨hx_7, hbv_7⟩ | ⟨hx_7, hbv_7⟩
    · ite_branch hbv_7
      store_step with ih.eo__24smtx_5ftypeof s4 v2 _ hinv4 h64 (hG.rem hrem) h_v2 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying dropping h_v2 h_v6 v2 v6
      step as ⟨e_v8, he_v8⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eChar.construct s5 e_v8 (by rw [he_v8]; exact empty_args) hinv5 h64 as ⟨v8, s6, hinv6, h_v8⟩ growing hG carrying h_v7 dropping he_v8 e_v8
      step as ⟨e_v9, he_v9⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eSeq.construct s6 e_v9 (by rw [he_v9]; rfl) h_v8 hinv6 h64 as ⟨v9, s7, hinv7, h_v9⟩ growing hG carrying h_v7 dropping h_v8 he_v9 hinv6 e_v9 s6 v8
      step as ⟨e_v10, he_v10⟩
      store_step with Store.native_spec_Teq s7 e_v10 (by rw [he_v10]; rfl) h_v7 h_v9 hinv7 h64 as ⟨v10, s8, hinv8, h_v10⟩ growing hG carrying dropping h_v7 h_v9 he_v10 hinv7 e_v10 s7 v7 v9
      have h_ite_v13 := (show if_35_eo__24smtx_5ftypeof s8 v10 ⦃ r s' => s'.Inv ∧ s8.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_35_eo__24smtx_5ftypeof
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s8
        rcases Store.boolean_value_native h_v10 with ⟨hx_11, hbv_11⟩ | ⟨hx_11, hbv_11⟩
        · ite_branch hbv_11
          step as ⟨e_v11, he_v11⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s8 e_v11 (by rw [he_v11]; exact empty_args) hinv8 h64 as ⟨v11, s9, hinv9, h_v11⟩ growing hG carrying dropping h_v10 he_v11 e_v11 v10
          ite_done hinv9 hG with (native_ite_true_rep _ hx_11 h_v11)
        · ite_branch hbv_11
          step as ⟨e_v12, he_v12⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s8 e_v12 (by rw [he_v12]; exact empty_args) hinv8 h64 as ⟨v12, s9, hinv9, h_v12⟩ growing hG carrying dropping h_v10 he_v12 hinv8 e_v12 s8 v10
          ite_done hinv9 hG with (native_ite_false_rep _ hx_11 h_v12))
      store_step with h_ite_v13 as ⟨v13, s9, hinv9, h_v13⟩ growing hG carrying dropping h_ite_v13 h_v10 hinv8 s8 v10
      ite_done hinv9 hG with (native_ite_true_rep _ hx_7 h_v13)
    · ite_branch hbv_7
      step as ⟨e_v14, he_v14⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s4 e_v14 (by rw [he_v14]; exact empty_args) hinv4 h64 as ⟨v14, s5, hinv5, h_v14⟩ growing hG carrying dropping h_v2 h_v6 he_v14 hinv4 e_v14 s4 v2 v6
      ite_done hinv5 hG with (native_ite_false_rep _ hx_7 h_v14))
  store_step with h_ite_v15 as ⟨v15, s5, hinv5, h_v15⟩ growing hG carrying dropping h_ite_v15 h_v2 h_v6 hinv4 s4 v2 v6
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v4, s1, hinv1, h_v4⟩ growing hG carrying h_v2 h_v3 dropping h_a0 h_v1 v1
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v5, s2, hinv2, h_v5⟩ growing hG carrying h_v3 h_v4 dropping h_v2 hinv1 s1 v2
  store_step with ih.eo__24smtx_5ftypeof s2 v3 _ hinv2 h64 (hG.rem hrem) h_v3 as ⟨v6, s3, hinv3, h_v6⟩ growing hG carrying h_v4 h_v5 dropping h_v3 hinv2 s2 v3
  store_step with ih.eo__24smtx_5ftypeof_5fseq_5fop_5f3 s3 v4 v5 v6 _ _ _ hinv3 h64 (hG.rem hrem) h_v4 h_v5 h_v6 as ⟨v7, s4, hinv4, h_v7⟩ growing hG carrying dropping h_v4 h_v5 h_v6 hinv3 s3 v4 v5 v6
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v4, s1, hinv1, h_v4⟩ growing hG carrying h_v2 h_v3 dropping h_a0 h_v1 v1
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eChar.construct s1 e_v5 (by rw [he_v5]; exact empty_args) hinv1 h64 as ⟨v5, s2, hinv2, h_v5⟩ growing hG carrying h_v2 h_v3 h_v4 dropping he_v5 hinv1 e_v5 s1
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eSeq.construct s2 e_v6 (by rw [he_v6]; rfl) h_v5 hinv2 h64 as ⟨v6, s3, hinv3, h_v6⟩ growing hG carrying h_v2 h_v3 h_v4 dropping h_v5 he_v6 hinv2 e_v6 s2 v5
  step as ⟨e_v7, he_v7⟩
  store_step with Store.native_spec_Teq s3 e_v7 (by rw [he_v7]; rfl) h_v4 h_v6 hinv3 h64 as ⟨v7, s4, hinv4, h_v7⟩ growing hG carrying h_v2 h_v3 dropping h_v4 h_v6 he_v7 hinv3 e_v7 s3 v4 v6
  have h_ite_v22 := (show if_39_eo__24smtx_5ftypeof s4 v7 v2 v3 ⦃ r s' => s'.Inv ∧ s4.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_39_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s4
    rcases Store.boolean_value_native h_v7 with ⟨hx_8, hbv_8⟩ | ⟨hx_8, hbv_8⟩
    · ite_branch hbv_8
      store_step with ih.eo__24smtx_5ftypeof s4 v2 _ hinv4 h64 (hG.rem hrem) h_v2 as ⟨v8, s5, hinv5, h_v8⟩ growing hG carrying h_v3 dropping h_v2 h_v7 v2 v7
      step as ⟨e_v9, he_v9⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eRegLan.construct s5 e_v9 (by rw [he_v9]; exact empty_args) hinv5 h64 as ⟨v9, s6, hinv6, h_v9⟩ growing hG carrying h_v3 h_v8 dropping he_v9 e_v9
      step as ⟨e_v10, he_v10⟩
      store_step with Store.native_spec_Teq s6 e_v10 (by rw [he_v10]; rfl) h_v8 h_v9 hinv6 h64 as ⟨v10, s7, hinv7, h_v10⟩ growing hG carrying h_v3 dropping h_v8 h_v9 he_v10 hinv6 e_v10 s6 v8 v9
      have h_ite_v20 := (show if_38_eo__24smtx_5ftypeof s7 v10 v3 ⦃ r s' => s'.Inv ∧ s7.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_38_eo__24smtx_5ftypeof
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s7
        rcases Store.boolean_value_native h_v10 with ⟨hx_11, hbv_11⟩ | ⟨hx_11, hbv_11⟩
        · ite_branch hbv_11
          store_step with ih.eo__24smtx_5ftypeof s7 v3 _ hinv7 h64 (hG.rem hrem) h_v3 as ⟨v11, s8, hinv8, h_v11⟩ growing hG carrying dropping h_v10 h_v3 v10 v3
          step as ⟨e_v12, he_v12⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eChar.construct s8 e_v12 (by rw [he_v12]; exact empty_args) hinv8 h64 as ⟨v12, s9, hinv9, h_v12⟩ growing hG carrying h_v11 dropping he_v12 e_v12
          step as ⟨e_v13, he_v13⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eSeq.construct s9 e_v13 (by rw [he_v13]; rfl) h_v12 hinv9 h64 as ⟨v13, s10, hinv10, h_v13⟩ growing hG carrying h_v11 dropping h_v12 he_v13 hinv9 e_v13 s9 v12
          step as ⟨e_v14, he_v14⟩
          store_step with Store.native_spec_Teq s10 e_v14 (by rw [he_v14]; rfl) h_v11 h_v13 hinv10 h64 as ⟨v14, s11, hinv11, h_v14⟩ growing hG carrying dropping h_v11 h_v13 he_v14 hinv10 e_v14 s10 v11 v13
          have h_ite_v18 := (show if_37_eo__24smtx_5ftypeof s11 v14 ⦃ r s' => s'.Inv ∧ s11.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
            unfold if_37_eo__24smtx_5ftypeof
            have hrem := (hG.rem hrem)
            have hG := Store.Grows.refl s11
            rcases Store.boolean_value_native h_v14 with ⟨hx_15, hbv_15⟩ | ⟨hx_15, hbv_15⟩
            · ite_branch hbv_15
              step as ⟨e_v15, he_v15⟩
              store_step with CtorSpec.eo__24emb_5ftsm_2eChar.construct s11 e_v15 (by rw [he_v15]; exact empty_args) hinv11 h64 as ⟨v15, s12, hinv12, h_v15⟩ growing hG carrying dropping h_v14 he_v15 e_v15 v14
              step as ⟨e_v16, he_v16⟩
              store_step with CtorSpec.eo__24emb_5ftsm_2eSeq.construct s12 e_v16 (by rw [he_v16]; rfl) h_v15 hinv12 h64 as ⟨v16, s13, hinv13, h_v16⟩ growing hG carrying dropping h_v15 he_v16 e_v16 v15
              ite_done hinv13 hG with (native_ite_true_rep _ hx_15 h_v16)
            · ite_branch hbv_15
              step as ⟨e_v17, he_v17⟩
              store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s11 e_v17 (by rw [he_v17]; exact empty_args) hinv11 h64 as ⟨v17, s12, hinv12, h_v17⟩ growing hG carrying dropping h_v14 he_v17 hinv11 e_v17 s11 v14
              ite_done hinv12 hG with (native_ite_false_rep _ hx_15 h_v17))
          store_step with h_ite_v18 as ⟨v18, s12, hinv12, h_v18⟩ growing hG carrying dropping h_ite_v18 h_v14 hinv11 s11 v14
          ite_done hinv12 hG with (native_ite_true_rep _ hx_11 h_v18)
        · ite_branch hbv_11
          step as ⟨e_v19, he_v19⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s7 e_v19 (by rw [he_v19]; exact empty_args) hinv7 h64 as ⟨v19, s8, hinv8, h_v19⟩ growing hG carrying dropping h_v10 h_v3 he_v19 hinv7 e_v19 s7 v10 v3
          ite_done hinv8 hG with (native_ite_false_rep _ hx_11 h_v19))
      store_step with h_ite_v20 as ⟨v20, s8, hinv8, h_v20⟩ growing hG carrying dropping h_ite_v20 h_v10 h_v3 hinv7 s7 v10 v3
      ite_done hinv8 hG with (native_ite_true_rep _ hx_8 h_v20)
    · ite_branch hbv_8
      step as ⟨e_v21, he_v21⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s4 e_v21 (by rw [he_v21]; exact empty_args) hinv4 h64 as ⟨v21, s5, hinv5, h_v21⟩ growing hG carrying dropping h_v2 h_v3 h_v7 he_v21 hinv4 e_v21 s4 v2 v3 v7
      ite_done hinv5 hG with (native_ite_false_rep _ hx_8 h_v21))
  store_step with h_ite_v22 as ⟨v22, s5, hinv5, h_v22⟩ growing hG carrying dropping h_ite_v22 h_v2 h_v3 h_v7 hinv4 s4 v2 v3 v7
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v4, s1, hinv1, h_v4⟩ growing hG carrying h_v2 h_v3 dropping h_a0 h_v1 v1
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eChar.construct s1 e_v5 (by rw [he_v5]; exact empty_args) hinv1 h64 as ⟨v5, s2, hinv2, h_v5⟩ growing hG carrying h_v2 h_v3 h_v4 dropping he_v5 hinv1 e_v5 s1
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eSeq.construct s2 e_v6 (by rw [he_v6]; rfl) h_v5 hinv2 h64 as ⟨v6, s3, hinv3, h_v6⟩ growing hG carrying h_v2 h_v3 h_v4 dropping h_v5 he_v6 hinv2 e_v6 s2 v5
  step as ⟨e_v7, he_v7⟩
  store_step with Store.native_spec_Teq s3 e_v7 (by rw [he_v7]; rfl) h_v4 h_v6 hinv3 h64 as ⟨v7, s4, hinv4, h_v7⟩ growing hG carrying h_v2 h_v3 dropping h_v4 h_v6 he_v7 hinv3 e_v7 s3 v4 v6
  have h_ite_v22 := (show if_42_eo__24smtx_5ftypeof s4 v7 v2 v3 ⦃ r s' => s'.Inv ∧ s4.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_42_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s4
    rcases Store.boolean_value_native h_v7 with ⟨hx_8, hbv_8⟩ | ⟨hx_8, hbv_8⟩
    · ite_branch hbv_8
      store_step with ih.eo__24smtx_5ftypeof s4 v2 _ hinv4 h64 (hG.rem hrem) h_v2 as ⟨v8, s5, hinv5, h_v8⟩ growing hG carrying h_v3 dropping h_v2 h_v7 v2 v7
      step as ⟨e_v9, he_v9⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eRegLan.construct s5 e_v9 (by rw [he_v9]; exact empty_args) hinv5 h64 as ⟨v9, s6, hinv6, h_v9⟩ growing hG carrying h_v3 h_v8 dropping he_v9 e_v9
      step as ⟨e_v10, he_v10⟩
      store_step with Store.native_spec_Teq s6 e_v10 (by rw [he_v10]; rfl) h_v8 h_v9 hinv6 h64 as ⟨v10, s7, hinv7, h_v10⟩ growing hG carrying h_v3 dropping h_v8 h_v9 he_v10 hinv6 e_v10 s6 v8 v9
      have h_ite_v20 := (show if_41_eo__24smtx_5ftypeof s7 v10 v3 ⦃ r s' => s'.Inv ∧ s7.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_41_eo__24smtx_5ftypeof
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s7
        rcases Store.boolean_value_native h_v10 with ⟨hx_11, hbv_11⟩ | ⟨hx_11, hbv_11⟩
        · ite_branch hbv_11
          store_step with ih.eo__24smtx_5ftypeof s7 v3 _ hinv7 h64 (hG.rem hrem) h_v3 as ⟨v11, s8, hinv8, h_v11⟩ growing hG carrying dropping h_v10 h_v3 v10 v3
          step as ⟨e_v12, he_v12⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eChar.construct s8 e_v12 (by rw [he_v12]; exact empty_args) hinv8 h64 as ⟨v12, s9, hinv9, h_v12⟩ growing hG carrying h_v11 dropping he_v12 e_v12
          step as ⟨e_v13, he_v13⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eSeq.construct s9 e_v13 (by rw [he_v13]; rfl) h_v12 hinv9 h64 as ⟨v13, s10, hinv10, h_v13⟩ growing hG carrying h_v11 dropping h_v12 he_v13 hinv9 e_v13 s9 v12
          step as ⟨e_v14, he_v14⟩
          store_step with Store.native_spec_Teq s10 e_v14 (by rw [he_v14]; rfl) h_v11 h_v13 hinv10 h64 as ⟨v14, s11, hinv11, h_v14⟩ growing hG carrying dropping h_v11 h_v13 he_v14 hinv10 e_v14 s10 v11 v13
          have h_ite_v18 := (show if_40_eo__24smtx_5ftypeof s11 v14 ⦃ r s' => s'.Inv ∧ s11.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
            unfold if_40_eo__24smtx_5ftypeof
            have hrem := (hG.rem hrem)
            have hG := Store.Grows.refl s11
            rcases Store.boolean_value_native h_v14 with ⟨hx_15, hbv_15⟩ | ⟨hx_15, hbv_15⟩
            · ite_branch hbv_15
              step as ⟨e_v15, he_v15⟩
              store_step with CtorSpec.eo__24emb_5ftsm_2eChar.construct s11 e_v15 (by rw [he_v15]; exact empty_args) hinv11 h64 as ⟨v15, s12, hinv12, h_v15⟩ growing hG carrying dropping h_v14 he_v15 e_v15 v14
              step as ⟨e_v16, he_v16⟩
              store_step with CtorSpec.eo__24emb_5ftsm_2eSeq.construct s12 e_v16 (by rw [he_v16]; rfl) h_v15 hinv12 h64 as ⟨v16, s13, hinv13, h_v16⟩ growing hG carrying dropping h_v15 he_v16 e_v16 v15
              ite_done hinv13 hG with (native_ite_true_rep _ hx_15 h_v16)
            · ite_branch hbv_15
              step as ⟨e_v17, he_v17⟩
              store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s11 e_v17 (by rw [he_v17]; exact empty_args) hinv11 h64 as ⟨v17, s12, hinv12, h_v17⟩ growing hG carrying dropping h_v14 he_v17 hinv11 e_v17 s11 v14
              ite_done hinv12 hG with (native_ite_false_rep _ hx_15 h_v17))
          store_step with h_ite_v18 as ⟨v18, s12, hinv12, h_v18⟩ growing hG carrying dropping h_ite_v18 h_v14 hinv11 s11 v14
          ite_done hinv12 hG with (native_ite_true_rep _ hx_11 h_v18)
        · ite_branch hbv_11
          step as ⟨e_v19, he_v19⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s7 e_v19 (by rw [he_v19]; exact empty_args) hinv7 h64 as ⟨v19, s8, hinv8, h_v19⟩ growing hG carrying dropping h_v10 h_v3 he_v19 hinv7 e_v19 s7 v10 v3
          ite_done hinv8 hG with (native_ite_false_rep _ hx_11 h_v19))
      store_step with h_ite_v20 as ⟨v20, s8, hinv8, h_v20⟩ growing hG carrying dropping h_ite_v20 h_v10 h_v3 hinv7 s7 v10 v3
      ite_done hinv8 hG with (native_ite_true_rep _ hx_8 h_v20)
    · ite_branch hbv_8
      step as ⟨e_v21, he_v21⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s4 e_v21 (by rw [he_v21]; exact empty_args) hinv4 h64 as ⟨v21, s5, hinv5, h_v21⟩ growing hG carrying dropping h_v2 h_v3 h_v7 he_v21 hinv4 e_v21 s4 v2 v3 v7
      ite_done hinv5 hG with (native_ite_false_rep _ hx_8 h_v21))
  store_step with h_ite_v22 as ⟨v22, s5, hinv5, h_v22⟩ growing hG carrying dropping h_ite_v22 h_v2 h_v3 h_v7 hinv4 s4 v2 v3 v7
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v4, s1, hinv1, h_v4⟩ growing hG carrying h_v2 h_v3 dropping h_a0 h_v1 v1
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eChar.construct s1 e_v5 (by rw [he_v5]; exact empty_args) hinv1 h64 as ⟨v5, s2, hinv2, h_v5⟩ growing hG carrying h_v2 h_v3 h_v4 dropping he_v5 hinv1 e_v5 s1
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eSeq.construct s2 e_v6 (by rw [he_v6]; rfl) h_v5 hinv2 h64 as ⟨v6, s3, hinv3, h_v6⟩ growing hG carrying h_v2 h_v3 h_v4 dropping h_v5 he_v6 hinv2 e_v6 s2 v5
  step as ⟨e_v7, he_v7⟩
  store_step with Store.native_spec_Teq s3 e_v7 (by rw [he_v7]; rfl) h_v4 h_v6 hinv3 h64 as ⟨v7, s4, hinv4, h_v7⟩ growing hG carrying h_v2 h_v3 dropping h_v4 h_v6 he_v7 hinv3 e_v7 s3 v4 v6
  have h_ite_v20 := (show if_45_eo__24smtx_5ftypeof s4 v7 v2 v3 ⦃ r s' => s'.Inv ∧ s4.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_45_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s4
    rcases Store.boolean_value_native h_v7 with ⟨hx_8, hbv_8⟩ | ⟨hx_8, hbv_8⟩
    · ite_branch hbv_8
      store_step with ih.eo__24smtx_5ftypeof s4 v2 _ hinv4 h64 (hG.rem hrem) h_v2 as ⟨v8, s5, hinv5, h_v8⟩ growing hG carrying h_v3 dropping h_v2 h_v7 v2 v7
      step as ⟨e_v9, he_v9⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eRegLan.construct s5 e_v9 (by rw [he_v9]; exact empty_args) hinv5 h64 as ⟨v9, s6, hinv6, h_v9⟩ growing hG carrying h_v3 h_v8 dropping he_v9 e_v9
      step as ⟨e_v10, he_v10⟩
      store_step with Store.native_spec_Teq s6 e_v10 (by rw [he_v10]; rfl) h_v8 h_v9 hinv6 h64 as ⟨v10, s7, hinv7, h_v10⟩ growing hG carrying h_v3 dropping h_v8 h_v9 he_v10 hinv6 e_v10 s6 v8 v9
      have h_ite_v18 := (show if_44_eo__24smtx_5ftypeof s7 v10 v3 ⦃ r s' => s'.Inv ∧ s7.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_44_eo__24smtx_5ftypeof
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s7
        rcases Store.boolean_value_native h_v10 with ⟨hx_11, hbv_11⟩ | ⟨hx_11, hbv_11⟩
        · ite_branch hbv_11
          store_step with ih.eo__24smtx_5ftypeof s7 v3 _ hinv7 h64 (hG.rem hrem) h_v3 as ⟨v11, s8, hinv8, h_v11⟩ growing hG carrying dropping h_v10 h_v3 v10 v3
          step as ⟨e_v12, he_v12⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eInt.construct s8 e_v12 (by rw [he_v12]; exact empty_args) hinv8 h64 as ⟨v12, s9, hinv9, h_v12⟩ growing hG carrying h_v11 dropping he_v12 e_v12
          step as ⟨e_v13, he_v13⟩
          store_step with Store.native_spec_Teq s9 e_v13 (by rw [he_v13]; rfl) h_v11 h_v12 hinv9 h64 as ⟨v13, s10, hinv10, h_v13⟩ growing hG carrying dropping h_v11 h_v12 he_v13 hinv9 e_v13 s9 v11 v12
          have h_ite_v16 := (show if_43_eo__24smtx_5ftypeof s10 v13 ⦃ r s' => s'.Inv ∧ s10.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
            unfold if_43_eo__24smtx_5ftypeof
            have hrem := (hG.rem hrem)
            have hG := Store.Grows.refl s10
            rcases Store.boolean_value_native h_v13 with ⟨hx_14, hbv_14⟩ | ⟨hx_14, hbv_14⟩
            · ite_branch hbv_14
              step as ⟨e_v14, he_v14⟩
              store_step with CtorSpec.eo__24emb_5ftsm_2eInt.construct s10 e_v14 (by rw [he_v14]; exact empty_args) hinv10 h64 as ⟨v14, s11, hinv11, h_v14⟩ growing hG carrying dropping h_v13 he_v14 e_v14 v13
              ite_done hinv11 hG with (native_ite_true_rep _ hx_14 h_v14)
            · ite_branch hbv_14
              step as ⟨e_v15, he_v15⟩
              store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s10 e_v15 (by rw [he_v15]; exact empty_args) hinv10 h64 as ⟨v15, s11, hinv11, h_v15⟩ growing hG carrying dropping h_v13 he_v15 hinv10 e_v15 s10 v13
              ite_done hinv11 hG with (native_ite_false_rep _ hx_14 h_v15))
          store_step with h_ite_v16 as ⟨v16, s11, hinv11, h_v16⟩ growing hG carrying dropping h_ite_v16 h_v13 hinv10 s10 v13
          ite_done hinv11 hG with (native_ite_true_rep _ hx_11 h_v16)
        · ite_branch hbv_11
          step as ⟨e_v17, he_v17⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s7 e_v17 (by rw [he_v17]; exact empty_args) hinv7 h64 as ⟨v17, s8, hinv8, h_v17⟩ growing hG carrying dropping h_v10 h_v3 he_v17 hinv7 e_v17 s7 v10 v3
          ite_done hinv8 hG with (native_ite_false_rep _ hx_11 h_v17))
      store_step with h_ite_v18 as ⟨v18, s8, hinv8, h_v18⟩ growing hG carrying dropping h_ite_v18 h_v10 h_v3 hinv7 s7 v10 v3
      ite_done hinv8 hG with (native_ite_true_rep _ hx_8 h_v18)
    · ite_branch hbv_8
      step as ⟨e_v19, he_v19⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s4 e_v19 (by rw [he_v19]; exact empty_args) hinv4 h64 as ⟨v19, s5, hinv5, h_v19⟩ growing hG carrying dropping h_v2 h_v3 h_v7 he_v19 hinv4 e_v19 s4 v2 v3 v7
      ite_done hinv5 hG with (native_ite_false_rep _ hx_8 h_v19))
  store_step with h_ite_v20 as ⟨v20, s5, hinv5, h_v20⟩ growing hG carrying dropping h_ite_v20 h_v2 h_v3 h_v7 hinv4 s4 v2 v3 v7
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
  store_step with CtorSpec.eo__24emb_5fsm_2ere_2eallchar.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 dropping he_v0 e_v0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__smtx_typeof.case_104
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eRegLan.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying dropping h_a0 h_v0 he_v1 hinv1 e_v1 s1 v0
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
  store_step with CtorSpec.eo__24emb_5fsm_2ere_2enone.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 dropping he_v0 e_v0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__smtx_typeof.case_105
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eRegLan.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying dropping h_a0 h_v0 he_v1 hinv1 e_v1 s1 v0
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
  store_step with CtorSpec.eo__24emb_5fsm_2ere_2eall.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 dropping he_v0 e_v0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__smtx_typeof.case_106
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eRegLan.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying dropping h_a0 h_v0 he_v1 hinv1 e_v1 s1 v0
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying dropping h_a0 h_v1 v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eChar.construct s1 e_v3 (by rw [he_v3]; exact empty_args) hinv1 h64 as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying h_v2 dropping he_v3 hinv1 e_v3 s1
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eSeq.construct s2 e_v4 (by rw [he_v4]; rfl) h_v3 hinv2 h64 as ⟨v4, s3, hinv3, h_v4⟩ growing hG carrying h_v2 dropping h_v3 he_v4 hinv2 e_v4 s2 v3
  step as ⟨e_v5, he_v5⟩
  store_step with Store.native_spec_Teq s3 e_v5 (by rw [he_v5]; rfl) h_v2 h_v4 hinv3 h64 as ⟨v5, s4, hinv4, h_v5⟩ growing hG carrying dropping h_v2 h_v4 he_v5 hinv3 e_v5 s3 v2 v4
  have h_ite_v8 := (show if_46_eo__24smtx_5ftypeof s4 v5 ⦃ r s' => s'.Inv ∧ s4.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_46_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s4
    rcases Store.boolean_value_native h_v5 with ⟨hx_6, hbv_6⟩ | ⟨hx_6, hbv_6⟩
    · ite_branch hbv_6
      step as ⟨e_v6, he_v6⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eRegLan.construct s4 e_v6 (by rw [he_v6]; exact empty_args) hinv4 h64 as ⟨v6, s5, hinv5, h_v6⟩ growing hG carrying dropping h_v5 he_v6 e_v6 v5
      ite_done hinv5 hG with (native_ite_true_rep _ hx_6 h_v6)
    · ite_branch hbv_6
      step as ⟨e_v7, he_v7⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s4 e_v7 (by rw [he_v7]; exact empty_args) hinv4 h64 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying dropping h_v5 he_v7 hinv4 e_v7 s4 v5
      ite_done hinv5 hG with (native_ite_false_rep _ hx_6 h_v7))
  store_step with h_ite_v8 as ⟨v8, s5, hinv5, h_v8⟩ growing hG carrying dropping h_ite_v8 h_v5 hinv4 s4 v5
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying dropping h_a0 h_v1 v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eRegLan.construct s1 e_v3 (by rw [he_v3]; exact empty_args) hinv1 h64 as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying h_v2 dropping he_v3 hinv1 e_v3 s1
  step as ⟨e_v4, he_v4⟩
  store_step with Store.native_spec_Teq s2 e_v4 (by rw [he_v4]; rfl) h_v2 h_v3 hinv2 h64 as ⟨v4, s3, hinv3, h_v4⟩ growing hG carrying dropping h_v2 h_v3 he_v4 hinv2 e_v4 s2 v2 v3
  have h_ite_v7 := (show if_47_eo__24smtx_5ftypeof s3 v4 ⦃ r s' => s'.Inv ∧ s3.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_47_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s3
    rcases Store.boolean_value_native h_v4 with ⟨hx_5, hbv_5⟩ | ⟨hx_5, hbv_5⟩
    · ite_branch hbv_5
      step as ⟨e_v5, he_v5⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eRegLan.construct s3 e_v5 (by rw [he_v5]; exact empty_args) hinv3 h64 as ⟨v5, s4, hinv4, h_v5⟩ growing hG carrying dropping h_v4 he_v5 e_v5 v4
      ite_done hinv4 hG with (native_ite_true_rep _ hx_5 h_v5)
    · ite_branch hbv_5
      step as ⟨e_v6, he_v6⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s3 e_v6 (by rw [he_v6]; exact empty_args) hinv3 h64 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying dropping h_v4 he_v6 hinv3 e_v6 s3 v4
      ite_done hinv4 hG with (native_ite_false_rep _ hx_5 h_v6))
  store_step with h_ite_v7 as ⟨v7, s4, hinv4, h_v7⟩ growing hG carrying dropping h_ite_v7 h_v4 hinv3 s3 v4
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying dropping h_a0 h_v1 v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eRegLan.construct s1 e_v3 (by rw [he_v3]; exact empty_args) hinv1 h64 as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying h_v2 dropping he_v3 hinv1 e_v3 s1
  step as ⟨e_v4, he_v4⟩
  store_step with Store.native_spec_Teq s2 e_v4 (by rw [he_v4]; rfl) h_v2 h_v3 hinv2 h64 as ⟨v4, s3, hinv3, h_v4⟩ growing hG carrying dropping h_v2 h_v3 he_v4 hinv2 e_v4 s2 v2 v3
  have h_ite_v7 := (show if_48_eo__24smtx_5ftypeof s3 v4 ⦃ r s' => s'.Inv ∧ s3.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_48_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s3
    rcases Store.boolean_value_native h_v4 with ⟨hx_5, hbv_5⟩ | ⟨hx_5, hbv_5⟩
    · ite_branch hbv_5
      step as ⟨e_v5, he_v5⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eRegLan.construct s3 e_v5 (by rw [he_v5]; exact empty_args) hinv3 h64 as ⟨v5, s4, hinv4, h_v5⟩ growing hG carrying dropping h_v4 he_v5 e_v5 v4
      ite_done hinv4 hG with (native_ite_true_rep _ hx_5 h_v5)
    · ite_branch hbv_5
      step as ⟨e_v6, he_v6⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s3 e_v6 (by rw [he_v6]; exact empty_args) hinv3 h64 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying dropping h_v4 he_v6 hinv3 e_v6 s3 v4
      ite_done hinv4 hG with (native_ite_false_rep _ hx_5 h_v6))
  store_step with h_ite_v7 as ⟨v7, s4, hinv4, h_v7⟩ growing hG carrying dropping h_ite_v7 h_v4 hinv3 s3 v4
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
  store_step with ih.eo__24smtx_5ftypeof s v2 _ hinv h64 hrem h_v2 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v1 dropping h_a0 h_v2 v2
  store_step with ih.eo__24smtx_5ftypeof_5fre_2e_5e s1 v1 v3 _ _ hinv1 h64 (hG.rem hrem) h_v1 h_v3 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying dropping h_v1 h_v3 hinv1 s1 v1 v3
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying dropping h_a0 h_v1 v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eRegLan.construct s1 e_v3 (by rw [he_v3]; exact empty_args) hinv1 h64 as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying h_v2 dropping he_v3 hinv1 e_v3 s1
  step as ⟨e_v4, he_v4⟩
  store_step with Store.native_spec_Teq s2 e_v4 (by rw [he_v4]; rfl) h_v2 h_v3 hinv2 h64 as ⟨v4, s3, hinv3, h_v4⟩ growing hG carrying dropping h_v2 h_v3 he_v4 hinv2 e_v4 s2 v2 v3
  have h_ite_v7 := (show if_49_eo__24smtx_5ftypeof s3 v4 ⦃ r s' => s'.Inv ∧ s3.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_49_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s3
    rcases Store.boolean_value_native h_v4 with ⟨hx_5, hbv_5⟩ | ⟨hx_5, hbv_5⟩
    · ite_branch hbv_5
      step as ⟨e_v5, he_v5⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eRegLan.construct s3 e_v5 (by rw [he_v5]; exact empty_args) hinv3 h64 as ⟨v5, s4, hinv4, h_v5⟩ growing hG carrying dropping h_v4 he_v5 e_v5 v4
      ite_done hinv4 hG with (native_ite_true_rep _ hx_5 h_v5)
    · ite_branch hbv_5
      step as ⟨e_v6, he_v6⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s3 e_v6 (by rw [he_v6]; exact empty_args) hinv3 h64 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying dropping h_v4 he_v6 hinv3 e_v6 s3 v4
      ite_done hinv4 hG with (native_ite_false_rep _ hx_5 h_v6))
  store_step with h_ite_v7 as ⟨v7, s4, hinv4, h_v7⟩ growing hG carrying dropping h_ite_v7 h_v4 hinv3 s3 v4
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying dropping h_a0 h_v1 v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eRegLan.construct s1 e_v3 (by rw [he_v3]; exact empty_args) hinv1 h64 as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying h_v2 dropping he_v3 hinv1 e_v3 s1
  step as ⟨e_v4, he_v4⟩
  store_step with Store.native_spec_Teq s2 e_v4 (by rw [he_v4]; rfl) h_v2 h_v3 hinv2 h64 as ⟨v4, s3, hinv3, h_v4⟩ growing hG carrying dropping h_v2 h_v3 he_v4 hinv2 e_v4 s2 v2 v3
  have h_ite_v7 := (show if_50_eo__24smtx_5ftypeof s3 v4 ⦃ r s' => s'.Inv ∧ s3.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_50_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s3
    rcases Store.boolean_value_native h_v4 with ⟨hx_5, hbv_5⟩ | ⟨hx_5, hbv_5⟩
    · ite_branch hbv_5
      step as ⟨e_v5, he_v5⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eRegLan.construct s3 e_v5 (by rw [he_v5]; exact empty_args) hinv3 h64 as ⟨v5, s4, hinv4, h_v5⟩ growing hG carrying dropping h_v4 he_v5 e_v5 v4
      ite_done hinv4 hG with (native_ite_true_rep _ hx_5 h_v5)
    · ite_branch hbv_5
      step as ⟨e_v6, he_v6⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s3 e_v6 (by rw [he_v6]; exact empty_args) hinv3 h64 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying dropping h_v4 he_v6 hinv3 e_v6 s3 v4
      ite_done hinv4 hG with (native_ite_false_rep _ hx_5 h_v6))
  store_step with h_ite_v7 as ⟨v7, s4, hinv4, h_v7⟩ growing hG carrying dropping h_ite_v7 h_v4 hinv3 s3 v4
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v2 dropping h_a0 h_v1 v1
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eChar.construct s1 e_v4 (by rw [he_v4]; exact empty_args) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v2 h_v3 dropping he_v4 hinv1 e_v4 s1
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eSeq.construct s2 e_v5 (by rw [he_v5]; rfl) h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_v2 h_v3 dropping h_v4 he_v5 hinv2 e_v5 s2 v4
  step as ⟨e_v6, he_v6⟩
  store_step with Store.native_spec_Teq s3 e_v6 (by rw [he_v6]; rfl) h_v3 h_v5 hinv3 h64 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_v2 dropping h_v3 h_v5 he_v6 hinv3 e_v6 s3 v3 v5
  have h_ite_v15 := (show if_52_eo__24smtx_5ftypeof s4 v6 v2 ⦃ r s' => s'.Inv ∧ s4.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_52_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s4
    rcases Store.boolean_value_native h_v6 with ⟨hx_7, hbv_7⟩ | ⟨hx_7, hbv_7⟩
    · ite_branch hbv_7
      store_step with ih.eo__24smtx_5ftypeof s4 v2 _ hinv4 h64 (hG.rem hrem) h_v2 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying dropping h_v2 h_v6 v2 v6
      step as ⟨e_v8, he_v8⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eChar.construct s5 e_v8 (by rw [he_v8]; exact empty_args) hinv5 h64 as ⟨v8, s6, hinv6, h_v8⟩ growing hG carrying h_v7 dropping he_v8 e_v8
      step as ⟨e_v9, he_v9⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eSeq.construct s6 e_v9 (by rw [he_v9]; rfl) h_v8 hinv6 h64 as ⟨v9, s7, hinv7, h_v9⟩ growing hG carrying h_v7 dropping h_v8 he_v9 hinv6 e_v9 s6 v8
      step as ⟨e_v10, he_v10⟩
      store_step with Store.native_spec_Teq s7 e_v10 (by rw [he_v10]; rfl) h_v7 h_v9 hinv7 h64 as ⟨v10, s8, hinv8, h_v10⟩ growing hG carrying dropping h_v7 h_v9 he_v10 hinv7 e_v10 s7 v7 v9
      have h_ite_v13 := (show if_51_eo__24smtx_5ftypeof s8 v10 ⦃ r s' => s'.Inv ∧ s8.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_51_eo__24smtx_5ftypeof
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s8
        rcases Store.boolean_value_native h_v10 with ⟨hx_11, hbv_11⟩ | ⟨hx_11, hbv_11⟩
        · ite_branch hbv_11
          step as ⟨e_v11, he_v11⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eRegLan.construct s8 e_v11 (by rw [he_v11]; exact empty_args) hinv8 h64 as ⟨v11, s9, hinv9, h_v11⟩ growing hG carrying dropping h_v10 he_v11 e_v11 v10
          ite_done hinv9 hG with (native_ite_true_rep _ hx_11 h_v11)
        · ite_branch hbv_11
          step as ⟨e_v12, he_v12⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s8 e_v12 (by rw [he_v12]; exact empty_args) hinv8 h64 as ⟨v12, s9, hinv9, h_v12⟩ growing hG carrying dropping h_v10 he_v12 hinv8 e_v12 s8 v10
          ite_done hinv9 hG with (native_ite_false_rep _ hx_11 h_v12))
      store_step with h_ite_v13 as ⟨v13, s9, hinv9, h_v13⟩ growing hG carrying dropping h_ite_v13 h_v10 hinv8 s8 v10
      ite_done hinv9 hG with (native_ite_true_rep _ hx_7 h_v13)
    · ite_branch hbv_7
      step as ⟨e_v14, he_v14⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s4 e_v14 (by rw [he_v14]; exact empty_args) hinv4 h64 as ⟨v14, s5, hinv5, h_v14⟩ growing hG carrying dropping h_v2 h_v6 he_v14 hinv4 e_v14 s4 v2 v6
      ite_done hinv5 hG with (native_ite_false_rep _ hx_7 h_v14))
  store_step with h_ite_v15 as ⟨v15, s5, hinv5, h_v15⟩ growing hG carrying dropping h_ite_v15 h_v2 h_v6 hinv4 s4 v2 v6
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v2 dropping h_a0 h_v1 v1
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eRegLan.construct s1 e_v4 (by rw [he_v4]; exact empty_args) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v2 h_v3 dropping he_v4 hinv1 e_v4 s1
  step as ⟨e_v5, he_v5⟩
  store_step with Store.native_spec_Teq s2 e_v5 (by rw [he_v5]; rfl) h_v3 h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_v2 dropping h_v3 h_v4 he_v5 hinv2 e_v5 s2 v3 v4
  have h_ite_v13 := (show if_54_eo__24smtx_5ftypeof s3 v5 v2 ⦃ r s' => s'.Inv ∧ s3.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_54_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s3
    rcases Store.boolean_value_native h_v5 with ⟨hx_6, hbv_6⟩ | ⟨hx_6, hbv_6⟩
    · ite_branch hbv_6
      store_step with ih.eo__24smtx_5ftypeof s3 v2 _ hinv3 h64 (hG.rem hrem) h_v2 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying dropping h_v2 h_v5 v2 v5
      step as ⟨e_v7, he_v7⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eRegLan.construct s4 e_v7 (by rw [he_v7]; exact empty_args) hinv4 h64 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_v6 dropping he_v7 e_v7
      step as ⟨e_v8, he_v8⟩
      store_step with Store.native_spec_Teq s5 e_v8 (by rw [he_v8]; rfl) h_v6 h_v7 hinv5 h64 as ⟨v8, s6, hinv6, h_v8⟩ growing hG carrying dropping h_v6 h_v7 he_v8 hinv5 e_v8 s5 v6 v7
      have h_ite_v11 := (show if_53_eo__24smtx_5ftypeof s6 v8 ⦃ r s' => s'.Inv ∧ s6.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_53_eo__24smtx_5ftypeof
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s6
        rcases Store.boolean_value_native h_v8 with ⟨hx_9, hbv_9⟩ | ⟨hx_9, hbv_9⟩
        · ite_branch hbv_9
          step as ⟨e_v9, he_v9⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eRegLan.construct s6 e_v9 (by rw [he_v9]; exact empty_args) hinv6 h64 as ⟨v9, s7, hinv7, h_v9⟩ growing hG carrying dropping h_v8 he_v9 e_v9 v8
          ite_done hinv7 hG with (native_ite_true_rep _ hx_9 h_v9)
        · ite_branch hbv_9
          step as ⟨e_v10, he_v10⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s6 e_v10 (by rw [he_v10]; exact empty_args) hinv6 h64 as ⟨v10, s7, hinv7, h_v10⟩ growing hG carrying dropping h_v8 he_v10 hinv6 e_v10 s6 v8
          ite_done hinv7 hG with (native_ite_false_rep _ hx_9 h_v10))
      store_step with h_ite_v11 as ⟨v11, s7, hinv7, h_v11⟩ growing hG carrying dropping h_ite_v11 h_v8 hinv6 s6 v8
      ite_done hinv7 hG with (native_ite_true_rep _ hx_6 h_v11)
    · ite_branch hbv_6
      step as ⟨e_v12, he_v12⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s3 e_v12 (by rw [he_v12]; exact empty_args) hinv3 h64 as ⟨v12, s4, hinv4, h_v12⟩ growing hG carrying dropping h_v2 h_v5 he_v12 hinv3 e_v12 s3 v2 v5
      ite_done hinv4 hG with (native_ite_false_rep _ hx_6 h_v12))
  store_step with h_ite_v13 as ⟨v13, s4, hinv4, h_v13⟩ growing hG carrying dropping h_ite_v13 h_v2 h_v5 hinv3 s3 v2 v5
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v2 dropping h_a0 h_v1 v1
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eRegLan.construct s1 e_v4 (by rw [he_v4]; exact empty_args) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v2 h_v3 dropping he_v4 hinv1 e_v4 s1
  step as ⟨e_v5, he_v5⟩
  store_step with Store.native_spec_Teq s2 e_v5 (by rw [he_v5]; rfl) h_v3 h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_v2 dropping h_v3 h_v4 he_v5 hinv2 e_v5 s2 v3 v4
  have h_ite_v13 := (show if_56_eo__24smtx_5ftypeof s3 v5 v2 ⦃ r s' => s'.Inv ∧ s3.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_56_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s3
    rcases Store.boolean_value_native h_v5 with ⟨hx_6, hbv_6⟩ | ⟨hx_6, hbv_6⟩
    · ite_branch hbv_6
      store_step with ih.eo__24smtx_5ftypeof s3 v2 _ hinv3 h64 (hG.rem hrem) h_v2 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying dropping h_v2 h_v5 v2 v5
      step as ⟨e_v7, he_v7⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eRegLan.construct s4 e_v7 (by rw [he_v7]; exact empty_args) hinv4 h64 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_v6 dropping he_v7 e_v7
      step as ⟨e_v8, he_v8⟩
      store_step with Store.native_spec_Teq s5 e_v8 (by rw [he_v8]; rfl) h_v6 h_v7 hinv5 h64 as ⟨v8, s6, hinv6, h_v8⟩ growing hG carrying dropping h_v6 h_v7 he_v8 hinv5 e_v8 s5 v6 v7
      have h_ite_v11 := (show if_55_eo__24smtx_5ftypeof s6 v8 ⦃ r s' => s'.Inv ∧ s6.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_55_eo__24smtx_5ftypeof
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s6
        rcases Store.boolean_value_native h_v8 with ⟨hx_9, hbv_9⟩ | ⟨hx_9, hbv_9⟩
        · ite_branch hbv_9
          step as ⟨e_v9, he_v9⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eRegLan.construct s6 e_v9 (by rw [he_v9]; exact empty_args) hinv6 h64 as ⟨v9, s7, hinv7, h_v9⟩ growing hG carrying dropping h_v8 he_v9 e_v9 v8
          ite_done hinv7 hG with (native_ite_true_rep _ hx_9 h_v9)
        · ite_branch hbv_9
          step as ⟨e_v10, he_v10⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s6 e_v10 (by rw [he_v10]; exact empty_args) hinv6 h64 as ⟨v10, s7, hinv7, h_v10⟩ growing hG carrying dropping h_v8 he_v10 hinv6 e_v10 s6 v8
          ite_done hinv7 hG with (native_ite_false_rep _ hx_9 h_v10))
      store_step with h_ite_v11 as ⟨v11, s7, hinv7, h_v11⟩ growing hG carrying dropping h_ite_v11 h_v8 hinv6 s6 v8
      ite_done hinv7 hG with (native_ite_true_rep _ hx_6 h_v11)
    · ite_branch hbv_6
      step as ⟨e_v12, he_v12⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s3 e_v12 (by rw [he_v12]; exact empty_args) hinv3 h64 as ⟨v12, s4, hinv4, h_v12⟩ growing hG carrying dropping h_v2 h_v5 he_v12 hinv3 e_v12 s3 v2 v5
      ite_done hinv4 hG with (native_ite_false_rep _ hx_6 h_v12))
  store_step with h_ite_v13 as ⟨v13, s4, hinv4, h_v13⟩ growing hG carrying dropping h_ite_v13 h_v2 h_v5 hinv3 s3 v2 v5
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v2 dropping h_a0 h_v1 v1
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eRegLan.construct s1 e_v4 (by rw [he_v4]; exact empty_args) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v2 h_v3 dropping he_v4 hinv1 e_v4 s1
  step as ⟨e_v5, he_v5⟩
  store_step with Store.native_spec_Teq s2 e_v5 (by rw [he_v5]; rfl) h_v3 h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_v2 dropping h_v3 h_v4 he_v5 hinv2 e_v5 s2 v3 v4
  have h_ite_v13 := (show if_58_eo__24smtx_5ftypeof s3 v5 v2 ⦃ r s' => s'.Inv ∧ s3.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_58_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s3
    rcases Store.boolean_value_native h_v5 with ⟨hx_6, hbv_6⟩ | ⟨hx_6, hbv_6⟩
    · ite_branch hbv_6
      store_step with ih.eo__24smtx_5ftypeof s3 v2 _ hinv3 h64 (hG.rem hrem) h_v2 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying dropping h_v2 h_v5 v2 v5
      step as ⟨e_v7, he_v7⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eRegLan.construct s4 e_v7 (by rw [he_v7]; exact empty_args) hinv4 h64 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_v6 dropping he_v7 e_v7
      step as ⟨e_v8, he_v8⟩
      store_step with Store.native_spec_Teq s5 e_v8 (by rw [he_v8]; rfl) h_v6 h_v7 hinv5 h64 as ⟨v8, s6, hinv6, h_v8⟩ growing hG carrying dropping h_v6 h_v7 he_v8 hinv5 e_v8 s5 v6 v7
      have h_ite_v11 := (show if_57_eo__24smtx_5ftypeof s6 v8 ⦃ r s' => s'.Inv ∧ s6.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_57_eo__24smtx_5ftypeof
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s6
        rcases Store.boolean_value_native h_v8 with ⟨hx_9, hbv_9⟩ | ⟨hx_9, hbv_9⟩
        · ite_branch hbv_9
          step as ⟨e_v9, he_v9⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eRegLan.construct s6 e_v9 (by rw [he_v9]; exact empty_args) hinv6 h64 as ⟨v9, s7, hinv7, h_v9⟩ growing hG carrying dropping h_v8 he_v9 e_v9 v8
          ite_done hinv7 hG with (native_ite_true_rep _ hx_9 h_v9)
        · ite_branch hbv_9
          step as ⟨e_v10, he_v10⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s6 e_v10 (by rw [he_v10]; exact empty_args) hinv6 h64 as ⟨v10, s7, hinv7, h_v10⟩ growing hG carrying dropping h_v8 he_v10 hinv6 e_v10 s6 v8
          ite_done hinv7 hG with (native_ite_false_rep _ hx_9 h_v10))
      store_step with h_ite_v11 as ⟨v11, s7, hinv7, h_v11⟩ growing hG carrying dropping h_ite_v11 h_v8 hinv6 s6 v8
      ite_done hinv7 hG with (native_ite_true_rep _ hx_6 h_v11)
    · ite_branch hbv_6
      step as ⟨e_v12, he_v12⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s3 e_v12 (by rw [he_v12]; exact empty_args) hinv3 h64 as ⟨v12, s4, hinv4, h_v12⟩ growing hG carrying dropping h_v2 h_v5 he_v12 hinv3 e_v12 s3 v2 v5
      ite_done hinv4 hG with (native_ite_false_rep _ hx_6 h_v12))
  store_step with h_ite_v13 as ⟨v13, s4, hinv4, h_v13⟩ growing hG carrying dropping h_ite_v13 h_v2 h_v5 hinv3 s3 v2 v5
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v2 dropping h_a0 h_v1 v1
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eRegLan.construct s1 e_v4 (by rw [he_v4]; exact empty_args) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v2 h_v3 dropping he_v4 hinv1 e_v4 s1
  step as ⟨e_v5, he_v5⟩
  store_step with Store.native_spec_Teq s2 e_v5 (by rw [he_v5]; rfl) h_v3 h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_v2 dropping h_v3 h_v4 he_v5 hinv2 e_v5 s2 v3 v4
  have h_ite_v13 := (show if_60_eo__24smtx_5ftypeof s3 v5 v2 ⦃ r s' => s'.Inv ∧ s3.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_60_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s3
    rcases Store.boolean_value_native h_v5 with ⟨hx_6, hbv_6⟩ | ⟨hx_6, hbv_6⟩
    · ite_branch hbv_6
      store_step with ih.eo__24smtx_5ftypeof s3 v2 _ hinv3 h64 (hG.rem hrem) h_v2 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying dropping h_v2 h_v5 v2 v5
      step as ⟨e_v7, he_v7⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eRegLan.construct s4 e_v7 (by rw [he_v7]; exact empty_args) hinv4 h64 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_v6 dropping he_v7 e_v7
      step as ⟨e_v8, he_v8⟩
      store_step with Store.native_spec_Teq s5 e_v8 (by rw [he_v8]; rfl) h_v6 h_v7 hinv5 h64 as ⟨v8, s6, hinv6, h_v8⟩ growing hG carrying dropping h_v6 h_v7 he_v8 hinv5 e_v8 s5 v6 v7
      have h_ite_v11 := (show if_59_eo__24smtx_5ftypeof s6 v8 ⦃ r s' => s'.Inv ∧ s6.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_59_eo__24smtx_5ftypeof
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s6
        rcases Store.boolean_value_native h_v8 with ⟨hx_9, hbv_9⟩ | ⟨hx_9, hbv_9⟩
        · ite_branch hbv_9
          step as ⟨e_v9, he_v9⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eRegLan.construct s6 e_v9 (by rw [he_v9]; exact empty_args) hinv6 h64 as ⟨v9, s7, hinv7, h_v9⟩ growing hG carrying dropping h_v8 he_v9 e_v9 v8
          ite_done hinv7 hG with (native_ite_true_rep _ hx_9 h_v9)
        · ite_branch hbv_9
          step as ⟨e_v10, he_v10⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s6 e_v10 (by rw [he_v10]; exact empty_args) hinv6 h64 as ⟨v10, s7, hinv7, h_v10⟩ growing hG carrying dropping h_v8 he_v10 hinv6 e_v10 s6 v8
          ite_done hinv7 hG with (native_ite_false_rep _ hx_9 h_v10))
      store_step with h_ite_v11 as ⟨v11, s7, hinv7, h_v11⟩ growing hG carrying dropping h_ite_v11 h_v8 hinv6 s6 v8
      ite_done hinv7 hG with (native_ite_true_rep _ hx_6 h_v11)
    · ite_branch hbv_6
      step as ⟨e_v12, he_v12⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s3 e_v12 (by rw [he_v12]; exact empty_args) hinv3 h64 as ⟨v12, s4, hinv4, h_v12⟩ growing hG carrying dropping h_v2 h_v5 he_v12 hinv3 e_v12 s3 v2 v5
      ite_done hinv4 hG with (native_ite_false_rep _ hx_6 h_v12))
  store_step with h_ite_v13 as ⟨v13, s4, hinv4, h_v13⟩ growing hG carrying dropping h_ite_v13 h_v2 h_v5 hinv3 s3 v2 v5
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
  store_step with ih.eo__24smtx_5ftypeof s v3 _ hinv h64 hrem h_v3 as ⟨v4, s1, hinv1, h_v4⟩ growing hG carrying h_v1 h_v2 dropping h_a0 h_v3 v3
  store_step with ih.eo__24smtx_5ftypeof_5fre_2eloop s1 v1 v2 v4 _ _ _ hinv1 h64 (hG.rem hrem) h_v1 h_v2 h_v4 as ⟨v5, s2, hinv2, h_v5⟩ growing hG carrying dropping h_v1 h_v2 h_v4 hinv1 s1 v1 v2 v4
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v2 dropping h_a0 h_v1 v1
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eChar.construct s1 e_v4 (by rw [he_v4]; exact empty_args) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v2 h_v3 dropping he_v4 hinv1 e_v4 s1
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eSeq.construct s2 e_v5 (by rw [he_v5]; rfl) h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_v2 h_v3 dropping h_v4 he_v5 hinv2 e_v5 s2 v4
  step as ⟨e_v6, he_v6⟩
  store_step with Store.native_spec_Teq s3 e_v6 (by rw [he_v6]; rfl) h_v3 h_v5 hinv3 h64 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_v2 dropping h_v3 h_v5 he_v6 hinv3 e_v6 s3 v3 v5
  have h_ite_v14 := (show if_62_eo__24smtx_5ftypeof s4 v6 v2 ⦃ r s' => s'.Inv ∧ s4.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_62_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s4
    rcases Store.boolean_value_native h_v6 with ⟨hx_7, hbv_7⟩ | ⟨hx_7, hbv_7⟩
    · ite_branch hbv_7
      store_step with ih.eo__24smtx_5ftypeof s4 v2 _ hinv4 h64 (hG.rem hrem) h_v2 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying dropping h_v2 h_v6 v2 v6
      step as ⟨e_v8, he_v8⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eRegLan.construct s5 e_v8 (by rw [he_v8]; exact empty_args) hinv5 h64 as ⟨v8, s6, hinv6, h_v8⟩ growing hG carrying h_v7 dropping he_v8 e_v8
      step as ⟨e_v9, he_v9⟩
      store_step with Store.native_spec_Teq s6 e_v9 (by rw [he_v9]; rfl) h_v7 h_v8 hinv6 h64 as ⟨v9, s7, hinv7, h_v9⟩ growing hG carrying dropping h_v7 h_v8 he_v9 hinv6 e_v9 s6 v7 v8
      have h_ite_v12 := (show if_61_eo__24smtx_5ftypeof s7 v9 ⦃ r s' => s'.Inv ∧ s7.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_61_eo__24smtx_5ftypeof
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s7
        rcases Store.boolean_value_native h_v9 with ⟨hx_10, hbv_10⟩ | ⟨hx_10, hbv_10⟩
        · ite_branch hbv_10
          step as ⟨e_v10, he_v10⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s7 e_v10 (by rw [he_v10]; exact empty_args) hinv7 h64 as ⟨v10, s8, hinv8, h_v10⟩ growing hG carrying dropping h_v9 he_v10 e_v10 v9
          ite_done hinv8 hG with (native_ite_true_rep _ hx_10 h_v10)
        · ite_branch hbv_10
          step as ⟨e_v11, he_v11⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s7 e_v11 (by rw [he_v11]; exact empty_args) hinv7 h64 as ⟨v11, s8, hinv8, h_v11⟩ growing hG carrying dropping h_v9 he_v11 hinv7 e_v11 s7 v9
          ite_done hinv8 hG with (native_ite_false_rep _ hx_10 h_v11))
      store_step with h_ite_v12 as ⟨v12, s8, hinv8, h_v12⟩ growing hG carrying dropping h_ite_v12 h_v9 hinv7 s7 v9
      ite_done hinv8 hG with (native_ite_true_rep _ hx_7 h_v12)
    · ite_branch hbv_7
      step as ⟨e_v13, he_v13⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s4 e_v13 (by rw [he_v13]; exact empty_args) hinv4 h64 as ⟨v13, s5, hinv5, h_v13⟩ growing hG carrying dropping h_v2 h_v6 he_v13 hinv4 e_v13 s4 v2 v6
      ite_done hinv5 hG with (native_ite_false_rep _ hx_7 h_v13))
  store_step with h_ite_v14 as ⟨v14, s5, hinv5, h_v14⟩ growing hG carrying dropping h_ite_v14 h_v2 h_v6 hinv4 s4 v2 v6
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying h_v1 dropping h_a0
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eSeq.construct s1 e_v3 (by rw [he_v3]; rfl) h_v2 hinv1 h64 as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying h_v1 dropping h_v2 he_v3 hinv1 e_v3 s1 v2
  store_step with ih.eo__24smtx_5ftypeof s2 v1 _ hinv2 h64 (hG.rem hrem) h_v1 as ⟨v4, s3, hinv3, h_v4⟩ growing hG carrying h_v3 dropping h_v1 hinv2 s2 v1
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eSeq.construct s3 e_v5 (by rw [he_v5]; rfl) h_v4 hinv3 h64 as ⟨v5, s4, hinv4, h_v5⟩ growing hG carrying h_v3 dropping h_v4 he_v5 hinv3 e_v5 s3 v4
  store_step with ih.eo__24smtx_5ftypeof_5fguard_5fwf s4 v3 v5 _ _ hinv4 h64 (hG.rem hrem) h_v3 h_v5 as ⟨v6, s5, hinv5, h_v6⟩ growing hG carrying dropping h_v3 h_v5 hinv4 s4 v3 v5
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v2 dropping h_a0 h_v1 v1
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v3 dropping h_v2 hinv1 s1 v2
  store_step with ih.eo__24smtx_5ftypeof_5fseq_2enth s2 v3 v4 _ _ hinv2 h64 (hG.rem hrem) h_v3 h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying dropping h_v3 h_v4 hinv2 s2 v3 v4
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v4, s1, hinv1, h_v4⟩ growing hG carrying h_v2 h_v3 dropping h_a0 h_v1 v1
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eChar.construct s1 e_v5 (by rw [he_v5]; exact empty_args) hinv1 h64 as ⟨v5, s2, hinv2, h_v5⟩ growing hG carrying h_v2 h_v3 h_v4 dropping he_v5 hinv1 e_v5 s1
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eSeq.construct s2 e_v6 (by rw [he_v6]; rfl) h_v5 hinv2 h64 as ⟨v6, s3, hinv3, h_v6⟩ growing hG carrying h_v2 h_v3 h_v4 dropping h_v5 he_v6 hinv2 e_v6 s2 v5
  step as ⟨e_v7, he_v7⟩
  store_step with Store.native_spec_Teq s3 e_v7 (by rw [he_v7]; rfl) h_v4 h_v6 hinv3 h64 as ⟨v7, s4, hinv4, h_v7⟩ growing hG carrying h_v2 h_v3 dropping h_v4 h_v6 he_v7 hinv3 e_v7 s3 v4 v6
  have h_ite_v20 := (show if_65_eo__24smtx_5ftypeof s4 v7 v2 v3 ⦃ r s' => s'.Inv ∧ s4.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_65_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s4
    rcases Store.boolean_value_native h_v7 with ⟨hx_8, hbv_8⟩ | ⟨hx_8, hbv_8⟩
    · ite_branch hbv_8
      store_step with ih.eo__24smtx_5ftypeof s4 v2 _ hinv4 h64 (hG.rem hrem) h_v2 as ⟨v8, s5, hinv5, h_v8⟩ growing hG carrying h_v3 dropping h_v2 h_v7 v2 v7
      step as ⟨e_v9, he_v9⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eRegLan.construct s5 e_v9 (by rw [he_v9]; exact empty_args) hinv5 h64 as ⟨v9, s6, hinv6, h_v9⟩ growing hG carrying h_v3 h_v8 dropping he_v9 e_v9
      step as ⟨e_v10, he_v10⟩
      store_step with Store.native_spec_Teq s6 e_v10 (by rw [he_v10]; rfl) h_v8 h_v9 hinv6 h64 as ⟨v10, s7, hinv7, h_v10⟩ growing hG carrying h_v3 dropping h_v8 h_v9 he_v10 hinv6 e_v10 s6 v8 v9
      have h_ite_v18 := (show if_64_eo__24smtx_5ftypeof s7 v10 v3 ⦃ r s' => s'.Inv ∧ s7.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_64_eo__24smtx_5ftypeof
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s7
        rcases Store.boolean_value_native h_v10 with ⟨hx_11, hbv_11⟩ | ⟨hx_11, hbv_11⟩
        · ite_branch hbv_11
          store_step with ih.eo__24smtx_5ftypeof s7 v3 _ hinv7 h64 (hG.rem hrem) h_v3 as ⟨v11, s8, hinv8, h_v11⟩ growing hG carrying dropping h_v10 h_v3 v10 v3
          step as ⟨e_v12, he_v12⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eRegLan.construct s8 e_v12 (by rw [he_v12]; exact empty_args) hinv8 h64 as ⟨v12, s9, hinv9, h_v12⟩ growing hG carrying h_v11 dropping he_v12 e_v12
          step as ⟨e_v13, he_v13⟩
          store_step with Store.native_spec_Teq s9 e_v13 (by rw [he_v13]; rfl) h_v11 h_v12 hinv9 h64 as ⟨v13, s10, hinv10, h_v13⟩ growing hG carrying dropping h_v11 h_v12 he_v13 hinv9 e_v13 s9 v11 v12
          have h_ite_v16 := (show if_63_eo__24smtx_5ftypeof s10 v13 ⦃ r s' => s'.Inv ∧ s10.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
            unfold if_63_eo__24smtx_5ftypeof
            have hrem := (hG.rem hrem)
            have hG := Store.Grows.refl s10
            rcases Store.boolean_value_native h_v13 with ⟨hx_14, hbv_14⟩ | ⟨hx_14, hbv_14⟩
            · ite_branch hbv_14
              step as ⟨e_v14, he_v14⟩
              store_step with CtorSpec.eo__24emb_5ftsm_2eInt.construct s10 e_v14 (by rw [he_v14]; exact empty_args) hinv10 h64 as ⟨v14, s11, hinv11, h_v14⟩ growing hG carrying dropping h_v13 he_v14 e_v14 v13
              ite_done hinv11 hG with (native_ite_true_rep _ hx_14 h_v14)
            · ite_branch hbv_14
              step as ⟨e_v15, he_v15⟩
              store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s10 e_v15 (by rw [he_v15]; exact empty_args) hinv10 h64 as ⟨v15, s11, hinv11, h_v15⟩ growing hG carrying dropping h_v13 he_v15 hinv10 e_v15 s10 v13
              ite_done hinv11 hG with (native_ite_false_rep _ hx_14 h_v15))
          store_step with h_ite_v16 as ⟨v16, s11, hinv11, h_v16⟩ growing hG carrying dropping h_ite_v16 h_v13 hinv10 s10 v13
          ite_done hinv11 hG with (native_ite_true_rep _ hx_11 h_v16)
        · ite_branch hbv_11
          step as ⟨e_v17, he_v17⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s7 e_v17 (by rw [he_v17]; exact empty_args) hinv7 h64 as ⟨v17, s8, hinv8, h_v17⟩ growing hG carrying dropping h_v10 h_v3 he_v17 hinv7 e_v17 s7 v10 v3
          ite_done hinv8 hG with (native_ite_false_rep _ hx_11 h_v17))
      store_step with h_ite_v18 as ⟨v18, s8, hinv8, h_v18⟩ growing hG carrying dropping h_ite_v18 h_v10 h_v3 hinv7 s7 v10 v3
      ite_done hinv8 hG with (native_ite_true_rep _ hx_8 h_v18)
    · ite_branch hbv_8
      step as ⟨e_v19, he_v19⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s4 e_v19 (by rw [he_v19]; exact empty_args) hinv4 h64 as ⟨v19, s5, hinv5, h_v19⟩ growing hG carrying dropping h_v2 h_v3 h_v7 he_v19 hinv4 e_v19 s4 v2 v3 v7
      ite_done hinv5 hG with (native_ite_false_rep _ hx_8 h_v19))
  store_step with h_ite_v20 as ⟨v20, s5, hinv5, h_v20⟩ growing hG carrying dropping h_ite_v20 h_v2 h_v3 h_v7 hinv4 s4 v2 v3 v7
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v2 dropping h_a0 h_v1 v1
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v3 dropping h_v2 hinv1 s1 v2
  store_step with ih.eo__24smtx_5ftypeof_5fseq_5fdiff s2 v3 v4 _ _ hinv2 h64 (hG.rem hrem) h_v3 h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying dropping h_v3 h_v4 hinv2 s2 v3 v4
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v4, s1, hinv1, h_v4⟩ growing hG carrying h_v2 h_v3 dropping h_a0 h_v1 v1
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v5, s2, hinv2, h_v5⟩ growing hG carrying h_v3 h_v4 dropping h_v2 hinv1 s1 v2
  store_step with ih.eo__24smtx_5ftypeof s2 v3 _ hinv2 h64 (hG.rem hrem) h_v3 as ⟨v6, s3, hinv3, h_v6⟩ growing hG carrying h_v4 h_v5 dropping h_v3 hinv2 s2 v3
  store_step with ih.eo__24smtx_5ftypeof_5fstr_2eindexof s3 v4 v5 v6 _ _ _ hinv3 h64 (hG.rem hrem) h_v4 h_v5 h_v6 as ⟨v7, s4, hinv4, h_v7⟩ growing hG carrying dropping h_v4 h_v5 h_v6 hinv3 s3 v4 v5 v6
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v4, s1, hinv1, h_v4⟩ growing hG carrying h_v2 h_v3 dropping h_a0 h_v1 v1
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eChar.construct s1 e_v5 (by rw [he_v5]; exact empty_args) hinv1 h64 as ⟨v5, s2, hinv2, h_v5⟩ growing hG carrying h_v2 h_v3 h_v4 dropping he_v5 hinv1 e_v5 s1
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eSeq.construct s2 e_v6 (by rw [he_v6]; rfl) h_v5 hinv2 h64 as ⟨v6, s3, hinv3, h_v6⟩ growing hG carrying h_v2 h_v3 h_v4 dropping h_v5 he_v6 hinv2 e_v6 s2 v5
  step as ⟨e_v7, he_v7⟩
  store_step with Store.native_spec_Teq s3 e_v7 (by rw [he_v7]; rfl) h_v4 h_v6 hinv3 h64 as ⟨v7, s4, hinv4, h_v7⟩ growing hG carrying h_v2 h_v3 dropping h_v4 h_v6 he_v7 hinv3 e_v7 s3 v4 v6
  have h_ite_v20 := (show if_68_eo__24smtx_5ftypeof s4 v7 v2 v3 ⦃ r s' => s'.Inv ∧ s4.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_68_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s4
    rcases Store.boolean_value_native h_v7 with ⟨hx_8, hbv_8⟩ | ⟨hx_8, hbv_8⟩
    · ite_branch hbv_8
      store_step with ih.eo__24smtx_5ftypeof s4 v2 _ hinv4 h64 (hG.rem hrem) h_v2 as ⟨v8, s5, hinv5, h_v8⟩ growing hG carrying h_v3 dropping h_v2 h_v7 v2 v7
      step as ⟨e_v9, he_v9⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eRegLan.construct s5 e_v9 (by rw [he_v9]; exact empty_args) hinv5 h64 as ⟨v9, s6, hinv6, h_v9⟩ growing hG carrying h_v3 h_v8 dropping he_v9 e_v9
      step as ⟨e_v10, he_v10⟩
      store_step with Store.native_spec_Teq s6 e_v10 (by rw [he_v10]; rfl) h_v8 h_v9 hinv6 h64 as ⟨v10, s7, hinv7, h_v10⟩ growing hG carrying h_v3 dropping h_v8 h_v9 he_v10 hinv6 e_v10 s6 v8 v9
      have h_ite_v18 := (show if_67_eo__24smtx_5ftypeof s7 v10 v3 ⦃ r s' => s'.Inv ∧ s7.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_67_eo__24smtx_5ftypeof
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s7
        rcases Store.boolean_value_native h_v10 with ⟨hx_11, hbv_11⟩ | ⟨hx_11, hbv_11⟩
        · ite_branch hbv_11
          store_step with ih.eo__24smtx_5ftypeof s7 v3 _ hinv7 h64 (hG.rem hrem) h_v3 as ⟨v11, s8, hinv8, h_v11⟩ growing hG carrying dropping h_v10 h_v3 v10 v3
          step as ⟨e_v12, he_v12⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eInt.construct s8 e_v12 (by rw [he_v12]; exact empty_args) hinv8 h64 as ⟨v12, s9, hinv9, h_v12⟩ growing hG carrying h_v11 dropping he_v12 e_v12
          step as ⟨e_v13, he_v13⟩
          store_step with Store.native_spec_Teq s9 e_v13 (by rw [he_v13]; rfl) h_v11 h_v12 hinv9 h64 as ⟨v13, s10, hinv10, h_v13⟩ growing hG carrying dropping h_v11 h_v12 he_v13 hinv9 e_v13 s9 v11 v12
          have h_ite_v16 := (show if_66_eo__24smtx_5ftypeof s10 v13 ⦃ r s' => s'.Inv ∧ s10.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
            unfold if_66_eo__24smtx_5ftypeof
            have hrem := (hG.rem hrem)
            have hG := Store.Grows.refl s10
            rcases Store.boolean_value_native h_v13 with ⟨hx_14, hbv_14⟩ | ⟨hx_14, hbv_14⟩
            · ite_branch hbv_14
              step as ⟨e_v14, he_v14⟩
              store_step with CtorSpec.eo__24emb_5ftsm_2eInt.construct s10 e_v14 (by rw [he_v14]; exact empty_args) hinv10 h64 as ⟨v14, s11, hinv11, h_v14⟩ growing hG carrying dropping h_v13 he_v14 e_v14 v13
              ite_done hinv11 hG with (native_ite_true_rep _ hx_14 h_v14)
            · ite_branch hbv_14
              step as ⟨e_v15, he_v15⟩
              store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s10 e_v15 (by rw [he_v15]; exact empty_args) hinv10 h64 as ⟨v15, s11, hinv11, h_v15⟩ growing hG carrying dropping h_v13 he_v15 hinv10 e_v15 s10 v13
              ite_done hinv11 hG with (native_ite_false_rep _ hx_14 h_v15))
          store_step with h_ite_v16 as ⟨v16, s11, hinv11, h_v16⟩ growing hG carrying dropping h_ite_v16 h_v13 hinv10 s10 v13
          ite_done hinv11 hG with (native_ite_true_rep _ hx_11 h_v16)
        · ite_branch hbv_11
          step as ⟨e_v17, he_v17⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s7 e_v17 (by rw [he_v17]; exact empty_args) hinv7 h64 as ⟨v17, s8, hinv8, h_v17⟩ growing hG carrying dropping h_v10 h_v3 he_v17 hinv7 e_v17 s7 v10 v3
          ite_done hinv8 hG with (native_ite_false_rep _ hx_11 h_v17))
      store_step with h_ite_v18 as ⟨v18, s8, hinv8, h_v18⟩ growing hG carrying dropping h_ite_v18 h_v10 h_v3 hinv7 s7 v10 v3
      ite_done hinv8 hG with (native_ite_true_rep _ hx_8 h_v18)
    · ite_branch hbv_8
      step as ⟨e_v19, he_v19⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s4 e_v19 (by rw [he_v19]; exact empty_args) hinv4 h64 as ⟨v19, s5, hinv5, h_v19⟩ growing hG carrying dropping h_v2 h_v3 h_v7 he_v19 hinv4 e_v19 s4 v2 v3 v7
      ite_done hinv5 hG with (native_ite_false_rep _ hx_8 h_v19))
  store_step with h_ite_v20 as ⟨v20, s5, hinv5, h_v20⟩ growing hG carrying dropping h_ite_v20 h_v2 h_v3 h_v7 hinv4 s4 v2 v3 v7
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
  store_step with ih.eo__24smtx_5ftypeof s v3 _ hinv h64 hrem h_v3 as ⟨v4, s1, hinv1, h_v4⟩ growing hG carrying h_v2 dropping h_a0 h_v1 h_v3 v1 v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s1 e_v5 (by rw [he_v5]; exact empty_args) hinv1 h64 as ⟨v5, s2, hinv2, h_v5⟩ growing hG carrying h_v2 h_v4 dropping he_v5 hinv1 e_v5 s1
  step as ⟨e_v6, he_v6⟩
  store_step with Store.native_spec_Teq s2 e_v6 (by rw [he_v6]; rfl) h_v4 h_v5 hinv2 h64 as ⟨v6, s3, hinv3, h_v6⟩ growing hG carrying h_v2 dropping h_v4 h_v5 he_v6 hinv2 e_v6 s2 v4 v5
  have h_ite_v9 := (show if_69_eo__24smtx_5ftypeof s3 v6 v2 ⦃ r s' => s'.Inv ∧ s3.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_69_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s3
    rcases Store.boolean_value_native h_v6 with ⟨hx_7, hbv_7⟩ | ⟨hx_7, hbv_7⟩
    · ite_branch hbv_7
      store_step with ih.eo__24smtx_5ftypeof_5fguard_5fwf s3 v2 v2 _ _ hinv3 h64 (hG.rem hrem) h_v2 h_v2 as ⟨v7, s4, hinv4, h_v7⟩ growing hG carrying dropping h_v2 h_v6 v2 v6
      ite_done hinv4 hG with (native_ite_true_rep _ hx_7 h_v7)
    · ite_branch hbv_7
      step as ⟨e_v8, he_v8⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s3 e_v8 (by rw [he_v8]; exact empty_args) hinv3 h64 as ⟨v8, s4, hinv4, h_v8⟩ growing hG carrying dropping h_v2 h_v6 he_v8 hinv3 e_v8 s3 v2 v6
      ite_done hinv4 hG with (native_ite_false_rep _ hx_7 h_v8))
  store_step with h_ite_v9 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying dropping h_ite_v9 h_v2 h_v6 hinv3 s3 v2 v6
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
  store_step with CtorSpec.eo__24emb_5ftsm_2eSet.construct s e_v2 (by rw [he_v2]; rfl) h_v1 hinv h64 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying h_v1 dropping h_a0 he_v2 e_v2
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eSet.construct s1 e_v3 (by rw [he_v3]; rfl) h_v1 hinv1 h64 as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying h_v2 dropping h_v1 he_v3 hinv1 e_v3 s1 v1
  store_step with ih.eo__24smtx_5ftypeof_5fguard_5fwf s2 v2 v3 _ _ hinv2 h64 (hG.rem hrem) h_v2 h_v3 as ⟨v4, s3, hinv3, h_v4⟩ growing hG carrying dropping h_v2 h_v3 hinv2 s2 v2 v3
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying h_v1 dropping h_a0
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eSet.construct s1 e_v3 (by rw [he_v3]; rfl) h_v2 hinv1 h64 as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying h_v1 dropping h_v2 he_v3 hinv1 e_v3 s1 v2
  store_step with ih.eo__24smtx_5ftypeof s2 v1 _ hinv2 h64 (hG.rem hrem) h_v1 as ⟨v4, s3, hinv3, h_v4⟩ growing hG carrying h_v3 dropping h_v1 hinv2 s2 v1
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eSet.construct s3 e_v5 (by rw [he_v5]; rfl) h_v4 hinv3 h64 as ⟨v5, s4, hinv4, h_v5⟩ growing hG carrying h_v3 dropping h_v4 he_v5 hinv3 e_v5 s3 v4
  store_step with ih.eo__24smtx_5ftypeof_5fguard_5fwf s4 v3 v5 _ _ hinv4 h64 (hG.rem hrem) h_v3 h_v5 as ⟨v6, s5, hinv5, h_v6⟩ growing hG carrying dropping h_v3 h_v5 hinv4 s4 v3 v5
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v2 dropping h_a0 h_v1 v1
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v3 dropping h_v2 hinv1 s1 v2
  store_step with ih.eo__24smtx_5ftypeof_5fsets_5fop_5f2 s2 v3 v4 _ _ hinv2 h64 (hG.rem hrem) h_v3 h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying dropping h_v3 h_v4 hinv2 s2 v3 v4
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v2 dropping h_a0 h_v1 v1
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v3 dropping h_v2 hinv1 s1 v2
  store_step with ih.eo__24smtx_5ftypeof_5fsets_5fop_5f2 s2 v3 v4 _ _ hinv2 h64 (hG.rem hrem) h_v3 h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying dropping h_v3 h_v4 hinv2 s2 v3 v4
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v2 dropping h_a0 h_v1 v1
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v3 dropping h_v2 hinv1 s1 v2
  store_step with ih.eo__24smtx_5ftypeof_5fsets_5fop_5f2 s2 v3 v4 _ _ hinv2 h64 (hG.rem hrem) h_v3 h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying dropping h_v3 h_v4 hinv2 s2 v3 v4
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v2 dropping h_a0 h_v1 v1
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v3 dropping h_v2 hinv1 s1 v2
  store_step with ih.eo__24smtx_5ftypeof_5fset_2emember s2 v3 v4 _ _ hinv2 h64 (hG.rem hrem) h_v3 h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying dropping h_v3 h_v4 hinv2 s2 v3 v4
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v2 dropping h_a0 h_v1 v1
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v3 dropping h_v2 hinv1 s1 v2
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s2 e_v5 (by rw [he_v5]; exact empty_args) hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_v3 h_v4 dropping he_v5 hinv2 e_v5 s2
  store_step with ih.eo__24smtx_5ftypeof_5fsets_5fop_5f2_5fret s3 v3 v4 v5 _ _ _ hinv3 h64 (hG.rem hrem) h_v3 h_v4 h_v5 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying dropping h_v3 h_v4 h_v5 hinv3 s3 v3 v4 v5
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v2 dropping h_a0 h_v1 v1
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v3 dropping h_v2 hinv1 s1 v2
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eReal.construct s2 e_v5 (by rw [he_v5]; exact empty_args) hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_v3 h_v4 dropping he_v5 hinv2 e_v5 s2
  store_step with ih.eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2_5fret s3 v3 v4 v5 _ _ _ hinv3 h64 (hG.rem hrem) h_v3 h_v4 h_v5 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying dropping h_v3 h_v4 h_v5 hinv3 s3 v3 v4 v5
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v2 dropping h_a0 h_v1 v1
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v3 dropping h_v2 hinv1 s1 v2
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eReal.construct s2 e_v5 (by rw [he_v5]; exact empty_args) hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_v3 h_v4 dropping he_v5 hinv2 e_v5 s2
  store_step with ih.eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2_5fret s3 v3 v4 v5 _ _ _ hinv3 h64 (hG.rem hrem) h_v3 h_v4 h_v5 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying dropping h_v3 h_v4 h_v5 hinv3 s3 v3 v4 v5
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
  store_step with ih.eo__24smtx_5ftypeof s v3 _ hinv h64 hrem h_v3 as ⟨v4, s1, hinv1, h_v4⟩ growing hG carrying h_v2 dropping h_a0 h_v1 h_v3 v1 v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s1 e_v5 (by rw [he_v5]; exact empty_args) hinv1 h64 as ⟨v5, s2, hinv2, h_v5⟩ growing hG carrying h_v2 h_v4 dropping he_v5 hinv1 e_v5 s1
  step as ⟨e_v6, he_v6⟩
  store_step with Store.native_spec_Teq s2 e_v6 (by rw [he_v6]; rfl) h_v4 h_v5 hinv2 h64 as ⟨v6, s3, hinv3, h_v6⟩ growing hG carrying h_v2 dropping h_v4 h_v5 he_v6 hinv2 e_v6 s2 v4 v5
  have h_ite_v10 := (show if_70_eo__24smtx_5ftypeof s3 v6 v2 ⦃ r s' => s'.Inv ∧ s3.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_70_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s3
    rcases Store.boolean_value_native h_v6 with ⟨hx_7, hbv_7⟩ | ⟨hx_7, hbv_7⟩
    · ite_branch hbv_7
      step as ⟨e_v7, he_v7⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s3 e_v7 (by rw [he_v7]; exact empty_args) hinv3 h64 as ⟨v7, s4, hinv4, h_v7⟩ growing hG carrying h_v2 dropping h_v6 he_v7 e_v7 v6
      store_step with ih.eo__24smtx_5ftypeof_5fguard_5fwf s4 v2 v7 _ _ hinv4 h64 (hG.rem hrem) h_v2 h_v7 as ⟨v8, s5, hinv5, h_v8⟩ growing hG carrying dropping h_v2 h_v7 v2 v7
      ite_done hinv5 hG with (native_ite_true_rep _ hx_7 h_v8)
    · ite_branch hbv_7
      step as ⟨e_v9, he_v9⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s3 e_v9 (by rw [he_v9]; exact empty_args) hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying dropping h_v2 h_v6 he_v9 hinv3 e_v9 s3 v2 v6
      ite_done hinv4 hG with (native_ite_false_rep _ hx_7 h_v9))
  store_step with h_ite_v10 as ⟨v10, s4, hinv4, h_v10⟩ growing hG carrying dropping h_ite_v10 h_v2 h_v6 hinv3 s3 v2 v6
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
  store_step with ih.eo__24smtx_5ftypeof s v3 _ hinv h64 hrem h_v3 as ⟨v4, s1, hinv1, h_v4⟩ growing hG carrying h_v2 dropping h_a0 h_v1 h_v3 v1 v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s1 e_v5 (by rw [he_v5]; exact empty_args) hinv1 h64 as ⟨v5, s2, hinv2, h_v5⟩ growing hG carrying h_v2 h_v4 dropping he_v5 hinv1 e_v5 s1
  step as ⟨e_v6, he_v6⟩
  store_step with Store.native_spec_Teq s2 e_v6 (by rw [he_v6]; rfl) h_v4 h_v5 hinv2 h64 as ⟨v6, s3, hinv3, h_v6⟩ growing hG carrying h_v2 dropping h_v4 h_v5 he_v6 hinv2 e_v6 s2 v4 v5
  have h_ite_v10 := (show if_71_eo__24smtx_5ftypeof s3 v6 v2 ⦃ r s' => s'.Inv ∧ s3.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_71_eo__24smtx_5ftypeof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s3
    rcases Store.boolean_value_native h_v6 with ⟨hx_7, hbv_7⟩ | ⟨hx_7, hbv_7⟩
    · ite_branch hbv_7
      step as ⟨e_v7, he_v7⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s3 e_v7 (by rw [he_v7]; exact empty_args) hinv3 h64 as ⟨v7, s4, hinv4, h_v7⟩ growing hG carrying h_v2 dropping h_v6 he_v7 e_v7 v6
      store_step with ih.eo__24smtx_5ftypeof_5fguard_5fwf s4 v2 v7 _ _ hinv4 h64 (hG.rem hrem) h_v2 h_v7 as ⟨v8, s5, hinv5, h_v8⟩ growing hG carrying dropping h_v2 h_v7 v2 v7
      ite_done hinv5 hG with (native_ite_true_rep _ hx_7 h_v8)
    · ite_branch hbv_7
      step as ⟨e_v9, he_v9⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s3 e_v9 (by rw [he_v9]; exact empty_args) hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying dropping h_v2 h_v6 he_v9 hinv3 e_v9 s3 v2 v6
      ite_done hinv4 hG with (native_ite_false_rep _ hx_7 h_v9))
  store_step with h_ite_v10 as ⟨v10, s4, hinv4, h_v10⟩ growing hG carrying dropping h_ite_v10 h_v2 h_v6 hinv3 s3 v2 v6
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
  store_step with ih.eo__24smtx_5ftypeof s v2 _ hinv h64 hrem h_v2 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v1 dropping h_a0 h_v2 v2
  store_step with ih.eo__24smtx_5ftypeof_5fint_5fto_5fbv s1 v1 v3 _ _ hinv1 h64 (hG.rem hrem) h_v1 h_v3 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying dropping h_v1 h_v3 hinv1 s1 v1 v3
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying dropping h_a0 h_v1 v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eInt.construct s1 e_v3 (by rw [he_v3]; exact empty_args) hinv1 h64 as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying h_v2 dropping he_v3 hinv1 e_v3 s1
  store_step with ih.eo__24smtx_5ftypeof_5fbv_5fop_5f1_5fret s2 v2 v3 _ _ hinv2 h64 (hG.rem hrem) h_v2 h_v3 as ⟨v4, s3, hinv3, h_v4⟩ growing hG carrying dropping h_v2 h_v3 hinv2 s2 v2 v3
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying dropping h_a0 h_v1 v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eInt.construct s1 e_v3 (by rw [he_v3]; exact empty_args) hinv1 h64 as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying h_v2 dropping he_v3 hinv1 e_v3 s1
  store_step with ih.eo__24smtx_5ftypeof_5fbv_5fop_5f1_5fret s2 v2 v3 _ _ hinv2 h64 (hG.rem hrem) h_v2 h_v3 as ⟨v4, s3, hinv3, h_v4⟩ growing hG carrying dropping h_v2 h_v3 hinv2 s2 v2 v3
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
  store_step with CtorSpec.eo__24emb_5ftsm_2eDatatype.construct s e_v4 (by rw [he_v4]; rfl) h_v1 h_v2 hinv h64 as ⟨v4, s1, hinv1, h_v4⟩ growing hG carrying h_v1 h_v2 h_v3 dropping h_a0 he_v4 e_v4
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eDatatype.construct s1 e_v5 (by rw [he_v5]; rfl) h_v1 h_v2 hinv1 h64 as ⟨v5, s2, hinv2, h_v5⟩ growing hG carrying h_v1 h_v2 h_v3 h_v4 dropping he_v5 hinv1 e_v5 s1
  store_step with ih.eo__24smtx_5fdd_5flookup s2 v1 v2 _ _ hinv2 h64 (hG.rem hrem) h_v1 h_v2 as ⟨v6, s3, hinv3, h_v6⟩ growing hG carrying h_v2 h_v3 h_v4 h_v5 dropping h_v1 hinv2 s2 v1
  store_step with ih.eo__24smtx_5fdt_5fresolve s3 v6 v2 _ _ hinv3 h64 (hG.rem hrem) h_v6 h_v2 as ⟨v7, s4, hinv4, h_v7⟩ growing hG carrying h_v3 h_v4 h_v5 dropping h_v2 h_v6 hinv3 s3 v2 v6
  store_step with ih.eo__24smtx_5ftypeof_5fdt_5fcons_5frec s4 v5 v7 v3 _ _ _ hinv4 h64 (hG.rem hrem) h_v5 h_v7 h_v3 as ⟨v8, s5, hinv5, h_v8⟩ growing hG carrying h_v4 dropping h_v3 h_v5 h_v7 hinv4 s4 v3 v5 v7
  store_step with ih.eo__24smtx_5ftypeof_5fguard_5fwf s5 v4 v8 _ _ hinv5 h64 (hG.rem hrem) h_v4 h_v8 as ⟨v9, s6, hinv6, h_v9⟩ growing hG carrying dropping h_v4 h_v8 hinv5 s5 v4 v8
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
  store_step with ih.eo__24smtx_5fret_5ftypeof_5fsel s v4 v5 v6 v7 _ _ _ _ hinv h64 hrem h_v4 h_v5 h_v6 h_v7 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_v2 h_v4 h_v5 h_v6 h_v7 dropping h_a0 h_v1 v1
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eDatatype.construct s1 e_v9 (by rw [he_v9]; rfl) h_v4 h_v5 hinv1 h64 as ⟨v9, s2, hinv2, h_v9⟩ growing hG carrying h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 dropping he_v9 hinv1 e_v9 s1
  store_step with ih.eo__24smtx_5fret_5ftypeof_5fsel s2 v4 v5 v6 v7 _ _ _ _ hinv2 h64 (hG.rem hrem) h_v4 h_v5 h_v6 h_v7 as ⟨v10, s3, hinv3, h_v10⟩ growing hG carrying h_v2 h_v8 h_v9 dropping h_v4 h_v5 h_v6 h_v7 hinv2 s2 v4 v5 v6 v7
  step as ⟨e_v11, he_v11⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eFunType.construct s3 e_v11 (by rw [he_v11]; rfl) h_v9 h_v10 hinv3 h64 as ⟨v11, s4, hinv4, h_v11⟩ growing hG carrying h_v2 h_v8 dropping h_v10 h_v9 he_v11 hinv3 e_v11 s3 v10 v9
  store_step with ih.eo__24smtx_5ftypeof s4 v2 _ hinv4 h64 (hG.rem hrem) h_v2 as ⟨v12, s5, hinv5, h_v12⟩ growing hG carrying h_v8 h_v11 dropping h_v2 hinv4 s4 v2
  store_step with ih.eo__24smtx_5ftypeof_5fapply s5 v11 v12 _ _ hinv5 h64 (hG.rem hrem) h_v11 h_v12 as ⟨v13, s6, hinv6, h_v13⟩ growing hG carrying h_v8 dropping h_v11 h_v12 hinv5 s5 v11 v12
  store_step with ih.eo__24smtx_5ftypeof_5fguard_5fwf s6 v8 v13 _ _ hinv6 h64 (hG.rem hrem) h_v8 h_v13 as ⟨v14, s7, hinv7, h_v14⟩ growing hG carrying dropping h_v13 h_v8 hinv6 s6 v13 v8
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
  store_step with CtorSpec.eo__24emb_5ftsm_2eDatatype.construct s e_v7 (by rw [he_v7]; rfl) h_v4 h_v5 hinv h64 as ⟨v7, s1, hinv1, h_v7⟩ growing hG carrying h_v2 h_v4 h_v5 h_v6 dropping h_a0 h_v1 he_v7 e_v7 v1
  store_step with ih.eo__24smtx_5fdd_5flookup s1 v4 v5 _ _ hinv1 h64 (hG.rem hrem) h_v4 h_v5 as ⟨v8, s2, hinv2, h_v8⟩ growing hG carrying h_v2 h_v4 h_v5 h_v6 h_v7 dropping hinv1 s1
  store_step with ih.eo__24smtx_5fdt_5fresolve s2 v8 v5 _ _ hinv2 h64 (hG.rem hrem) h_v8 h_v5 as ⟨v9, s3, hinv3, h_v9⟩ growing hG carrying h_v2 h_v4 h_v5 h_v6 h_v7 dropping h_v8 hinv2 s2 v8
  store_step with ih.eo__24smtx_5ftypeof_5fdt_5fcons_5frec s3 v7 v9 v6 _ _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v9 h_v6 as ⟨v10, s4, hinv4, h_v10⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_v6 h_v7 h_v9 hinv3 s3 v6 v7 v9
  step as ⟨e_v11, he_v11⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eDatatype.construct s4 e_v11 (by rw [he_v11]; rfl) h_v4 h_v5 hinv4 h64 as ⟨v11, s5, hinv5, h_v11⟩ growing hG carrying h_v2 h_v10 dropping h_v4 h_v5 he_v11 hinv4 e_v11 s4 v4 v5
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s5 e_v12 (by rw [he_v12]; exact empty_args) hinv5 h64 as ⟨v12, s6, hinv6, h_v12⟩ growing hG carrying h_v2 h_v10 h_v11 dropping he_v12 hinv5 e_v12 s5
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eFunType.construct s6 e_v13 (by rw [he_v13]; rfl) h_v11 h_v12 hinv6 h64 as ⟨v13, s7, hinv7, h_v13⟩ growing hG carrying h_v2 h_v10 dropping h_v11 h_v12 he_v13 hinv6 e_v13 s6 v11 v12
  store_step with ih.eo__24smtx_5ftypeof s7 v2 _ hinv7 h64 (hG.rem hrem) h_v2 as ⟨v14, s8, hinv8, h_v14⟩ growing hG carrying h_v10 h_v13 dropping h_v2 hinv7 s7 v2
  store_step with ih.eo__24smtx_5ftypeof_5fapply s8 v13 v14 _ _ hinv8 h64 (hG.rem hrem) h_v13 h_v14 as ⟨v15, s9, hinv9, h_v15⟩ growing hG carrying h_v10 dropping h_v13 h_v14 hinv8 s8 v13 v14
  store_step with ih.eo__24smtx_5ftypeof_5fguard s9 v10 v15 _ _ hinv9 h64 (hG.rem hrem) h_v10 h_v15 as ⟨v16, s10, hinv10, h_v16⟩ growing hG carrying dropping h_v10 h_v15 hinv9 s9 v10 v15
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
  store_step with ih.eo__24smtx_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v2 dropping h_a0 h_v1 v1
  store_step with ih.eo__24smtx_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v3 dropping h_v2 hinv1 s1 v2
  store_step with ih.eo__24smtx_5ftypeof_5fapply s2 v3 v4 _ _ hinv2 h64 (hG.rem hrem) h_v3 h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying dropping h_v3 h_v4 hinv2 s2 v3 v4
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
  store_step with ih.eo__24smtx_5ftypeof_5fguard_5fwf s v2 v2 _ _ hinv h64 hrem h_v2 h_v2 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying dropping h_a0 h_v1 h_v2 v1 v2
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
  store_step with ih.eo__24smtx_5ftypeof_5fguard_5fwf s v2 v2 _ _ hinv h64 hrem h_v2 h_v2 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying dropping h_a0 h_v1 h_v2 v1 v2
  case_done hinv1 hG with h_v3 in EoCases.__smtx_typeof.case_146 using

end pathos_compiled_checker
