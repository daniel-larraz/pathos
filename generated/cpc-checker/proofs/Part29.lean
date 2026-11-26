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

theorem case_0_eo__24smtx_5ftypeof_5fextract_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    case_0_eo__24smtx_5ftypeof_5fextract s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof_extract.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof_extract.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24smtx_5ftypeof_5fextract
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2eNumeral.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__smtx_typeof_extract.case_0
  pat_destruct CtorSpec.eo__24emb_5fsm_2eNumeral.destruct h_a1 as ⟨v3, x_v3, h_v3⟩ else hinv hG in EoCases.__smtx_typeof_extract.case_0
  pat_destruct CtorSpec.eo__24emb_5ftsm_2eBitVec.destruct h_a2 as ⟨v5, x_v5, h_v5⟩ else hinv hG in EoCases.__smtx_typeof_extract.case_0
  simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.raw_int_u32_spec s 0#u32 (0) (by scalar_tac) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v5
  step as ⟨e_v7, he_v7⟩
  store_step with Store.native_spec_zleq s1 e_v7 (by rw [he_v7]; rfl) h_v6 h_v3 hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v5 h_v6
  rw [← Bridge.native_zleq] at h_v7
  have h_ite_v27 := (show if_2_eo__24smtx_5ftypeof_5fextract s2 v7 v5 v1 v3 ⦃ r s' => s'.Inv ∧ s2.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_2_eo__24smtx_5ftypeof_5fextract
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s2
    rcases Store.boolean_value_native h_v7 with ⟨hx_8, hbv_8⟩ | ⟨hx_8, hbv_8⟩
    · ite_branch hbv_8
      step as ⟨e_v8, he_v8⟩
      store_step with Store.native_spec_nat_to_int s2 e_v8 (by rw [he_v8]; rfl) h_v5 hinv2 h64 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v5 h_v6 h_v7
      rw [← Bridge.native_nat_to_int] at h_v8
      step as ⟨e_v9, he_v9⟩
      store_step with Store.native_spec_zlt s3 e_v9 (by rw [he_v9]; rfl) h_v1 h_v8 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v5 h_v6 h_v7 h_v8
      rw [← Bridge.native_zlt] at h_v9
      have h_ite_v25 := (show if_1_eo__24smtx_5ftypeof_5fextract s4 v9 v1 v3 ⦃ r s' => s'.Inv ∧ s4.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_1_eo__24smtx_5ftypeof_5fextract
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s4
        rcases Store.boolean_value_native h_v9 with ⟨hx_10, hbv_10⟩ | ⟨hx_10, hbv_10⟩
        · ite_branch hbv_10
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.raw_int_u32_spec s4 0#u32 (0) (by scalar_tac) hinv4 h64 as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v5 h_v6 h_v7 h_v8 h_v9
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.raw_int_u32_spec s5 1#u32 (1) (by scalar_tac) hinv5 h64 as ⟨v11, s6, hinv6, h_v11⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
          step as ⟨e_v12, he_v12⟩
          store_step with Store.native_spec_zplus s6 e_v12 (by rw [he_v12]; rfl) h_v1 h_v11 hinv6 h64 as ⟨v12, s7, hinv7, h_v12⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11
          rw [← Bridge.native_zplus] at h_v12
          step as ⟨e_v13, he_v13⟩
          store_step with Store.native_spec_zneg s7 e_v13 (by rw [he_v13]; rfl) h_v3 hinv7 h64 as ⟨v13, s8, hinv8, h_v13⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
          rw [← Bridge.native_zneg] at h_v13
          step as ⟨e_v14, he_v14⟩
          store_step with Store.native_spec_zplus s8 e_v14 (by rw [he_v14]; rfl) h_v12 h_v13 hinv8 h64 as ⟨v14, s9, hinv9, h_v14⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13
          rw [← Bridge.native_zplus] at h_v14
          step as ⟨e_v15, he_v15⟩
          store_step with Store.native_spec_zlt s9 e_v15 (by rw [he_v15]; rfl) h_v10 h_v14 hinv9 h64 as ⟨v15, s10, hinv10, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14
          rw [← Bridge.native_zlt] at h_v15
          have h_ite_v23 := (show if_0_eo__24smtx_5ftypeof_5fextract s10 v15 v1 v3 ⦃ r s' => s'.Inv ∧ s10.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
            unfold if_0_eo__24smtx_5ftypeof_5fextract
            have hrem := (hG.rem hrem)
            have hG := Store.Grows.refl s10
            rcases Store.boolean_value_native h_v15 with ⟨hx_16, hbv_16⟩ | ⟨hx_16, hbv_16⟩
            · ite_branch hbv_16
              try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
              store_step with Store.raw_int_u32_spec s10 1#u32 (1) (by scalar_tac) hinv10 h64 as ⟨v16, s11, hinv11, h_v16⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15
              step as ⟨e_v17, he_v17⟩
              store_step with Store.native_spec_zplus s11 e_v17 (by rw [he_v17]; rfl) h_v1 h_v16 hinv11 h64 as ⟨v17, s12, hinv12, h_v17⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16
              rw [← Bridge.native_zplus] at h_v17
              step as ⟨e_v18, he_v18⟩
              store_step with Store.native_spec_zneg s12 e_v18 (by rw [he_v18]; rfl) h_v3 hinv12 h64 as ⟨v18, s13, hinv13, h_v18⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17
              rw [← Bridge.native_zneg] at h_v18
              step as ⟨e_v19, he_v19⟩
              store_step with Store.native_spec_zplus s13 e_v19 (by rw [he_v19]; rfl) h_v17 h_v18 hinv13 h64 as ⟨v19, s14, hinv14, h_v19⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18
              rw [← Bridge.native_zplus] at h_v19
              step as ⟨e_v20, he_v20⟩
              store_step with Store.native_spec_int_to_nat s14 e_v20 (by rw [he_v20]; rfl) h_v19 hinv14 h64 as ⟨v20, s15, hinv15, h_v20⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19
              rw [← Bridge.native_int_to_nat] at h_v20
              step as ⟨e_v21, he_v21⟩
              store_step with CtorSpec.eo__24emb_5ftsm_2eBitVec.construct s15 e_v21 (by rw [he_v21]; rfl) h_v20 hinv15 h64 as ⟨v21, s16, hinv16, h_v21⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20
              ite_done hinv16 hG with (native_ite_true_rep _ hx_16 h_v21)
            · ite_branch hbv_16
              step as ⟨e_v22, he_v22⟩
              store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s10 e_v22 (by rw [he_v22]; exact empty_args) hinv10 h64 as ⟨v22, s11, hinv11, h_v22⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15
              ite_done hinv11 hG with (native_ite_false_rep _ hx_16 h_v22))
          store_step with h_ite_v23 as ⟨v23, s11, hinv11, h_v23⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15
          ite_done hinv11 hG with (native_ite_true_rep _ hx_10 h_v23)
        · ite_branch hbv_10
          step as ⟨e_v24, he_v24⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s4 e_v24 (by rw [he_v24]; exact empty_args) hinv4 h64 as ⟨v24, s5, hinv5, h_v24⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v5 h_v6 h_v7 h_v8 h_v9
          ite_done hinv5 hG with (native_ite_false_rep _ hx_10 h_v24))
      store_step with h_ite_v25 as ⟨v25, s5, hinv5, h_v25⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v5 h_v6 h_v7 h_v8 h_v9
      ite_done hinv5 hG with (native_ite_true_rep _ hx_8 h_v25)
    · ite_branch hbv_8
      step as ⟨e_v26, he_v26⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s2 e_v26 (by rw [he_v26]; exact empty_args) hinv2 h64 as ⟨v26, s3, hinv3, h_v26⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v5 h_v6 h_v7
      ite_done hinv3 hG with (native_ite_false_rep _ hx_8 h_v26))
  store_step with h_ite_v27 as ⟨v27, s3, hinv3, h_v27⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v5 h_v6 h_v7
  case_done hinv3 hG with h_v27 in EoCases.__smtx_typeof_extract.case_0 using

theorem case_1_eo__24smtx_5ftypeof_5fextract_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    case_1_eo__24smtx_5ftypeof_5fextract s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof_extract.case_1 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof_extract.case_1 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24smtx_5ftypeof_5fextract
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2
  case_done hinv1 hG with h_v0 in EoCases.__smtx_typeof_extract.case_1 using

/-- logos's `__smtx_typeof_extract` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24smtx_5ftypeof_5fextract.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __smtx_typeof_extract x_a0 x_a1 x_a2 =
      (firstSome [EoCases.__smtx_typeof_extract.case_0 x_a0 x_a1 x_a2, EoCases.__smtx_typeof_extract.case_1 x_a0 x_a1 x_a2] default) := by
  conv => lhs; unfold __smtx_typeof_extract
  unfold EoCases.__smtx_typeof_extract.case_0 EoCases.__smtx_typeof_extract.case_1
  logos_eq

theorem body_eo__24smtx_5ftypeof_5fextract_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24smtx_5ftypeof_5fextract s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_typeof_extract x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24smtx_5ftypeof_5fextract.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24smtx_5ftypeof_5fextract
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24smtx_5ftypeof_5fextract_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 using
  case_step with case_1_eo__24smtx_5ftypeof_5fextract_spec n ih s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 using hc0
  body_stuck hinv2 hG using hc0 hc1 in EoCases.__smtx_typeof_extract.case_0 EoCases.__smtx_typeof_extract.case_1 splitting x_a0 x_a1 x_a2

theorem eo__24smtx_5ftypeof_5fextract_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24smtx_5ftypeof_5fextract.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24smtx_5ftypeof_5fextract
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24smtx_5ftypeof_5fextract s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__smtx_typeof_extract x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24smtx_5ftypeof_5fextract_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24smtx_5ftypeof_5fguard_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_0_eo__24smtx_5ftypeof_5fguard s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof_guard.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof_guard.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24smtx_5ftypeof_5fguard
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  step as ⟨e_v1, he_v1⟩
  store_step with Store.native_spec_Teq s1 e_v1 (by rw [he_v1]; rfl) h_a0 h_v0 hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  have h_ite_v3 := (show if_0_eo__24smtx_5ftypeof_5fguard s2 v1 a1 ⦃ r s' => s'.Inv ∧ s2.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_0_eo__24smtx_5ftypeof_5fguard
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s2
    rcases Store.boolean_value_native h_v1 with ⟨hx_2, hbv_2⟩ | ⟨hx_2, hbv_2⟩
    · ite_branch hbv_2
      step as ⟨e_v2, he_v2⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1
      ite_done hinv3 hG with (native_ite_true_rep _ hx_2 h_v2)
    · ite_branch hbv_2
      ite_done hinv2 hG with (native_ite_false_rep _ hx_2 h_a1))
  store_step with h_ite_v3 as ⟨v3, s3, hinv3, h_v3⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1
  case_done hinv3 hG with h_v3 in EoCases.__smtx_typeof_guard.case_0 using

/-- logos's `__smtx_typeof_guard` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24smtx_5ftypeof_5fguard.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __smtx_typeof_guard x_a0 x_a1 =
      (firstSome [EoCases.__smtx_typeof_guard.case_0 x_a0 x_a1] default) := by
  conv => lhs; unfold __smtx_typeof_guard
  unfold EoCases.__smtx_typeof_guard.case_0
  logos_eq

theorem body_eo__24smtx_5ftypeof_5fguard_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24smtx_5ftypeof_5fguard s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_typeof_guard x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24smtx_5ftypeof_5fguard.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24smtx_5ftypeof_5fguard
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24smtx_5ftypeof_5fguard_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using
  body_stuck hinv1 hG using hc0 in EoCases.__smtx_typeof_guard.case_0 splitting x_a0 x_a1

theorem eo__24smtx_5ftypeof_5fguard_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24smtx_5ftypeof_5fguard.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24smtx_5ftypeof_5fguard
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24smtx_5ftypeof_5fguard s1 a0 a1) (fun s' t => Represents.rep s' t (__smtx_typeof_guard x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24smtx_5ftypeof_5fguard_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24smtx_5ftypeof_5fguard_5fwf_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_0_eo__24smtx_5ftypeof_5fguard_5fwf s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof_guard_wf.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof_guard_wf.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24smtx_5ftypeof_5fguard_5fwf
  have hG := Store.Grows.refl s
  store_step with ih.eo__24smtx_5ftype_5fwf s a0 _ hinv h64 hrem h_a0 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  have h_ite_v2 := (show if_0_eo__24smtx_5ftypeof_5fguard_5fwf s1 v0 a1 ⦃ r s' => s'.Inv ∧ s1.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_0_eo__24smtx_5ftypeof_5fguard_5fwf
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s1
    rcases Store.boolean_value_native h_v0 with ⟨hx_1, hbv_1⟩ | ⟨hx_1, hbv_1⟩
    · ite_branch hbv_1
      ite_done hinv1 hG with (native_ite_true_rep _ hx_1 h_a1)
    · ite_branch hbv_1
      step as ⟨e_v1, he_v1⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
      ite_done hinv2 hG with (native_ite_false_rep _ hx_1 h_v1))
  store_step with h_ite_v2 as ⟨v2, s2, hinv2, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0
  case_done hinv2 hG with h_v2 in EoCases.__smtx_typeof_guard_wf.case_0 using

/-- logos's `__smtx_typeof_guard_wf` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24smtx_5ftypeof_5fguard_5fwf.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __smtx_typeof_guard_wf x_a0 x_a1 =
      (firstSome [EoCases.__smtx_typeof_guard_wf.case_0 x_a0 x_a1] default) := by
  conv => lhs; unfold __smtx_typeof_guard_wf
  unfold EoCases.__smtx_typeof_guard_wf.case_0
  logos_eq

theorem body_eo__24smtx_5ftypeof_5fguard_5fwf_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24smtx_5ftypeof_5fguard_5fwf s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_typeof_guard_wf x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24smtx_5ftypeof_5fguard_5fwf.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24smtx_5ftypeof_5fguard_5fwf
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24smtx_5ftypeof_5fguard_5fwf_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using
  body_stuck hinv1 hG using hc0 in EoCases.__smtx_typeof_guard_wf.case_0 splitting x_a0 x_a1

theorem eo__24smtx_5ftypeof_5fguard_5fwf_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24smtx_5ftypeof_5fguard_5fwf.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24smtx_5ftypeof_5fguard_5fwf
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24smtx_5ftypeof_5fguard_5fwf s1 a0 a1) (fun s' t => Represents.rep s' t (__smtx_typeof_guard_wf x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24smtx_5ftypeof_5fguard_5fwf_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24smtx_5ftypeof_5fint_5fto_5fbv_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_0_eo__24smtx_5ftypeof_5fint_5fto_5fbv s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof_int_to_bv.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof_int_to_bv.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24smtx_5ftypeof_5fint_5fto_5fbv
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2eNumeral.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__smtx_typeof_int_to_bv.case_0
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eInt.construct s e_v2 (by rw [he_v2]; exact empty_args) hinv h64 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying h_a0 h_a1 h_v1
  pat_same a1 v2 with h_a1 h_v2 using hinv1 else hinv1 hG in EoCases.__smtx_typeof_int_to_bv.case_0
  simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.raw_int_u32_spec s1 0#u32 (0) (by scalar_tac) hinv1 h64 as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2
  step as ⟨e_v4, he_v4⟩
  store_step with Store.native_spec_zleq s2 e_v4 (by rw [he_v4]; rfl) h_v3 h_v1 hinv2 h64 as ⟨v4, s3, hinv3, h_v4⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3
  rw [← Bridge.native_zleq] at h_v4
  have h_ite_v8 := (show if_0_eo__24smtx_5ftypeof_5fint_5fto_5fbv s3 v4 v1 ⦃ r s' => s'.Inv ∧ s3.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_0_eo__24smtx_5ftypeof_5fint_5fto_5fbv
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s3
    rcases Store.boolean_value_native h_v4 with ⟨hx_5, hbv_5⟩ | ⟨hx_5, hbv_5⟩
    · ite_branch hbv_5
      step as ⟨e_v5, he_v5⟩
      store_step with Store.native_spec_int_to_nat s3 e_v5 (by rw [he_v5]; rfl) h_v1 hinv3 h64 as ⟨v5, s4, hinv4, h_v5⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4
      rw [← Bridge.native_int_to_nat] at h_v5
      step as ⟨e_v6, he_v6⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eBitVec.construct s4 e_v6 (by rw [he_v6]; rfl) h_v5 hinv4 h64 as ⟨v6, s5, hinv5, h_v6⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4 h_v5
      ite_done hinv5 hG with (native_ite_true_rep _ hx_5 h_v6)
    · ite_branch hbv_5
      step as ⟨e_v7, he_v7⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s3 e_v7 (by rw [he_v7]; exact empty_args) hinv3 h64 as ⟨v7, s4, hinv4, h_v7⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4
      ite_done hinv4 hG with (native_ite_false_rep _ hx_5 h_v7))
  store_step with h_ite_v8 as ⟨v8, s4, hinv4, h_v8⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4
  case_done hinv4 hG with h_v8 in EoCases.__smtx_typeof_int_to_bv.case_0 using

theorem case_1_eo__24smtx_5ftypeof_5fint_5fto_5fbv_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_1_eo__24smtx_5ftypeof_5fint_5fto_5fbv s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof_int_to_bv.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof_int_to_bv.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24smtx_5ftypeof_5fint_5fto_5fbv
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  case_done hinv1 hG with h_v0 in EoCases.__smtx_typeof_int_to_bv.case_1 using

/-- logos's `__smtx_typeof_int_to_bv` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24smtx_5ftypeof_5fint_5fto_5fbv.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __smtx_typeof_int_to_bv x_a0 x_a1 =
      (firstSome [EoCases.__smtx_typeof_int_to_bv.case_0 x_a0 x_a1, EoCases.__smtx_typeof_int_to_bv.case_1 x_a0 x_a1] default) := by
  conv => lhs; unfold __smtx_typeof_int_to_bv
  unfold EoCases.__smtx_typeof_int_to_bv.case_0 EoCases.__smtx_typeof_int_to_bv.case_1
  logos_eq

theorem body_eo__24smtx_5ftypeof_5fint_5fto_5fbv_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24smtx_5ftypeof_5fint_5fto_5fbv s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_typeof_int_to_bv x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24smtx_5ftypeof_5fint_5fto_5fbv.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24smtx_5ftypeof_5fint_5fto_5fbv
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24smtx_5ftypeof_5fint_5fto_5fbv_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using
  case_step with case_1_eo__24smtx_5ftypeof_5fint_5fto_5fbv_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 using hc0
  body_stuck hinv2 hG using hc0 hc1 in EoCases.__smtx_typeof_int_to_bv.case_0 EoCases.__smtx_typeof_int_to_bv.case_1 splitting x_a0 x_a1

theorem eo__24smtx_5ftypeof_5fint_5fto_5fbv_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24smtx_5ftypeof_5fint_5fto_5fbv.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24smtx_5ftypeof_5fint_5fto_5fbv
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24smtx_5ftypeof_5fint_5fto_5fbv s1 a0 a1) (fun s' t => Represents.rep s' t (__smtx_typeof_int_to_bv x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24smtx_5ftypeof_5fint_5fto_5fbv_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24smtx_5ftypeof_5fite_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    case_0_eo__24smtx_5ftypeof_5fite s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof_ite.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof_ite.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24smtx_5ftypeof_5fite
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__smtx_typeof_ite.case_0
  step as ⟨e_v1, he_v1⟩
  store_step with Store.native_spec_Teq s1 e_v1 (by rw [he_v1]; rfl) h_a1 h_a2 hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0
  have h_ite_v3 := (show if_0_eo__24smtx_5ftypeof_5fite s2 v1 a1 ⦃ r s' => s'.Inv ∧ s2.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_0_eo__24smtx_5ftypeof_5fite
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s2
    rcases Store.boolean_value_native h_v1 with ⟨hx_2, hbv_2⟩ | ⟨hx_2, hbv_2⟩
    · ite_branch hbv_2
      ite_done hinv2 hG with (native_ite_true_rep _ hx_2 h_a1)
    · ite_branch hbv_2
      step as ⟨e_v2, he_v2⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1
      ite_done hinv3 hG with (native_ite_false_rep _ hx_2 h_v2))
  store_step with h_ite_v3 as ⟨v3, s3, hinv3, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1
  case_done hinv3 hG with h_v3 in EoCases.__smtx_typeof_ite.case_0 using

theorem case_1_eo__24smtx_5ftypeof_5fite_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    case_1_eo__24smtx_5ftypeof_5fite s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof_ite.case_1 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof_ite.case_1 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24smtx_5ftypeof_5fite
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2
  case_done hinv1 hG with h_v0 in EoCases.__smtx_typeof_ite.case_1 using

/-- logos's `__smtx_typeof_ite` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24smtx_5ftypeof_5fite.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __smtx_typeof_ite x_a0 x_a1 x_a2 =
      (firstSome [EoCases.__smtx_typeof_ite.case_0 x_a0 x_a1 x_a2, EoCases.__smtx_typeof_ite.case_1 x_a0 x_a1 x_a2] default) := by
  conv => lhs; unfold __smtx_typeof_ite
  unfold EoCases.__smtx_typeof_ite.case_0 EoCases.__smtx_typeof_ite.case_1
  logos_eq

theorem body_eo__24smtx_5ftypeof_5fite_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24smtx_5ftypeof_5fite s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_typeof_ite x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24smtx_5ftypeof_5fite.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24smtx_5ftypeof_5fite
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24smtx_5ftypeof_5fite_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 using
  case_step with case_1_eo__24smtx_5ftypeof_5fite_spec n ih s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 using hc0
  body_stuck hinv2 hG using hc0 hc1 in EoCases.__smtx_typeof_ite.case_0 EoCases.__smtx_typeof_ite.case_1 splitting x_a0 x_a1 x_a2

theorem eo__24smtx_5ftypeof_5fite_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24smtx_5ftypeof_5fite.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24smtx_5ftypeof_5fite
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24smtx_5ftypeof_5fite s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__smtx_typeof_ite x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24smtx_5ftypeof_5fite_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24smtx_5ftypeof_5fmap_5fdiff_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_0_eo__24smtx_5ftypeof_5fmap_5fdiff s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof_map_diff.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof_map_diff.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24smtx_5ftypeof_5fmap_5fdiff
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5ftsm_2eMap.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof_map_diff.case_0
  pat_destruct CtorSpec.eo__24emb_5ftsm_2eMap.destruct h_a1 as ⟨v4, x_v4, h_v4⟩ ⟨v5, x_v5, h_v5⟩ else hinv hG in EoCases.__smtx_typeof_map_diff.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with Store.native_spec_Teq s e_v6 (by rw [he_v6]; rfl) h_v1 h_v4 hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5
  step as ⟨e_v7, he_v7⟩
  store_step with Store.native_spec_Teq s1 e_v7 (by rw [he_v7]; rfl) h_v2 h_v5 hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6
  step as ⟨e_v8, he_v8⟩
  store_step with Store.native_spec_and s2 e_v8 (by rw [he_v8]; rfl) h_v6 h_v7 hinv2 h64 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  rw [← Bridge.native_and] at h_v8
  have h_ite_v10 := (show if_0_eo__24smtx_5ftypeof_5fmap_5fdiff s3 v8 v1 ⦃ r s' => s'.Inv ∧ s3.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_0_eo__24smtx_5ftypeof_5fmap_5fdiff
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s3
    rcases Store.boolean_value_native h_v8 with ⟨hx_9, hbv_9⟩ | ⟨hx_9, hbv_9⟩
    · ite_branch hbv_9
      ite_done hinv3 hG with (native_ite_true_rep _ hx_9 h_v1)
    · ite_branch hbv_9
      step as ⟨e_v9, he_v9⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s3 e_v9 (by rw [he_v9]; exact empty_args) hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
      ite_done hinv4 hG with (native_ite_false_rep _ hx_9 h_v9))
  store_step with h_ite_v10 as ⟨v10, s4, hinv4, h_v10⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v10 in EoCases.__smtx_typeof_map_diff.case_0 using

theorem case_1_eo__24smtx_5ftypeof_5fmap_5fdiff_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_1_eo__24smtx_5ftypeof_5fmap_5fdiff s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof_map_diff.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof_map_diff.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24smtx_5ftypeof_5fmap_5fdiff
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5ftsm_2eSet.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__smtx_typeof_map_diff.case_1
  pat_destruct CtorSpec.eo__24emb_5ftsm_2eSet.destruct h_a1 as ⟨v3, x_v3, h_v3⟩ else hinv hG in EoCases.__smtx_typeof_map_diff.case_1
  step as ⟨e_v4, he_v4⟩
  store_step with Store.native_spec_Teq s e_v4 (by rw [he_v4]; rfl) h_v1 h_v3 hinv h64 as ⟨v4, s1, hinv1, h_v4⟩ growing hG carrying h_a0 h_a1 h_v1 h_v3
  have h_ite_v6 := (show if_1_eo__24smtx_5ftypeof_5fmap_5fdiff s1 v4 v1 ⦃ r s' => s'.Inv ∧ s1.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_1_eo__24smtx_5ftypeof_5fmap_5fdiff
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s1
    rcases Store.boolean_value_native h_v4 with ⟨hx_5, hbv_5⟩ | ⟨hx_5, hbv_5⟩
    · ite_branch hbv_5
      ite_done hinv1 hG with (native_ite_true_rep _ hx_5 h_v1)
    · ite_branch hbv_5
      step as ⟨e_v5, he_v5⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s1 e_v5 (by rw [he_v5]; exact empty_args) hinv1 h64 as ⟨v5, s2, hinv2, h_v5⟩ growing hG carrying h_a0 h_a1 h_v1 h_v3 h_v4
      ite_done hinv2 hG with (native_ite_false_rep _ hx_5 h_v5))
  store_step with h_ite_v6 as ⟨v6, s2, hinv2, h_v6⟩ growing hG carrying h_a0 h_a1 h_v1 h_v3 h_v4
  case_done hinv2 hG with h_v6 in EoCases.__smtx_typeof_map_diff.case_1 using

theorem case_2_eo__24smtx_5ftypeof_5fmap_5fdiff_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_2_eo__24smtx_5ftypeof_5fmap_5fdiff s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof_map_diff.case_2 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof_map_diff.case_2 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24smtx_5ftypeof_5fmap_5fdiff
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  case_done hinv1 hG with h_v0 in EoCases.__smtx_typeof_map_diff.case_2 using

/-- logos's `__smtx_typeof_map_diff` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24smtx_5ftypeof_5fmap_5fdiff.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __smtx_typeof_map_diff x_a0 x_a1 =
      (firstSome [EoCases.__smtx_typeof_map_diff.case_0 x_a0 x_a1, EoCases.__smtx_typeof_map_diff.case_1 x_a0 x_a1, EoCases.__smtx_typeof_map_diff.case_2 x_a0 x_a1] default) := by
  conv => lhs; unfold __smtx_typeof_map_diff
  unfold EoCases.__smtx_typeof_map_diff.case_0 EoCases.__smtx_typeof_map_diff.case_1 EoCases.__smtx_typeof_map_diff.case_2
  logos_eq

theorem body_eo__24smtx_5ftypeof_5fmap_5fdiff_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24smtx_5ftypeof_5fmap_5fdiff s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_typeof_map_diff x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24smtx_5ftypeof_5fmap_5fdiff.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24smtx_5ftypeof_5fmap_5fdiff
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24smtx_5ftypeof_5fmap_5fdiff_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using
  case_step with case_1_eo__24smtx_5ftypeof_5fmap_5fdiff_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 using hc0
  case_step with case_2_eo__24smtx_5ftypeof_5fmap_5fdiff_spec n ih s2 a0 a1 x_a0 x_a1 hinv2 h64 (hG.rem hrem) h_a0 h_a1
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0 h_a1 using hc0 hc1
  body_stuck hinv3 hG using hc0 hc1 hc2 in EoCases.__smtx_typeof_map_diff.case_0 EoCases.__smtx_typeof_map_diff.case_1 EoCases.__smtx_typeof_map_diff.case_2 splitting x_a0 x_a1

theorem eo__24smtx_5ftypeof_5fmap_5fdiff_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24smtx_5ftypeof_5fmap_5fdiff.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24smtx_5ftypeof_5fmap_5fdiff
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24smtx_5ftypeof_5fmap_5fdiff s1 a0 a1) (fun s' t => Represents.rep s' t (__smtx_typeof_map_diff x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24smtx_5ftypeof_5fmap_5fdiff_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24smtx_5ftypeof_5fre_2e_5e_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_0_eo__24smtx_5ftypeof_5fre_2e_5e s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof_re_exp.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof_re_exp.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24smtx_5ftypeof_5fre_2e_5e
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2eNumeral.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__smtx_typeof_re_exp.case_0
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eRegLan.construct s e_v2 (by rw [he_v2]; exact empty_args) hinv h64 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying h_a0 h_a1 h_v1
  pat_same a1 v2 with h_a1 h_v2 using hinv1 else hinv1 hG in EoCases.__smtx_typeof_re_exp.case_0
  simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.raw_int_u32_spec s1 0#u32 (0) (by scalar_tac) hinv1 h64 as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2
  step as ⟨e_v4, he_v4⟩
  store_step with Store.native_spec_zleq s2 e_v4 (by rw [he_v4]; rfl) h_v3 h_v1 hinv2 h64 as ⟨v4, s3, hinv3, h_v4⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3
  rw [← Bridge.native_zleq] at h_v4
  have h_ite_v7 := (show if_0_eo__24smtx_5ftypeof_5fre_2e_5e s3 v4 ⦃ r s' => s'.Inv ∧ s3.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_0_eo__24smtx_5ftypeof_5fre_2e_5e
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s3
    rcases Store.boolean_value_native h_v4 with ⟨hx_5, hbv_5⟩ | ⟨hx_5, hbv_5⟩
    · ite_branch hbv_5
      step as ⟨e_v5, he_v5⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eRegLan.construct s3 e_v5 (by rw [he_v5]; exact empty_args) hinv3 h64 as ⟨v5, s4, hinv4, h_v5⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4
      ite_done hinv4 hG with (native_ite_true_rep _ hx_5 h_v5)
    · ite_branch hbv_5
      step as ⟨e_v6, he_v6⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s3 e_v6 (by rw [he_v6]; exact empty_args) hinv3 h64 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4
      ite_done hinv4 hG with (native_ite_false_rep _ hx_5 h_v6))
  store_step with h_ite_v7 as ⟨v7, s4, hinv4, h_v7⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4
  case_done hinv4 hG with h_v7 in EoCases.__smtx_typeof_re_exp.case_0 using

theorem case_1_eo__24smtx_5ftypeof_5fre_2e_5e_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_1_eo__24smtx_5ftypeof_5fre_2e_5e s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof_re_exp.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof_re_exp.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24smtx_5ftypeof_5fre_2e_5e
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  case_done hinv1 hG with h_v0 in EoCases.__smtx_typeof_re_exp.case_1 using

/-- logos's `__smtx_typeof_re_exp` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24smtx_5ftypeof_5fre_2e_5e.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __smtx_typeof_re_exp x_a0 x_a1 =
      (firstSome [EoCases.__smtx_typeof_re_exp.case_0 x_a0 x_a1, EoCases.__smtx_typeof_re_exp.case_1 x_a0 x_a1] default) := by
  conv => lhs; unfold __smtx_typeof_re_exp
  unfold EoCases.__smtx_typeof_re_exp.case_0 EoCases.__smtx_typeof_re_exp.case_1
  logos_eq

theorem body_eo__24smtx_5ftypeof_5fre_2e_5e_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24smtx_5ftypeof_5fre_2e_5e s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_typeof_re_exp x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24smtx_5ftypeof_5fre_2e_5e.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24smtx_5ftypeof_5fre_2e_5e
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24smtx_5ftypeof_5fre_2e_5e_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using
  case_step with case_1_eo__24smtx_5ftypeof_5fre_2e_5e_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 using hc0
  body_stuck hinv2 hG using hc0 hc1 in EoCases.__smtx_typeof_re_exp.case_0 EoCases.__smtx_typeof_re_exp.case_1 splitting x_a0 x_a1

theorem eo__24smtx_5ftypeof_5fre_2e_5e_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24smtx_5ftypeof_5fre_2e_5e.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24smtx_5ftypeof_5fre_2e_5e
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24smtx_5ftypeof_5fre_2e_5e s1 a0 a1) (fun s' t => Represents.rep s' t (__smtx_typeof_re_exp x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24smtx_5ftypeof_5fre_2e_5e_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24smtx_5ftypeof_5fre_2eloop_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    case_0_eo__24smtx_5ftypeof_5fre_2eloop s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof_re_loop.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof_re_loop.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24smtx_5ftypeof_5fre_2eloop
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2eNumeral.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__smtx_typeof_re_loop.case_0
  pat_destruct CtorSpec.eo__24emb_5fsm_2eNumeral.destruct h_a1 as ⟨v3, x_v3, h_v3⟩ else hinv hG in EoCases.__smtx_typeof_re_loop.case_0
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eRegLan.construct s e_v4 (by rw [he_v4]; exact empty_args) hinv h64 as ⟨v4, s1, hinv1, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3
  pat_same a2 v4 with h_a2 h_v4 using hinv1 else hinv1 hG in EoCases.__smtx_typeof_re_loop.case_0
  simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.raw_int_u32_spec s1 0#u32 (0) (by scalar_tac) hinv1 h64 as ⟨v5, s2, hinv2, h_v5⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4
  step as ⟨e_v6, he_v6⟩
  store_step with Store.native_spec_zleq s2 e_v6 (by rw [he_v6]; rfl) h_v5 h_v1 hinv2 h64 as ⟨v6, s3, hinv3, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v5
  rw [← Bridge.native_zleq] at h_v6
  have h_ite_v13 := (show if_1_eo__24smtx_5ftypeof_5fre_2eloop s3 v6 v3 ⦃ r s' => s'.Inv ∧ s3.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_1_eo__24smtx_5ftypeof_5fre_2eloop
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s3
    rcases Store.boolean_value_native h_v6 with ⟨hx_7, hbv_7⟩ | ⟨hx_7, hbv_7⟩
    · ite_branch hbv_7
      try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
      store_step with Store.raw_int_u32_spec s3 0#u32 (0) (by scalar_tac) hinv3 h64 as ⟨v7, s4, hinv4, h_v7⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v5 h_v6
      step as ⟨e_v8, he_v8⟩
      store_step with Store.native_spec_zleq s4 e_v8 (by rw [he_v8]; rfl) h_v7 h_v3 hinv4 h64 as ⟨v8, s5, hinv5, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v5 h_v6 h_v7
      rw [← Bridge.native_zleq] at h_v8
      have h_ite_v11 := (show if_0_eo__24smtx_5ftypeof_5fre_2eloop s5 v8 ⦃ r s' => s'.Inv ∧ s5.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_0_eo__24smtx_5ftypeof_5fre_2eloop
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s5
        rcases Store.boolean_value_native h_v8 with ⟨hx_9, hbv_9⟩ | ⟨hx_9, hbv_9⟩
        · ite_branch hbv_9
          step as ⟨e_v9, he_v9⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eRegLan.construct s5 e_v9 (by rw [he_v9]; exact empty_args) hinv5 h64 as ⟨v9, s6, hinv6, h_v9⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
          ite_done hinv6 hG with (native_ite_true_rep _ hx_9 h_v9)
        · ite_branch hbv_9
          step as ⟨e_v10, he_v10⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s5 e_v10 (by rw [he_v10]; exact empty_args) hinv5 h64 as ⟨v10, s6, hinv6, h_v10⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
          ite_done hinv6 hG with (native_ite_false_rep _ hx_9 h_v10))
      store_step with h_ite_v11 as ⟨v11, s6, hinv6, h_v11⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
      ite_done hinv6 hG with (native_ite_true_rep _ hx_7 h_v11)
    · ite_branch hbv_7
      step as ⟨e_v12, he_v12⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s3 e_v12 (by rw [he_v12]; exact empty_args) hinv3 h64 as ⟨v12, s4, hinv4, h_v12⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v5 h_v6
      ite_done hinv4 hG with (native_ite_false_rep _ hx_7 h_v12))
  store_step with h_ite_v13 as ⟨v13, s4, hinv4, h_v13⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v5 h_v6
  case_done hinv4 hG with h_v13 in EoCases.__smtx_typeof_re_loop.case_0 using

theorem case_1_eo__24smtx_5ftypeof_5fre_2eloop_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    case_1_eo__24smtx_5ftypeof_5fre_2eloop s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof_re_loop.case_1 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof_re_loop.case_1 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24smtx_5ftypeof_5fre_2eloop
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2
  case_done hinv1 hG with h_v0 in EoCases.__smtx_typeof_re_loop.case_1 using

/-- logos's `__smtx_typeof_re_loop` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24smtx_5ftypeof_5fre_2eloop.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __smtx_typeof_re_loop x_a0 x_a1 x_a2 =
      (firstSome [EoCases.__smtx_typeof_re_loop.case_0 x_a0 x_a1 x_a2, EoCases.__smtx_typeof_re_loop.case_1 x_a0 x_a1 x_a2] default) := by
  conv => lhs; unfold __smtx_typeof_re_loop
  unfold EoCases.__smtx_typeof_re_loop.case_0 EoCases.__smtx_typeof_re_loop.case_1
  logos_eq

theorem body_eo__24smtx_5ftypeof_5fre_2eloop_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24smtx_5ftypeof_5fre_2eloop s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_typeof_re_loop x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24smtx_5ftypeof_5fre_2eloop.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24smtx_5ftypeof_5fre_2eloop
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24smtx_5ftypeof_5fre_2eloop_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 using
  case_step with case_1_eo__24smtx_5ftypeof_5fre_2eloop_spec n ih s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 using hc0
  body_stuck hinv2 hG using hc0 hc1 in EoCases.__smtx_typeof_re_loop.case_0 EoCases.__smtx_typeof_re_loop.case_1 splitting x_a0 x_a1 x_a2

theorem eo__24smtx_5ftypeof_5fre_2eloop_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24smtx_5ftypeof_5fre_2eloop.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24smtx_5ftypeof_5fre_2eloop
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24smtx_5ftypeof_5fre_2eloop s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__smtx_typeof_re_loop x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24smtx_5ftypeof_5fre_2eloop_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24smtx_5ftypeof_5frotate_5fleft_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_0_eo__24smtx_5ftypeof_5frotate_5fleft s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof_rotate_left.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof_rotate_left.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24smtx_5ftypeof_5frotate_5fleft
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2eNumeral.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__smtx_typeof_rotate_left.case_0
  pat_destruct CtorSpec.eo__24emb_5ftsm_2eBitVec.destruct h_a1 as ⟨v3, x_v3, h_v3⟩ else hinv hG in EoCases.__smtx_typeof_rotate_left.case_0
  simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.raw_int_u32_spec s 0#u32 (0) (by scalar_tac) hinv h64 as ⟨v4, s1, hinv1, h_v4⟩ growing hG carrying h_a0 h_a1 h_v1 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with Store.native_spec_zleq s1 e_v5 (by rw [he_v5]; rfl) h_v4 h_v1 hinv1 h64 as ⟨v5, s2, hinv2, h_v5⟩ growing hG carrying h_a0 h_a1 h_v1 h_v3 h_v4
  rw [← Bridge.native_zleq] at h_v5
  have h_ite_v8 := (show if_0_eo__24smtx_5ftypeof_5frotate_5fleft s2 v5 v3 ⦃ r s' => s'.Inv ∧ s2.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_0_eo__24smtx_5ftypeof_5frotate_5fleft
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s2
    rcases Store.boolean_value_native h_v5 with ⟨hx_6, hbv_6⟩ | ⟨hx_6, hbv_6⟩
    · ite_branch hbv_6
      step as ⟨e_v6, he_v6⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eBitVec.construct s2 e_v6 (by rw [he_v6]; rfl) h_v3 hinv2 h64 as ⟨v6, s3, hinv3, h_v6⟩ growing hG carrying h_a0 h_a1 h_v1 h_v3 h_v4 h_v5
      ite_done hinv3 hG with (native_ite_true_rep _ hx_6 h_v6)
    · ite_branch hbv_6
      step as ⟨e_v7, he_v7⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s2 e_v7 (by rw [he_v7]; exact empty_args) hinv2 h64 as ⟨v7, s3, hinv3, h_v7⟩ growing hG carrying h_a0 h_a1 h_v1 h_v3 h_v4 h_v5
      ite_done hinv3 hG with (native_ite_false_rep _ hx_6 h_v7))
  store_step with h_ite_v8 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_a1 h_v1 h_v3 h_v4 h_v5
  case_done hinv3 hG with h_v8 in EoCases.__smtx_typeof_rotate_left.case_0 using

theorem case_1_eo__24smtx_5ftypeof_5frotate_5fleft_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_1_eo__24smtx_5ftypeof_5frotate_5fleft s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof_rotate_left.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof_rotate_left.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24smtx_5ftypeof_5frotate_5fleft
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  case_done hinv1 hG with h_v0 in EoCases.__smtx_typeof_rotate_left.case_1 using

/-- logos's `__smtx_typeof_rotate_left` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24smtx_5ftypeof_5frotate_5fleft.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __smtx_typeof_rotate_left x_a0 x_a1 =
      (firstSome [EoCases.__smtx_typeof_rotate_left.case_0 x_a0 x_a1, EoCases.__smtx_typeof_rotate_left.case_1 x_a0 x_a1] default) := by
  conv => lhs; unfold __smtx_typeof_rotate_left
  unfold EoCases.__smtx_typeof_rotate_left.case_0 EoCases.__smtx_typeof_rotate_left.case_1
  logos_eq

theorem body_eo__24smtx_5ftypeof_5frotate_5fleft_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24smtx_5ftypeof_5frotate_5fleft s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_typeof_rotate_left x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24smtx_5ftypeof_5frotate_5fleft.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24smtx_5ftypeof_5frotate_5fleft
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24smtx_5ftypeof_5frotate_5fleft_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using
  case_step with case_1_eo__24smtx_5ftypeof_5frotate_5fleft_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 using hc0
  body_stuck hinv2 hG using hc0 hc1 in EoCases.__smtx_typeof_rotate_left.case_0 EoCases.__smtx_typeof_rotate_left.case_1 splitting x_a0 x_a1

theorem eo__24smtx_5ftypeof_5frotate_5fleft_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24smtx_5ftypeof_5frotate_5fleft.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24smtx_5ftypeof_5frotate_5fleft
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24smtx_5ftypeof_5frotate_5fleft s1 a0 a1) (fun s' t => Represents.rep s' t (__smtx_typeof_rotate_left x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24smtx_5ftypeof_5frotate_5fleft_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24smtx_5ftypeof_5frotate_5fright_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_0_eo__24smtx_5ftypeof_5frotate_5fright s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof_rotate_right.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof_rotate_right.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24smtx_5ftypeof_5frotate_5fright
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2eNumeral.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__smtx_typeof_rotate_right.case_0
  pat_destruct CtorSpec.eo__24emb_5ftsm_2eBitVec.destruct h_a1 as ⟨v3, x_v3, h_v3⟩ else hinv hG in EoCases.__smtx_typeof_rotate_right.case_0
  simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.raw_int_u32_spec s 0#u32 (0) (by scalar_tac) hinv h64 as ⟨v4, s1, hinv1, h_v4⟩ growing hG carrying h_a0 h_a1 h_v1 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with Store.native_spec_zleq s1 e_v5 (by rw [he_v5]; rfl) h_v4 h_v1 hinv1 h64 as ⟨v5, s2, hinv2, h_v5⟩ growing hG carrying h_a0 h_a1 h_v1 h_v3 h_v4
  rw [← Bridge.native_zleq] at h_v5
  have h_ite_v8 := (show if_0_eo__24smtx_5ftypeof_5frotate_5fright s2 v5 v3 ⦃ r s' => s'.Inv ∧ s2.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_0_eo__24smtx_5ftypeof_5frotate_5fright
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s2
    rcases Store.boolean_value_native h_v5 with ⟨hx_6, hbv_6⟩ | ⟨hx_6, hbv_6⟩
    · ite_branch hbv_6
      step as ⟨e_v6, he_v6⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eBitVec.construct s2 e_v6 (by rw [he_v6]; rfl) h_v3 hinv2 h64 as ⟨v6, s3, hinv3, h_v6⟩ growing hG carrying h_a0 h_a1 h_v1 h_v3 h_v4 h_v5
      ite_done hinv3 hG with (native_ite_true_rep _ hx_6 h_v6)
    · ite_branch hbv_6
      step as ⟨e_v7, he_v7⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s2 e_v7 (by rw [he_v7]; exact empty_args) hinv2 h64 as ⟨v7, s3, hinv3, h_v7⟩ growing hG carrying h_a0 h_a1 h_v1 h_v3 h_v4 h_v5
      ite_done hinv3 hG with (native_ite_false_rep _ hx_6 h_v7))
  store_step with h_ite_v8 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_a1 h_v1 h_v3 h_v4 h_v5
  case_done hinv3 hG with h_v8 in EoCases.__smtx_typeof_rotate_right.case_0 using

theorem case_1_eo__24smtx_5ftypeof_5frotate_5fright_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_1_eo__24smtx_5ftypeof_5frotate_5fright s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof_rotate_right.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof_rotate_right.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24smtx_5ftypeof_5frotate_5fright
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  case_done hinv1 hG with h_v0 in EoCases.__smtx_typeof_rotate_right.case_1 using

/-- logos's `__smtx_typeof_rotate_right` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24smtx_5ftypeof_5frotate_5fright.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __smtx_typeof_rotate_right x_a0 x_a1 =
      (firstSome [EoCases.__smtx_typeof_rotate_right.case_0 x_a0 x_a1, EoCases.__smtx_typeof_rotate_right.case_1 x_a0 x_a1] default) := by
  conv => lhs; unfold __smtx_typeof_rotate_right
  unfold EoCases.__smtx_typeof_rotate_right.case_0 EoCases.__smtx_typeof_rotate_right.case_1
  logos_eq

theorem body_eo__24smtx_5ftypeof_5frotate_5fright_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24smtx_5ftypeof_5frotate_5fright s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_typeof_rotate_right x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24smtx_5ftypeof_5frotate_5fright.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24smtx_5ftypeof_5frotate_5fright
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24smtx_5ftypeof_5frotate_5fright_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using
  case_step with case_1_eo__24smtx_5ftypeof_5frotate_5fright_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 using hc0
  body_stuck hinv2 hG using hc0 hc1 in EoCases.__smtx_typeof_rotate_right.case_0 EoCases.__smtx_typeof_rotate_right.case_1 splitting x_a0 x_a1

theorem eo__24smtx_5ftypeof_5frotate_5fright_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24smtx_5ftypeof_5frotate_5fright.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24smtx_5ftypeof_5frotate_5fright
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24smtx_5ftypeof_5frotate_5fright s1 a0 a1) (fun s' t => Represents.rep s' t (__smtx_typeof_rotate_right x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24smtx_5ftypeof_5frotate_5fright_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24smtx_5ftypeof_5fselect_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_0_eo__24smtx_5ftypeof_5fselect s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof_select.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof_select.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24smtx_5ftypeof_5fselect
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5ftsm_2eMap.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof_select.case_0
  step as ⟨e_v3, he_v3⟩
  store_step with Store.native_spec_Teq s e_v3 (by rw [he_v3]; rfl) h_v1 h_a1 hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2
  have h_ite_v5 := (show if_0_eo__24smtx_5ftypeof_5fselect s1 v3 v2 ⦃ r s' => s'.Inv ∧ s1.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_0_eo__24smtx_5ftypeof_5fselect
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s1
    rcases Store.boolean_value_native h_v3 with ⟨hx_4, hbv_4⟩ | ⟨hx_4, hbv_4⟩
    · ite_branch hbv_4
      ite_done hinv1 hG with (native_ite_true_rep _ hx_4 h_v2)
    · ite_branch hbv_4
      step as ⟨e_v4, he_v4⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s1 e_v4 (by rw [he_v4]; exact empty_args) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3
      ite_done hinv2 hG with (native_ite_false_rep _ hx_4 h_v4))
  store_step with h_ite_v5 as ⟨v5, s2, hinv2, h_v5⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3
  case_done hinv2 hG with h_v5 in EoCases.__smtx_typeof_select.case_0 using

theorem case_1_eo__24smtx_5ftypeof_5fselect_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_1_eo__24smtx_5ftypeof_5fselect s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof_select.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof_select.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24smtx_5ftypeof_5fselect
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  case_done hinv1 hG with h_v0 in EoCases.__smtx_typeof_select.case_1 using

/-- logos's `__smtx_typeof_select` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24smtx_5ftypeof_5fselect.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __smtx_typeof_select x_a0 x_a1 =
      (firstSome [EoCases.__smtx_typeof_select.case_0 x_a0 x_a1, EoCases.__smtx_typeof_select.case_1 x_a0 x_a1] default) := by
  conv => lhs; unfold __smtx_typeof_select
  unfold EoCases.__smtx_typeof_select.case_0 EoCases.__smtx_typeof_select.case_1
  logos_eq

theorem body_eo__24smtx_5ftypeof_5fselect_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24smtx_5ftypeof_5fselect s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_typeof_select x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24smtx_5ftypeof_5fselect.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24smtx_5ftypeof_5fselect
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24smtx_5ftypeof_5fselect_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using
  case_step with case_1_eo__24smtx_5ftypeof_5fselect_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 using hc0
  body_stuck hinv2 hG using hc0 hc1 in EoCases.__smtx_typeof_select.case_0 EoCases.__smtx_typeof_select.case_1 splitting x_a0 x_a1

theorem eo__24smtx_5ftypeof_5fselect_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24smtx_5ftypeof_5fselect.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24smtx_5ftypeof_5fselect
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24smtx_5ftypeof_5fselect s1 a0 a1) (fun s' t => Represents.rep s' t (__smtx_typeof_select x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24smtx_5ftypeof_5fselect_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24smtx_5ftypeof_5fseq_2enth_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_0_eo__24smtx_5ftypeof_5fseq_2enth s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof_seq_nth.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof_seq_nth.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24smtx_5ftypeof_5fseq_2enth
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5ftsm_2eSeq.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__smtx_typeof_seq_nth.case_0
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eInt.construct s e_v2 (by rw [he_v2]; exact empty_args) hinv h64 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying h_a0 h_a1 h_v1
  pat_same a1 v2 with h_a1 h_v2 using hinv1 else hinv1 hG in EoCases.__smtx_typeof_seq_nth.case_0
  store_step with ih.eo__24smtx_5ftypeof_5fguard_5fwf s1 v1 v1 _ _ hinv1 h64 (hG.rem hrem) h_v1 h_v1 as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2
  case_done hinv2 hG with h_v3 in EoCases.__smtx_typeof_seq_nth.case_0 using

theorem case_1_eo__24smtx_5ftypeof_5fseq_2enth_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_1_eo__24smtx_5ftypeof_5fseq_2enth s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof_seq_nth.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof_seq_nth.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24smtx_5ftypeof_5fseq_2enth
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  case_done hinv1 hG with h_v0 in EoCases.__smtx_typeof_seq_nth.case_1 using

/-- logos's `__smtx_typeof_seq_nth` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24smtx_5ftypeof_5fseq_2enth.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __smtx_typeof_seq_nth x_a0 x_a1 =
      (firstSome [EoCases.__smtx_typeof_seq_nth.case_0 x_a0 x_a1, EoCases.__smtx_typeof_seq_nth.case_1 x_a0 x_a1] default) := by
  conv => lhs; unfold __smtx_typeof_seq_nth
  unfold EoCases.__smtx_typeof_seq_nth.case_0 EoCases.__smtx_typeof_seq_nth.case_1
  logos_eq

theorem body_eo__24smtx_5ftypeof_5fseq_2enth_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24smtx_5ftypeof_5fseq_2enth s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_typeof_seq_nth x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24smtx_5ftypeof_5fseq_2enth.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24smtx_5ftypeof_5fseq_2enth
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24smtx_5ftypeof_5fseq_2enth_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using
  case_step with case_1_eo__24smtx_5ftypeof_5fseq_2enth_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 using hc0
  body_stuck hinv2 hG using hc0 hc1 in EoCases.__smtx_typeof_seq_nth.case_0 EoCases.__smtx_typeof_seq_nth.case_1 splitting x_a0 x_a1

theorem eo__24smtx_5ftypeof_5fseq_2enth_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24smtx_5ftypeof_5fseq_2enth.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24smtx_5ftypeof_5fseq_2enth
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24smtx_5ftypeof_5fseq_2enth s1 a0 a1) (fun s' t => Represents.rep s' t (__smtx_typeof_seq_nth x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24smtx_5ftypeof_5fseq_2enth_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24smtx_5ftypeof_5fseq_5fdiff_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_0_eo__24smtx_5ftypeof_5fseq_5fdiff s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof_seq_diff.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof_seq_diff.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24smtx_5ftypeof_5fseq_5fdiff
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5ftsm_2eSeq.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__smtx_typeof_seq_diff.case_0
  pat_destruct CtorSpec.eo__24emb_5ftsm_2eSeq.destruct h_a1 as ⟨v3, x_v3, h_v3⟩ else hinv hG in EoCases.__smtx_typeof_seq_diff.case_0
  step as ⟨e_v4, he_v4⟩
  store_step with Store.native_spec_Teq s e_v4 (by rw [he_v4]; rfl) h_v1 h_v3 hinv h64 as ⟨v4, s1, hinv1, h_v4⟩ growing hG carrying h_a0 h_a1 h_v1 h_v3
  have h_ite_v7 := (show if_0_eo__24smtx_5ftypeof_5fseq_5fdiff s1 v4 ⦃ r s' => s'.Inv ∧ s1.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_0_eo__24smtx_5ftypeof_5fseq_5fdiff
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s1
    rcases Store.boolean_value_native h_v4 with ⟨hx_5, hbv_5⟩ | ⟨hx_5, hbv_5⟩
    · ite_branch hbv_5
      step as ⟨e_v5, he_v5⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eInt.construct s1 e_v5 (by rw [he_v5]; exact empty_args) hinv1 h64 as ⟨v5, s2, hinv2, h_v5⟩ growing hG carrying h_a0 h_a1 h_v1 h_v3 h_v4
      ite_done hinv2 hG with (native_ite_true_rep _ hx_5 h_v5)
    · ite_branch hbv_5
      step as ⟨e_v6, he_v6⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s1 e_v6 (by rw [he_v6]; exact empty_args) hinv1 h64 as ⟨v6, s2, hinv2, h_v6⟩ growing hG carrying h_a0 h_a1 h_v1 h_v3 h_v4
      ite_done hinv2 hG with (native_ite_false_rep _ hx_5 h_v6))
  store_step with h_ite_v7 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_a1 h_v1 h_v3 h_v4
  case_done hinv2 hG with h_v7 in EoCases.__smtx_typeof_seq_diff.case_0 using

theorem case_1_eo__24smtx_5ftypeof_5fseq_5fdiff_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_1_eo__24smtx_5ftypeof_5fseq_5fdiff s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof_seq_diff.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof_seq_diff.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24smtx_5ftypeof_5fseq_5fdiff
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  case_done hinv1 hG with h_v0 in EoCases.__smtx_typeof_seq_diff.case_1 using

/-- logos's `__smtx_typeof_seq_diff` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24smtx_5ftypeof_5fseq_5fdiff.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __smtx_typeof_seq_diff x_a0 x_a1 =
      (firstSome [EoCases.__smtx_typeof_seq_diff.case_0 x_a0 x_a1, EoCases.__smtx_typeof_seq_diff.case_1 x_a0 x_a1] default) := by
  conv => lhs; unfold __smtx_typeof_seq_diff
  unfold EoCases.__smtx_typeof_seq_diff.case_0 EoCases.__smtx_typeof_seq_diff.case_1
  logos_eq

theorem body_eo__24smtx_5ftypeof_5fseq_5fdiff_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24smtx_5ftypeof_5fseq_5fdiff s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_typeof_seq_diff x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24smtx_5ftypeof_5fseq_5fdiff.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24smtx_5ftypeof_5fseq_5fdiff
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24smtx_5ftypeof_5fseq_5fdiff_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using
  case_step with case_1_eo__24smtx_5ftypeof_5fseq_5fdiff_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 using hc0
  body_stuck hinv2 hG using hc0 hc1 in EoCases.__smtx_typeof_seq_diff.case_0 EoCases.__smtx_typeof_seq_diff.case_1 splitting x_a0 x_a1

theorem eo__24smtx_5ftypeof_5fseq_5fdiff_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24smtx_5ftypeof_5fseq_5fdiff.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24smtx_5ftypeof_5fseq_5fdiff
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24smtx_5ftypeof_5fseq_5fdiff s1 a0 a1) (fun s' t => Represents.rep s' t (__smtx_typeof_seq_diff x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24smtx_5ftypeof_5fseq_5fdiff_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24smtx_5ftypeof_5fseq_5fop_5f1_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24smtx_5ftypeof_5fseq_5fop_5f1 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof_seq_op_1.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof_seq_op_1.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24smtx_5ftypeof_5fseq_5fop_5f1
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5ftsm_2eSeq.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__smtx_typeof_seq_op_1.case_0
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eSeq.construct s e_v2 (by rw [he_v2]; rfl) h_v1 hinv h64 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying h_a0 h_v1
  case_done hinv1 hG with h_v2 in EoCases.__smtx_typeof_seq_op_1.case_0 using

theorem case_1_eo__24smtx_5ftypeof_5fseq_5fop_5f1_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_1_eo__24smtx_5ftypeof_5fseq_5fop_5f1 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof_seq_op_1.case_1 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof_seq_op_1.case_1 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24smtx_5ftypeof_5fseq_5fop_5f1
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  case_done hinv1 hG with h_v0 in EoCases.__smtx_typeof_seq_op_1.case_1 using

/-- logos's `__smtx_typeof_seq_op_1` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24smtx_5ftypeof_5fseq_5fop_5f1.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __smtx_typeof_seq_op_1 x_a0 =
      (firstSome [EoCases.__smtx_typeof_seq_op_1.case_0 x_a0, EoCases.__smtx_typeof_seq_op_1.case_1 x_a0] default) := by
  conv => lhs; unfold __smtx_typeof_seq_op_1
  unfold EoCases.__smtx_typeof_seq_op_1.case_0 EoCases.__smtx_typeof_seq_op_1.case_1
  logos_eq

theorem body_eo__24smtx_5ftypeof_5fseq_5fop_5f1_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24smtx_5ftypeof_5fseq_5fop_5f1 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_typeof_seq_op_1 x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24smtx_5ftypeof_5fseq_5fop_5f1.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24smtx_5ftypeof_5fseq_5fop_5f1
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24smtx_5ftypeof_5fseq_5fop_5f1_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using
  case_step with case_1_eo__24smtx_5ftypeof_5fseq_5fop_5f1_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 using hc0
  body_stuck hinv2 hG using hc0 hc1 in EoCases.__smtx_typeof_seq_op_1.case_0 EoCases.__smtx_typeof_seq_op_1.case_1 splitting x_a0

theorem eo__24smtx_5ftypeof_5fseq_5fop_5f1_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24smtx_5ftypeof_5fseq_5fop_5f1.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24smtx_5ftypeof_5fseq_5fop_5f1
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24smtx_5ftypeof_5fseq_5fop_5f1 s1 a0) (fun s' t => Represents.rep s' t (__smtx_typeof_seq_op_1 x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24smtx_5ftypeof_5fseq_5fop_5f1_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24smtx_5ftypeof_5fseq_5fop_5f1_5fret_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_0_eo__24smtx_5ftypeof_5fseq_5fop_5f1_5fret s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof_seq_op_1_ret.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof_seq_op_1_ret.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24smtx_5ftypeof_5fseq_5fop_5f1_5fret
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5ftsm_2eSeq.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__smtx_typeof_seq_op_1_ret.case_0
  case_done hinv hG with h_a1 in EoCases.__smtx_typeof_seq_op_1_ret.case_0 using

theorem case_1_eo__24smtx_5ftypeof_5fseq_5fop_5f1_5fret_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_1_eo__24smtx_5ftypeof_5fseq_5fop_5f1_5fret s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof_seq_op_1_ret.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof_seq_op_1_ret.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24smtx_5ftypeof_5fseq_5fop_5f1_5fret
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  case_done hinv1 hG with h_v0 in EoCases.__smtx_typeof_seq_op_1_ret.case_1 using

/-- logos's `__smtx_typeof_seq_op_1_ret` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24smtx_5ftypeof_5fseq_5fop_5f1_5fret.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __smtx_typeof_seq_op_1_ret x_a0 x_a1 =
      (firstSome [EoCases.__smtx_typeof_seq_op_1_ret.case_0 x_a0 x_a1, EoCases.__smtx_typeof_seq_op_1_ret.case_1 x_a0 x_a1] default) := by
  conv => lhs; unfold __smtx_typeof_seq_op_1_ret
  unfold EoCases.__smtx_typeof_seq_op_1_ret.case_0 EoCases.__smtx_typeof_seq_op_1_ret.case_1
  logos_eq

theorem body_eo__24smtx_5ftypeof_5fseq_5fop_5f1_5fret_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24smtx_5ftypeof_5fseq_5fop_5f1_5fret s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_typeof_seq_op_1_ret x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24smtx_5ftypeof_5fseq_5fop_5f1_5fret.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24smtx_5ftypeof_5fseq_5fop_5f1_5fret
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24smtx_5ftypeof_5fseq_5fop_5f1_5fret_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using
  case_step with case_1_eo__24smtx_5ftypeof_5fseq_5fop_5f1_5fret_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 using hc0
  body_stuck hinv2 hG using hc0 hc1 in EoCases.__smtx_typeof_seq_op_1_ret.case_0 EoCases.__smtx_typeof_seq_op_1_ret.case_1 splitting x_a0 x_a1

theorem eo__24smtx_5ftypeof_5fseq_5fop_5f1_5fret_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24smtx_5ftypeof_5fseq_5fop_5f1_5fret.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24smtx_5ftypeof_5fseq_5fop_5f1_5fret
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24smtx_5ftypeof_5fseq_5fop_5f1_5fret s1 a0 a1) (fun s' t => Represents.rep s' t (__smtx_typeof_seq_op_1_ret x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24smtx_5ftypeof_5fseq_5fop_5f1_5fret_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24smtx_5ftypeof_5fseq_5fop_5f2_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_0_eo__24smtx_5ftypeof_5fseq_5fop_5f2 s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof_seq_op_2.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof_seq_op_2.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24smtx_5ftypeof_5fseq_5fop_5f2
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5ftsm_2eSeq.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__smtx_typeof_seq_op_2.case_0
  pat_destruct CtorSpec.eo__24emb_5ftsm_2eSeq.destruct h_a1 as ⟨v3, x_v3, h_v3⟩ else hinv hG in EoCases.__smtx_typeof_seq_op_2.case_0
  step as ⟨e_v4, he_v4⟩
  store_step with Store.native_spec_Teq s e_v4 (by rw [he_v4]; rfl) h_v1 h_v3 hinv h64 as ⟨v4, s1, hinv1, h_v4⟩ growing hG carrying h_a0 h_a1 h_v1 h_v3
  have h_ite_v7 := (show if_0_eo__24smtx_5ftypeof_5fseq_5fop_5f2 s1 v4 v1 ⦃ r s' => s'.Inv ∧ s1.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_0_eo__24smtx_5ftypeof_5fseq_5fop_5f2
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s1
    rcases Store.boolean_value_native h_v4 with ⟨hx_5, hbv_5⟩ | ⟨hx_5, hbv_5⟩
    · ite_branch hbv_5
      step as ⟨e_v5, he_v5⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eSeq.construct s1 e_v5 (by rw [he_v5]; rfl) h_v1 hinv1 h64 as ⟨v5, s2, hinv2, h_v5⟩ growing hG carrying h_a0 h_a1 h_v1 h_v3 h_v4
      ite_done hinv2 hG with (native_ite_true_rep _ hx_5 h_v5)
    · ite_branch hbv_5
      step as ⟨e_v6, he_v6⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s1 e_v6 (by rw [he_v6]; exact empty_args) hinv1 h64 as ⟨v6, s2, hinv2, h_v6⟩ growing hG carrying h_a0 h_a1 h_v1 h_v3 h_v4
      ite_done hinv2 hG with (native_ite_false_rep _ hx_5 h_v6))
  store_step with h_ite_v7 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_a1 h_v1 h_v3 h_v4
  case_done hinv2 hG with h_v7 in EoCases.__smtx_typeof_seq_op_2.case_0 using

theorem case_1_eo__24smtx_5ftypeof_5fseq_5fop_5f2_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_1_eo__24smtx_5ftypeof_5fseq_5fop_5f2 s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof_seq_op_2.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof_seq_op_2.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24smtx_5ftypeof_5fseq_5fop_5f2
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  case_done hinv1 hG with h_v0 in EoCases.__smtx_typeof_seq_op_2.case_1 using

/-- logos's `__smtx_typeof_seq_op_2` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24smtx_5ftypeof_5fseq_5fop_5f2.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __smtx_typeof_seq_op_2 x_a0 x_a1 =
      (firstSome [EoCases.__smtx_typeof_seq_op_2.case_0 x_a0 x_a1, EoCases.__smtx_typeof_seq_op_2.case_1 x_a0 x_a1] default) := by
  conv => lhs; unfold __smtx_typeof_seq_op_2
  unfold EoCases.__smtx_typeof_seq_op_2.case_0 EoCases.__smtx_typeof_seq_op_2.case_1
  logos_eq

theorem body_eo__24smtx_5ftypeof_5fseq_5fop_5f2_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24smtx_5ftypeof_5fseq_5fop_5f2 s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_typeof_seq_op_2 x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24smtx_5ftypeof_5fseq_5fop_5f2.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24smtx_5ftypeof_5fseq_5fop_5f2
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24smtx_5ftypeof_5fseq_5fop_5f2_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using
  case_step with case_1_eo__24smtx_5ftypeof_5fseq_5fop_5f2_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 using hc0
  body_stuck hinv2 hG using hc0 hc1 in EoCases.__smtx_typeof_seq_op_2.case_0 EoCases.__smtx_typeof_seq_op_2.case_1 splitting x_a0 x_a1

theorem eo__24smtx_5ftypeof_5fseq_5fop_5f2_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24smtx_5ftypeof_5fseq_5fop_5f2.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24smtx_5ftypeof_5fseq_5fop_5f2
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24smtx_5ftypeof_5fseq_5fop_5f2 s1 a0 a1) (fun s' t => Represents.rep s' t (__smtx_typeof_seq_op_2 x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24smtx_5ftypeof_5fseq_5fop_5f2_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24smtx_5ftypeof_5fseq_5fop_5f2_5fret_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    case_0_eo__24smtx_5ftypeof_5fseq_5fop_5f2_5fret s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof_seq_op_2_ret.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof_seq_op_2_ret.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24smtx_5ftypeof_5fseq_5fop_5f2_5fret
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5ftsm_2eSeq.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__smtx_typeof_seq_op_2_ret.case_0
  pat_destruct CtorSpec.eo__24emb_5ftsm_2eSeq.destruct h_a1 as ⟨v3, x_v3, h_v3⟩ else hinv hG in EoCases.__smtx_typeof_seq_op_2_ret.case_0
  step as ⟨e_v4, he_v4⟩
  store_step with Store.native_spec_Teq s e_v4 (by rw [he_v4]; rfl) h_v1 h_v3 hinv h64 as ⟨v4, s1, hinv1, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3
  have h_ite_v6 := (show if_0_eo__24smtx_5ftypeof_5fseq_5fop_5f2_5fret s1 v4 a2 ⦃ r s' => s'.Inv ∧ s1.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_0_eo__24smtx_5ftypeof_5fseq_5fop_5f2_5fret
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s1
    rcases Store.boolean_value_native h_v4 with ⟨hx_5, hbv_5⟩ | ⟨hx_5, hbv_5⟩
    · ite_branch hbv_5
      ite_done hinv1 hG with (native_ite_true_rep _ hx_5 h_a2)
    · ite_branch hbv_5
      step as ⟨e_v5, he_v5⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s1 e_v5 (by rw [he_v5]; exact empty_args) hinv1 h64 as ⟨v5, s2, hinv2, h_v5⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4
      ite_done hinv2 hG with (native_ite_false_rep _ hx_5 h_v5))
  store_step with h_ite_v6 as ⟨v6, s2, hinv2, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4
  case_done hinv2 hG with h_v6 in EoCases.__smtx_typeof_seq_op_2_ret.case_0 using

theorem case_1_eo__24smtx_5ftypeof_5fseq_5fop_5f2_5fret_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    case_1_eo__24smtx_5ftypeof_5fseq_5fop_5f2_5fret s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof_seq_op_2_ret.case_1 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof_seq_op_2_ret.case_1 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24smtx_5ftypeof_5fseq_5fop_5f2_5fret
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2
  case_done hinv1 hG with h_v0 in EoCases.__smtx_typeof_seq_op_2_ret.case_1 using

/-- logos's `__smtx_typeof_seq_op_2_ret` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24smtx_5ftypeof_5fseq_5fop_5f2_5fret.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __smtx_typeof_seq_op_2_ret x_a0 x_a1 x_a2 =
      (firstSome [EoCases.__smtx_typeof_seq_op_2_ret.case_0 x_a0 x_a1 x_a2, EoCases.__smtx_typeof_seq_op_2_ret.case_1 x_a0 x_a1 x_a2] default) := by
  conv => lhs; unfold __smtx_typeof_seq_op_2_ret
  unfold EoCases.__smtx_typeof_seq_op_2_ret.case_0 EoCases.__smtx_typeof_seq_op_2_ret.case_1
  logos_eq

theorem body_eo__24smtx_5ftypeof_5fseq_5fop_5f2_5fret_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24smtx_5ftypeof_5fseq_5fop_5f2_5fret s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_typeof_seq_op_2_ret x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24smtx_5ftypeof_5fseq_5fop_5f2_5fret.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24smtx_5ftypeof_5fseq_5fop_5f2_5fret
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24smtx_5ftypeof_5fseq_5fop_5f2_5fret_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 using
  case_step with case_1_eo__24smtx_5ftypeof_5fseq_5fop_5f2_5fret_spec n ih s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 using hc0
  body_stuck hinv2 hG using hc0 hc1 in EoCases.__smtx_typeof_seq_op_2_ret.case_0 EoCases.__smtx_typeof_seq_op_2_ret.case_1 splitting x_a0 x_a1 x_a2

theorem eo__24smtx_5ftypeof_5fseq_5fop_5f2_5fret_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24smtx_5ftypeof_5fseq_5fop_5f2_5fret.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24smtx_5ftypeof_5fseq_5fop_5f2_5fret
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24smtx_5ftypeof_5fseq_5fop_5f2_5fret s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__smtx_typeof_seq_op_2_ret x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24smtx_5ftypeof_5fseq_5fop_5f2_5fret_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24smtx_5ftypeof_5fseq_5fop_5f3_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    case_0_eo__24smtx_5ftypeof_5fseq_5fop_5f3 s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof_seq_op_3.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof_seq_op_3.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24smtx_5ftypeof_5fseq_5fop_5f3
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5ftsm_2eSeq.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__smtx_typeof_seq_op_3.case_0
  pat_destruct CtorSpec.eo__24emb_5ftsm_2eSeq.destruct h_a1 as ⟨v3, x_v3, h_v3⟩ else hinv hG in EoCases.__smtx_typeof_seq_op_3.case_0
  pat_destruct CtorSpec.eo__24emb_5ftsm_2eSeq.destruct h_a2 as ⟨v5, x_v5, h_v5⟩ else hinv hG in EoCases.__smtx_typeof_seq_op_3.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with Store.native_spec_Teq s e_v6 (by rw [he_v6]; rfl) h_v1 h_v3 hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v5
  have h_ite_v12 := (show if_1_eo__24smtx_5ftypeof_5fseq_5fop_5f3 s1 v6 v3 v5 v1 ⦃ r s' => s'.Inv ∧ s1.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_1_eo__24smtx_5ftypeof_5fseq_5fop_5f3
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s1
    rcases Store.boolean_value_native h_v6 with ⟨hx_7, hbv_7⟩ | ⟨hx_7, hbv_7⟩
    · ite_branch hbv_7
      step as ⟨e_v7, he_v7⟩
      store_step with Store.native_spec_Teq s1 e_v7 (by rw [he_v7]; rfl) h_v3 h_v5 hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v5 h_v6
      have h_ite_v10 := (show if_0_eo__24smtx_5ftypeof_5fseq_5fop_5f3 s2 v7 v1 ⦃ r s' => s'.Inv ∧ s2.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_0_eo__24smtx_5ftypeof_5fseq_5fop_5f3
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s2
        rcases Store.boolean_value_native h_v7 with ⟨hx_8, hbv_8⟩ | ⟨hx_8, hbv_8⟩
        · ite_branch hbv_8
          step as ⟨e_v8, he_v8⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eSeq.construct s2 e_v8 (by rw [he_v8]; rfl) h_v1 hinv2 h64 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v5 h_v6 h_v7
          ite_done hinv3 hG with (native_ite_true_rep _ hx_8 h_v8)
        · ite_branch hbv_8
          step as ⟨e_v9, he_v9⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s2 e_v9 (by rw [he_v9]; exact empty_args) hinv2 h64 as ⟨v9, s3, hinv3, h_v9⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v5 h_v6 h_v7
          ite_done hinv3 hG with (native_ite_false_rep _ hx_8 h_v9))
      store_step with h_ite_v10 as ⟨v10, s3, hinv3, h_v10⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v5 h_v6 h_v7
      ite_done hinv3 hG with (native_ite_true_rep _ hx_7 h_v10)
    · ite_branch hbv_7
      step as ⟨e_v11, he_v11⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s1 e_v11 (by rw [he_v11]; exact empty_args) hinv1 h64 as ⟨v11, s2, hinv2, h_v11⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v5 h_v6
      ite_done hinv2 hG with (native_ite_false_rep _ hx_7 h_v11))
  store_step with h_ite_v12 as ⟨v12, s2, hinv2, h_v12⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v5 h_v6
  case_done hinv2 hG with h_v12 in EoCases.__smtx_typeof_seq_op_3.case_0 using

theorem case_1_eo__24smtx_5ftypeof_5fseq_5fop_5f3_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    case_1_eo__24smtx_5ftypeof_5fseq_5fop_5f3 s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof_seq_op_3.case_1 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof_seq_op_3.case_1 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24smtx_5ftypeof_5fseq_5fop_5f3
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2
  case_done hinv1 hG with h_v0 in EoCases.__smtx_typeof_seq_op_3.case_1 using

/-- logos's `__smtx_typeof_seq_op_3` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24smtx_5ftypeof_5fseq_5fop_5f3.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __smtx_typeof_seq_op_3 x_a0 x_a1 x_a2 =
      (firstSome [EoCases.__smtx_typeof_seq_op_3.case_0 x_a0 x_a1 x_a2, EoCases.__smtx_typeof_seq_op_3.case_1 x_a0 x_a1 x_a2] default) := by
  conv => lhs; unfold __smtx_typeof_seq_op_3
  unfold EoCases.__smtx_typeof_seq_op_3.case_0 EoCases.__smtx_typeof_seq_op_3.case_1
  logos_eq

theorem body_eo__24smtx_5ftypeof_5fseq_5fop_5f3_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24smtx_5ftypeof_5fseq_5fop_5f3 s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_typeof_seq_op_3 x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24smtx_5ftypeof_5fseq_5fop_5f3.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24smtx_5ftypeof_5fseq_5fop_5f3
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24smtx_5ftypeof_5fseq_5fop_5f3_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 using
  case_step with case_1_eo__24smtx_5ftypeof_5fseq_5fop_5f3_spec n ih s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 using hc0
  body_stuck hinv2 hG using hc0 hc1 in EoCases.__smtx_typeof_seq_op_3.case_0 EoCases.__smtx_typeof_seq_op_3.case_1 splitting x_a0 x_a1 x_a2

theorem eo__24smtx_5ftypeof_5fseq_5fop_5f3_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24smtx_5ftypeof_5fseq_5fop_5f3.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24smtx_5ftypeof_5fseq_5fop_5f3
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24smtx_5ftypeof_5fseq_5fop_5f3 s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__smtx_typeof_seq_op_3 x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24smtx_5ftypeof_5fseq_5fop_5f3_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24smtx_5ftypeof_5fset_2emember_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_0_eo__24smtx_5ftypeof_5fset_2emember s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof_set_member.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof_set_member.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24smtx_5ftypeof_5fset_2emember
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5ftsm_2eSet.destruct h_a1 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__smtx_typeof_set_member.case_0
  step as ⟨e_v2, he_v2⟩
  store_step with Store.native_spec_Teq s e_v2 (by rw [he_v2]; rfl) h_a0 h_v1 hinv h64 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying h_a0 h_a1 h_v1
  have h_ite_v5 := (show if_0_eo__24smtx_5ftypeof_5fset_2emember s1 v2 ⦃ r s' => s'.Inv ∧ s1.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_0_eo__24smtx_5ftypeof_5fset_2emember
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s1
    rcases Store.boolean_value_native h_v2 with ⟨hx_3, hbv_3⟩ | ⟨hx_3, hbv_3⟩
    · ite_branch hbv_3
      step as ⟨e_v3, he_v3⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s1 e_v3 (by rw [he_v3]; exact empty_args) hinv1 h64 as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2
      ite_done hinv2 hG with (native_ite_true_rep _ hx_3 h_v3)
    · ite_branch hbv_3
      step as ⟨e_v4, he_v4⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s1 e_v4 (by rw [he_v4]; exact empty_args) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2
      ite_done hinv2 hG with (native_ite_false_rep _ hx_3 h_v4))
  store_step with h_ite_v5 as ⟨v5, s2, hinv2, h_v5⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2
  case_done hinv2 hG with h_v5 in EoCases.__smtx_typeof_set_member.case_0 using

theorem case_1_eo__24smtx_5ftypeof_5fset_2emember_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_1_eo__24smtx_5ftypeof_5fset_2emember s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof_set_member.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof_set_member.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24smtx_5ftypeof_5fset_2emember
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  case_done hinv1 hG with h_v0 in EoCases.__smtx_typeof_set_member.case_1 using

/-- logos's `__smtx_typeof_set_member` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24smtx_5ftypeof_5fset_2emember.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __smtx_typeof_set_member x_a0 x_a1 =
      (firstSome [EoCases.__smtx_typeof_set_member.case_0 x_a0 x_a1, EoCases.__smtx_typeof_set_member.case_1 x_a0 x_a1] default) := by
  conv => lhs; unfold __smtx_typeof_set_member
  unfold EoCases.__smtx_typeof_set_member.case_0 EoCases.__smtx_typeof_set_member.case_1
  logos_eq

theorem body_eo__24smtx_5ftypeof_5fset_2emember_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24smtx_5ftypeof_5fset_2emember s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_typeof_set_member x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24smtx_5ftypeof_5fset_2emember.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24smtx_5ftypeof_5fset_2emember
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24smtx_5ftypeof_5fset_2emember_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using
  case_step with case_1_eo__24smtx_5ftypeof_5fset_2emember_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 using hc0
  body_stuck hinv2 hG using hc0 hc1 in EoCases.__smtx_typeof_set_member.case_0 EoCases.__smtx_typeof_set_member.case_1 splitting x_a0 x_a1

theorem eo__24smtx_5ftypeof_5fset_2emember_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24smtx_5ftypeof_5fset_2emember.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24smtx_5ftypeof_5fset_2emember
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24smtx_5ftypeof_5fset_2emember s1 a0 a1) (fun s' t => Represents.rep s' t (__smtx_typeof_set_member x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24smtx_5ftypeof_5fset_2emember_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24smtx_5ftypeof_5fsets_5fop_5f2_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_0_eo__24smtx_5ftypeof_5fsets_5fop_5f2 s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof_sets_op_2.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof_sets_op_2.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24smtx_5ftypeof_5fsets_5fop_5f2
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5ftsm_2eSet.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__smtx_typeof_sets_op_2.case_0
  pat_destruct CtorSpec.eo__24emb_5ftsm_2eSet.destruct h_a1 as ⟨v3, x_v3, h_v3⟩ else hinv hG in EoCases.__smtx_typeof_sets_op_2.case_0
  step as ⟨e_v4, he_v4⟩
  store_step with Store.native_spec_Teq s e_v4 (by rw [he_v4]; rfl) h_v1 h_v3 hinv h64 as ⟨v4, s1, hinv1, h_v4⟩ growing hG carrying h_a0 h_a1 h_v1 h_v3
  have h_ite_v7 := (show if_0_eo__24smtx_5ftypeof_5fsets_5fop_5f2 s1 v4 v1 ⦃ r s' => s'.Inv ∧ s1.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_0_eo__24smtx_5ftypeof_5fsets_5fop_5f2
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s1
    rcases Store.boolean_value_native h_v4 with ⟨hx_5, hbv_5⟩ | ⟨hx_5, hbv_5⟩
    · ite_branch hbv_5
      step as ⟨e_v5, he_v5⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eSet.construct s1 e_v5 (by rw [he_v5]; rfl) h_v1 hinv1 h64 as ⟨v5, s2, hinv2, h_v5⟩ growing hG carrying h_a0 h_a1 h_v1 h_v3 h_v4
      ite_done hinv2 hG with (native_ite_true_rep _ hx_5 h_v5)
    · ite_branch hbv_5
      step as ⟨e_v6, he_v6⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s1 e_v6 (by rw [he_v6]; exact empty_args) hinv1 h64 as ⟨v6, s2, hinv2, h_v6⟩ growing hG carrying h_a0 h_a1 h_v1 h_v3 h_v4
      ite_done hinv2 hG with (native_ite_false_rep _ hx_5 h_v6))
  store_step with h_ite_v7 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_a1 h_v1 h_v3 h_v4
  case_done hinv2 hG with h_v7 in EoCases.__smtx_typeof_sets_op_2.case_0 using

theorem case_1_eo__24smtx_5ftypeof_5fsets_5fop_5f2_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_1_eo__24smtx_5ftypeof_5fsets_5fop_5f2 s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof_sets_op_2.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof_sets_op_2.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24smtx_5ftypeof_5fsets_5fop_5f2
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  case_done hinv1 hG with h_v0 in EoCases.__smtx_typeof_sets_op_2.case_1 using

/-- logos's `__smtx_typeof_sets_op_2` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24smtx_5ftypeof_5fsets_5fop_5f2.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __smtx_typeof_sets_op_2 x_a0 x_a1 =
      (firstSome [EoCases.__smtx_typeof_sets_op_2.case_0 x_a0 x_a1, EoCases.__smtx_typeof_sets_op_2.case_1 x_a0 x_a1] default) := by
  conv => lhs; unfold __smtx_typeof_sets_op_2
  unfold EoCases.__smtx_typeof_sets_op_2.case_0 EoCases.__smtx_typeof_sets_op_2.case_1
  logos_eq

theorem body_eo__24smtx_5ftypeof_5fsets_5fop_5f2_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24smtx_5ftypeof_5fsets_5fop_5f2 s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_typeof_sets_op_2 x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24smtx_5ftypeof_5fsets_5fop_5f2.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24smtx_5ftypeof_5fsets_5fop_5f2
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24smtx_5ftypeof_5fsets_5fop_5f2_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using
  case_step with case_1_eo__24smtx_5ftypeof_5fsets_5fop_5f2_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 using hc0
  body_stuck hinv2 hG using hc0 hc1 in EoCases.__smtx_typeof_sets_op_2.case_0 EoCases.__smtx_typeof_sets_op_2.case_1 splitting x_a0 x_a1

theorem eo__24smtx_5ftypeof_5fsets_5fop_5f2_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24smtx_5ftypeof_5fsets_5fop_5f2.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24smtx_5ftypeof_5fsets_5fop_5f2
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24smtx_5ftypeof_5fsets_5fop_5f2 s1 a0 a1) (fun s' t => Represents.rep s' t (__smtx_typeof_sets_op_2 x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24smtx_5ftypeof_5fsets_5fop_5f2_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24smtx_5ftypeof_5fsets_5fop_5f2_5fret_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    case_0_eo__24smtx_5ftypeof_5fsets_5fop_5f2_5fret s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof_sets_op_2_ret.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof_sets_op_2_ret.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24smtx_5ftypeof_5fsets_5fop_5f2_5fret
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5ftsm_2eSet.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__smtx_typeof_sets_op_2_ret.case_0
  pat_destruct CtorSpec.eo__24emb_5ftsm_2eSet.destruct h_a1 as ⟨v3, x_v3, h_v3⟩ else hinv hG in EoCases.__smtx_typeof_sets_op_2_ret.case_0
  step as ⟨e_v4, he_v4⟩
  store_step with Store.native_spec_Teq s e_v4 (by rw [he_v4]; rfl) h_v1 h_v3 hinv h64 as ⟨v4, s1, hinv1, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3
  have h_ite_v6 := (show if_0_eo__24smtx_5ftypeof_5fsets_5fop_5f2_5fret s1 v4 a2 ⦃ r s' => s'.Inv ∧ s1.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_0_eo__24smtx_5ftypeof_5fsets_5fop_5f2_5fret
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s1
    rcases Store.boolean_value_native h_v4 with ⟨hx_5, hbv_5⟩ | ⟨hx_5, hbv_5⟩
    · ite_branch hbv_5
      ite_done hinv1 hG with (native_ite_true_rep _ hx_5 h_a2)
    · ite_branch hbv_5
      step as ⟨e_v5, he_v5⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s1 e_v5 (by rw [he_v5]; exact empty_args) hinv1 h64 as ⟨v5, s2, hinv2, h_v5⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4
      ite_done hinv2 hG with (native_ite_false_rep _ hx_5 h_v5))
  store_step with h_ite_v6 as ⟨v6, s2, hinv2, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4
  case_done hinv2 hG with h_v6 in EoCases.__smtx_typeof_sets_op_2_ret.case_0 using

theorem case_1_eo__24smtx_5ftypeof_5fsets_5fop_5f2_5fret_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    case_1_eo__24smtx_5ftypeof_5fsets_5fop_5f2_5fret s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof_sets_op_2_ret.case_1 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof_sets_op_2_ret.case_1 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24smtx_5ftypeof_5fsets_5fop_5f2_5fret
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2
  case_done hinv1 hG with h_v0 in EoCases.__smtx_typeof_sets_op_2_ret.case_1 using

/-- logos's `__smtx_typeof_sets_op_2_ret` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24smtx_5ftypeof_5fsets_5fop_5f2_5fret.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __smtx_typeof_sets_op_2_ret x_a0 x_a1 x_a2 =
      (firstSome [EoCases.__smtx_typeof_sets_op_2_ret.case_0 x_a0 x_a1 x_a2, EoCases.__smtx_typeof_sets_op_2_ret.case_1 x_a0 x_a1 x_a2] default) := by
  conv => lhs; unfold __smtx_typeof_sets_op_2_ret
  unfold EoCases.__smtx_typeof_sets_op_2_ret.case_0 EoCases.__smtx_typeof_sets_op_2_ret.case_1
  logos_eq

theorem body_eo__24smtx_5ftypeof_5fsets_5fop_5f2_5fret_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24smtx_5ftypeof_5fsets_5fop_5f2_5fret s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_typeof_sets_op_2_ret x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24smtx_5ftypeof_5fsets_5fop_5f2_5fret.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24smtx_5ftypeof_5fsets_5fop_5f2_5fret
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24smtx_5ftypeof_5fsets_5fop_5f2_5fret_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 using
  case_step with case_1_eo__24smtx_5ftypeof_5fsets_5fop_5f2_5fret_spec n ih s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 using hc0
  body_stuck hinv2 hG using hc0 hc1 in EoCases.__smtx_typeof_sets_op_2_ret.case_0 EoCases.__smtx_typeof_sets_op_2_ret.case_1 splitting x_a0 x_a1 x_a2

theorem eo__24smtx_5ftypeof_5fsets_5fop_5f2_5fret_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24smtx_5ftypeof_5fsets_5fop_5f2_5fret.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24smtx_5ftypeof_5fsets_5fop_5f2_5fret
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24smtx_5ftypeof_5fsets_5fop_5f2_5fret s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__smtx_typeof_sets_op_2_ret x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24smtx_5ftypeof_5fsets_5fop_5f2_5fret_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24smtx_5ftypeof_5fsign_5fextend_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_0_eo__24smtx_5ftypeof_5fsign_5fextend s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof_sign_extend.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof_sign_extend.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24smtx_5ftypeof_5fsign_5fextend
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2eNumeral.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__smtx_typeof_sign_extend.case_0
  pat_destruct CtorSpec.eo__24emb_5ftsm_2eBitVec.destruct h_a1 as ⟨v3, x_v3, h_v3⟩ else hinv hG in EoCases.__smtx_typeof_sign_extend.case_0
  simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.raw_int_u32_spec s 0#u32 (0) (by scalar_tac) hinv h64 as ⟨v4, s1, hinv1, h_v4⟩ growing hG carrying h_a0 h_a1 h_v1 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with Store.native_spec_zleq s1 e_v5 (by rw [he_v5]; rfl) h_v4 h_v1 hinv1 h64 as ⟨v5, s2, hinv2, h_v5⟩ growing hG carrying h_a0 h_a1 h_v1 h_v3 h_v4
  rw [← Bridge.native_zleq] at h_v5
  have h_ite_v11 := (show if_0_eo__24smtx_5ftypeof_5fsign_5fextend s2 v5 v3 v1 ⦃ r s' => s'.Inv ∧ s2.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_0_eo__24smtx_5ftypeof_5fsign_5fextend
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s2
    rcases Store.boolean_value_native h_v5 with ⟨hx_6, hbv_6⟩ | ⟨hx_6, hbv_6⟩
    · ite_branch hbv_6
      step as ⟨e_v6, he_v6⟩
      store_step with Store.native_spec_nat_to_int s2 e_v6 (by rw [he_v6]; rfl) h_v3 hinv2 h64 as ⟨v6, s3, hinv3, h_v6⟩ growing hG carrying h_a0 h_a1 h_v1 h_v3 h_v4 h_v5
      rw [← Bridge.native_nat_to_int] at h_v6
      step as ⟨e_v7, he_v7⟩
      store_step with Store.native_spec_zplus s3 e_v7 (by rw [he_v7]; rfl) h_v1 h_v6 hinv3 h64 as ⟨v7, s4, hinv4, h_v7⟩ growing hG carrying h_a0 h_a1 h_v1 h_v3 h_v4 h_v5 h_v6
      rw [← Bridge.native_zplus] at h_v7
      step as ⟨e_v8, he_v8⟩
      store_step with Store.native_spec_int_to_nat s4 e_v8 (by rw [he_v8]; rfl) h_v7 hinv4 h64 as ⟨v8, s5, hinv5, h_v8⟩ growing hG carrying h_a0 h_a1 h_v1 h_v3 h_v4 h_v5 h_v6 h_v7
      rw [← Bridge.native_int_to_nat] at h_v8
      step as ⟨e_v9, he_v9⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eBitVec.construct s5 e_v9 (by rw [he_v9]; rfl) h_v8 hinv5 h64 as ⟨v9, s6, hinv6, h_v9⟩ growing hG carrying h_a0 h_a1 h_v1 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
      ite_done hinv6 hG with (native_ite_true_rep _ hx_6 h_v9)
    · ite_branch hbv_6
      step as ⟨e_v10, he_v10⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s2 e_v10 (by rw [he_v10]; exact empty_args) hinv2 h64 as ⟨v10, s3, hinv3, h_v10⟩ growing hG carrying h_a0 h_a1 h_v1 h_v3 h_v4 h_v5
      ite_done hinv3 hG with (native_ite_false_rep _ hx_6 h_v10))
  store_step with h_ite_v11 as ⟨v11, s3, hinv3, h_v11⟩ growing hG carrying h_a0 h_a1 h_v1 h_v3 h_v4 h_v5
  case_done hinv3 hG with h_v11 in EoCases.__smtx_typeof_sign_extend.case_0 using

theorem case_1_eo__24smtx_5ftypeof_5fsign_5fextend_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_1_eo__24smtx_5ftypeof_5fsign_5fextend s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof_sign_extend.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof_sign_extend.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24smtx_5ftypeof_5fsign_5fextend
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  case_done hinv1 hG with h_v0 in EoCases.__smtx_typeof_sign_extend.case_1 using

/-- logos's `__smtx_typeof_sign_extend` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24smtx_5ftypeof_5fsign_5fextend.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __smtx_typeof_sign_extend x_a0 x_a1 =
      (firstSome [EoCases.__smtx_typeof_sign_extend.case_0 x_a0 x_a1, EoCases.__smtx_typeof_sign_extend.case_1 x_a0 x_a1] default) := by
  conv => lhs; unfold __smtx_typeof_sign_extend
  unfold EoCases.__smtx_typeof_sign_extend.case_0 EoCases.__smtx_typeof_sign_extend.case_1
  logos_eq

theorem body_eo__24smtx_5ftypeof_5fsign_5fextend_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24smtx_5ftypeof_5fsign_5fextend s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_typeof_sign_extend x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24smtx_5ftypeof_5fsign_5fextend.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24smtx_5ftypeof_5fsign_5fextend
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24smtx_5ftypeof_5fsign_5fextend_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using
  case_step with case_1_eo__24smtx_5ftypeof_5fsign_5fextend_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 using hc0
  body_stuck hinv2 hG using hc0 hc1 in EoCases.__smtx_typeof_sign_extend.case_0 EoCases.__smtx_typeof_sign_extend.case_1 splitting x_a0 x_a1

theorem eo__24smtx_5ftypeof_5fsign_5fextend_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24smtx_5ftypeof_5fsign_5fextend.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24smtx_5ftypeof_5fsign_5fextend
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24smtx_5ftypeof_5fsign_5fextend s1 a0 a1) (fun s' t => Represents.rep s' t (__smtx_typeof_sign_extend x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24smtx_5ftypeof_5fsign_5fextend_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24smtx_5ftypeof_5fstore_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    case_0_eo__24smtx_5ftypeof_5fstore s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof_store.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof_store.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24smtx_5ftypeof_5fstore
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5ftsm_2eMap.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof_store.case_0
  step as ⟨e_v3, he_v3⟩
  store_step with Store.native_spec_Teq s e_v3 (by rw [he_v3]; rfl) h_v1 h_a1 hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2
  have h_ite_v9 := (show if_1_eo__24smtx_5ftypeof_5fstore s1 v3 v2 a2 v1 ⦃ r s' => s'.Inv ∧ s1.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_1_eo__24smtx_5ftypeof_5fstore
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s1
    rcases Store.boolean_value_native h_v3 with ⟨hx_4, hbv_4⟩ | ⟨hx_4, hbv_4⟩
    · ite_branch hbv_4
      step as ⟨e_v4, he_v4⟩
      store_step with Store.native_spec_Teq s1 e_v4 (by rw [he_v4]; rfl) h_v2 h_a2 hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v3
      have h_ite_v7 := (show if_0_eo__24smtx_5ftypeof_5fstore s2 v4 v1 v2 ⦃ r s' => s'.Inv ∧ s2.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_0_eo__24smtx_5ftypeof_5fstore
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s2
        rcases Store.boolean_value_native h_v4 with ⟨hx_5, hbv_5⟩ | ⟨hx_5, hbv_5⟩
        · ite_branch hbv_5
          step as ⟨e_v5, he_v5⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eMap.construct s2 e_v5 (by rw [he_v5]; rfl) h_v1 h_v2 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v3 h_v4
          ite_done hinv3 hG with (native_ite_true_rep _ hx_5 h_v5)
        · ite_branch hbv_5
          step as ⟨e_v6, he_v6⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s2 e_v6 (by rw [he_v6]; exact empty_args) hinv2 h64 as ⟨v6, s3, hinv3, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v3 h_v4
          ite_done hinv3 hG with (native_ite_false_rep _ hx_5 h_v6))
      store_step with h_ite_v7 as ⟨v7, s3, hinv3, h_v7⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v3 h_v4
      ite_done hinv3 hG with (native_ite_true_rep _ hx_4 h_v7)
    · ite_branch hbv_4
      step as ⟨e_v8, he_v8⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s1 e_v8 (by rw [he_v8]; exact empty_args) hinv1 h64 as ⟨v8, s2, hinv2, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v3
      ite_done hinv2 hG with (native_ite_false_rep _ hx_4 h_v8))
  store_step with h_ite_v9 as ⟨v9, s2, hinv2, h_v9⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v3
  case_done hinv2 hG with h_v9 in EoCases.__smtx_typeof_store.case_0 using

theorem case_1_eo__24smtx_5ftypeof_5fstore_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    case_1_eo__24smtx_5ftypeof_5fstore s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof_store.case_1 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof_store.case_1 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24smtx_5ftypeof_5fstore
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2
  case_done hinv1 hG with h_v0 in EoCases.__smtx_typeof_store.case_1 using

/-- logos's `__smtx_typeof_store` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24smtx_5ftypeof_5fstore.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __smtx_typeof_store x_a0 x_a1 x_a2 =
      (firstSome [EoCases.__smtx_typeof_store.case_0 x_a0 x_a1 x_a2, EoCases.__smtx_typeof_store.case_1 x_a0 x_a1 x_a2] default) := by
  conv => lhs; unfold __smtx_typeof_store
  unfold EoCases.__smtx_typeof_store.case_0 EoCases.__smtx_typeof_store.case_1
  logos_eq

theorem body_eo__24smtx_5ftypeof_5fstore_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24smtx_5ftypeof_5fstore s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_typeof_store x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24smtx_5ftypeof_5fstore.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24smtx_5ftypeof_5fstore
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24smtx_5ftypeof_5fstore_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 using
  case_step with case_1_eo__24smtx_5ftypeof_5fstore_spec n ih s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 using hc0
  body_stuck hinv2 hG using hc0 hc1 in EoCases.__smtx_typeof_store.case_0 EoCases.__smtx_typeof_store.case_1 splitting x_a0 x_a1 x_a2

theorem eo__24smtx_5ftypeof_5fstore_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24smtx_5ftypeof_5fstore.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24smtx_5ftypeof_5fstore
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24smtx_5ftypeof_5fstore s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__smtx_typeof_store x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24smtx_5ftypeof_5fstore_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24smtx_5ftypeof_5fstr_2eat_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_0_eo__24smtx_5ftypeof_5fstr_2eat s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof_str_at.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof_str_at.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24smtx_5ftypeof_5fstr_2eat
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5ftsm_2eSeq.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__smtx_typeof_str_at.case_0
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eInt.construct s e_v2 (by rw [he_v2]; exact empty_args) hinv h64 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying h_a0 h_a1 h_v1
  pat_same a1 v2 with h_a1 h_v2 using hinv1 else hinv1 hG in EoCases.__smtx_typeof_str_at.case_0
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eSeq.construct s1 e_v3 (by rw [he_v3]; rfl) h_v1 hinv1 h64 as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2
  case_done hinv2 hG with h_v3 in EoCases.__smtx_typeof_str_at.case_0 using

theorem case_1_eo__24smtx_5ftypeof_5fstr_2eat_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_1_eo__24smtx_5ftypeof_5fstr_2eat s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof_str_at.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof_str_at.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24smtx_5ftypeof_5fstr_2eat
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  case_done hinv1 hG with h_v0 in EoCases.__smtx_typeof_str_at.case_1 using

/-- logos's `__smtx_typeof_str_at` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24smtx_5ftypeof_5fstr_2eat.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __smtx_typeof_str_at x_a0 x_a1 =
      (firstSome [EoCases.__smtx_typeof_str_at.case_0 x_a0 x_a1, EoCases.__smtx_typeof_str_at.case_1 x_a0 x_a1] default) := by
  conv => lhs; unfold __smtx_typeof_str_at
  unfold EoCases.__smtx_typeof_str_at.case_0 EoCases.__smtx_typeof_str_at.case_1
  logos_eq

theorem body_eo__24smtx_5ftypeof_5fstr_2eat_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24smtx_5ftypeof_5fstr_2eat s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_typeof_str_at x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24smtx_5ftypeof_5fstr_2eat.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24smtx_5ftypeof_5fstr_2eat
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24smtx_5ftypeof_5fstr_2eat_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using
  case_step with case_1_eo__24smtx_5ftypeof_5fstr_2eat_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 using hc0
  body_stuck hinv2 hG using hc0 hc1 in EoCases.__smtx_typeof_str_at.case_0 EoCases.__smtx_typeof_str_at.case_1 splitting x_a0 x_a1

theorem eo__24smtx_5ftypeof_5fstr_2eat_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24smtx_5ftypeof_5fstr_2eat.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24smtx_5ftypeof_5fstr_2eat
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24smtx_5ftypeof_5fstr_2eat s1 a0 a1) (fun s' t => Represents.rep s' t (__smtx_typeof_str_at x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24smtx_5ftypeof_5fstr_2eat_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24smtx_5ftypeof_5fstr_2eindexof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    case_0_eo__24smtx_5ftypeof_5fstr_2eindexof s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof_str_indexof.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof_str_indexof.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24smtx_5ftypeof_5fstr_2eindexof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5ftsm_2eSeq.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__smtx_typeof_str_indexof.case_0
  pat_destruct CtorSpec.eo__24emb_5ftsm_2eSeq.destruct h_a1 as ⟨v3, x_v3, h_v3⟩ else hinv hG in EoCases.__smtx_typeof_str_indexof.case_0
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eInt.construct s e_v4 (by rw [he_v4]; exact empty_args) hinv h64 as ⟨v4, s1, hinv1, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3
  pat_same a2 v4 with h_a2 h_v4 using hinv1 else hinv1 hG in EoCases.__smtx_typeof_str_indexof.case_0
  step as ⟨e_v5, he_v5⟩
  store_step with Store.native_spec_Teq s1 e_v5 (by rw [he_v5]; rfl) h_v1 h_v3 hinv1 h64 as ⟨v5, s2, hinv2, h_v5⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4
  have h_ite_v8 := (show if_0_eo__24smtx_5ftypeof_5fstr_2eindexof s2 v5 ⦃ r s' => s'.Inv ∧ s2.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_0_eo__24smtx_5ftypeof_5fstr_2eindexof
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s2
    rcases Store.boolean_value_native h_v5 with ⟨hx_6, hbv_6⟩ | ⟨hx_6, hbv_6⟩
    · ite_branch hbv_6
      step as ⟨e_v6, he_v6⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eInt.construct s2 e_v6 (by rw [he_v6]; exact empty_args) hinv2 h64 as ⟨v6, s3, hinv3, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v5
      ite_done hinv3 hG with (native_ite_true_rep _ hx_6 h_v6)
    · ite_branch hbv_6
      step as ⟨e_v7, he_v7⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s2 e_v7 (by rw [he_v7]; exact empty_args) hinv2 h64 as ⟨v7, s3, hinv3, h_v7⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v5
      ite_done hinv3 hG with (native_ite_false_rep _ hx_6 h_v7))
  store_step with h_ite_v8 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v5
  case_done hinv3 hG with h_v8 in EoCases.__smtx_typeof_str_indexof.case_0 using

theorem case_1_eo__24smtx_5ftypeof_5fstr_2eindexof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    case_1_eo__24smtx_5ftypeof_5fstr_2eindexof s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof_str_indexof.case_1 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof_str_indexof.case_1 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24smtx_5ftypeof_5fstr_2eindexof
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2
  case_done hinv1 hG with h_v0 in EoCases.__smtx_typeof_str_indexof.case_1 using

/-- logos's `__smtx_typeof_str_indexof` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24smtx_5ftypeof_5fstr_2eindexof.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __smtx_typeof_str_indexof x_a0 x_a1 x_a2 =
      (firstSome [EoCases.__smtx_typeof_str_indexof.case_0 x_a0 x_a1 x_a2, EoCases.__smtx_typeof_str_indexof.case_1 x_a0 x_a1 x_a2] default) := by
  conv => lhs; unfold __smtx_typeof_str_indexof
  unfold EoCases.__smtx_typeof_str_indexof.case_0 EoCases.__smtx_typeof_str_indexof.case_1
  logos_eq

theorem body_eo__24smtx_5ftypeof_5fstr_2eindexof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24smtx_5ftypeof_5fstr_2eindexof s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_typeof_str_indexof x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24smtx_5ftypeof_5fstr_2eindexof.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24smtx_5ftypeof_5fstr_2eindexof
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24smtx_5ftypeof_5fstr_2eindexof_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 using
  case_step with case_1_eo__24smtx_5ftypeof_5fstr_2eindexof_spec n ih s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 using hc0
  body_stuck hinv2 hG using hc0 hc1 in EoCases.__smtx_typeof_str_indexof.case_0 EoCases.__smtx_typeof_str_indexof.case_1 splitting x_a0 x_a1 x_a2

theorem eo__24smtx_5ftypeof_5fstr_2eindexof_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24smtx_5ftypeof_5fstr_2eindexof.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24smtx_5ftypeof_5fstr_2eindexof
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24smtx_5ftypeof_5fstr_2eindexof s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__smtx_typeof_str_indexof x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24smtx_5ftypeof_5fstr_2eindexof_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24smtx_5ftypeof_5fstr_2esubstr_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    case_0_eo__24smtx_5ftypeof_5fstr_2esubstr s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof_str_substr.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof_str_substr.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24smtx_5ftypeof_5fstr_2esubstr
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5ftsm_2eSeq.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__smtx_typeof_str_substr.case_0
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eInt.construct s e_v2 (by rw [he_v2]; exact empty_args) hinv h64 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1
  pat_same a1 v2 with h_a1 h_v2 using hinv1 else hinv1 hG in EoCases.__smtx_typeof_str_substr.case_0
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eInt.construct s1 e_v3 (by rw [he_v3]; exact empty_args) hinv1 h64 as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2
  pat_same a2 v3 with h_a2 h_v3 using hinv2 else hinv2 hG in EoCases.__smtx_typeof_str_substr.case_0
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eSeq.construct s2 e_v4 (by rw [he_v4]; rfl) h_v1 hinv2 h64 as ⟨v4, s3, hinv3, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v3
  case_done hinv3 hG with h_v4 in EoCases.__smtx_typeof_str_substr.case_0 using

theorem case_1_eo__24smtx_5ftypeof_5fstr_2esubstr_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    case_1_eo__24smtx_5ftypeof_5fstr_2esubstr s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof_str_substr.case_1 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof_str_substr.case_1 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24smtx_5ftypeof_5fstr_2esubstr
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2
  case_done hinv1 hG with h_v0 in EoCases.__smtx_typeof_str_substr.case_1 using

/-- logos's `__smtx_typeof_str_substr` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24smtx_5ftypeof_5fstr_2esubstr.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __smtx_typeof_str_substr x_a0 x_a1 x_a2 =
      (firstSome [EoCases.__smtx_typeof_str_substr.case_0 x_a0 x_a1 x_a2, EoCases.__smtx_typeof_str_substr.case_1 x_a0 x_a1 x_a2] default) := by
  conv => lhs; unfold __smtx_typeof_str_substr
  unfold EoCases.__smtx_typeof_str_substr.case_0 EoCases.__smtx_typeof_str_substr.case_1
  logos_eq

theorem body_eo__24smtx_5ftypeof_5fstr_2esubstr_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24smtx_5ftypeof_5fstr_2esubstr s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_typeof_str_substr x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24smtx_5ftypeof_5fstr_2esubstr.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24smtx_5ftypeof_5fstr_2esubstr
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24smtx_5ftypeof_5fstr_2esubstr_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 using
  case_step with case_1_eo__24smtx_5ftypeof_5fstr_2esubstr_spec n ih s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 using hc0
  body_stuck hinv2 hG using hc0 hc1 in EoCases.__smtx_typeof_str_substr.case_0 EoCases.__smtx_typeof_str_substr.case_1 splitting x_a0 x_a1 x_a2

theorem eo__24smtx_5ftypeof_5fstr_2esubstr_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24smtx_5ftypeof_5fstr_2esubstr.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24smtx_5ftypeof_5fstr_2esubstr
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24smtx_5ftypeof_5fstr_2esubstr s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__smtx_typeof_str_substr x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24smtx_5ftypeof_5fstr_2esubstr_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24smtx_5ftypeof_5fstr_2eupdate_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    case_0_eo__24smtx_5ftypeof_5fstr_2eupdate s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof_str_update.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof_str_update.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24smtx_5ftypeof_5fstr_2eupdate
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5ftsm_2eSeq.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__smtx_typeof_str_update.case_0
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eInt.construct s e_v2 (by rw [he_v2]; exact empty_args) hinv h64 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1
  pat_same a1 v2 with h_a1 h_v2 using hinv1 else hinv1 hG in EoCases.__smtx_typeof_str_update.case_0
  pat_destruct CtorSpec.eo__24emb_5ftsm_2eSeq.destruct h_a2 as ⟨v4, x_v4, h_v4⟩ else hinv1 hG in EoCases.__smtx_typeof_str_update.case_0
  step as ⟨e_v5, he_v5⟩
  store_step with Store.native_spec_Teq s1 e_v5 (by rw [he_v5]; rfl) h_v1 h_v4 hinv1 h64 as ⟨v5, s2, hinv2, h_v5⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4
  have h_ite_v8 := (show if_0_eo__24smtx_5ftypeof_5fstr_2eupdate s2 v5 v1 ⦃ r s' => s'.Inv ∧ s2.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_0_eo__24smtx_5ftypeof_5fstr_2eupdate
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s2
    rcases Store.boolean_value_native h_v5 with ⟨hx_6, hbv_6⟩ | ⟨hx_6, hbv_6⟩
    · ite_branch hbv_6
      step as ⟨e_v6, he_v6⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eSeq.construct s2 e_v6 (by rw [he_v6]; rfl) h_v1 hinv2 h64 as ⟨v6, s3, hinv3, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5
      ite_done hinv3 hG with (native_ite_true_rep _ hx_6 h_v6)
    · ite_branch hbv_6
      step as ⟨e_v7, he_v7⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s2 e_v7 (by rw [he_v7]; exact empty_args) hinv2 h64 as ⟨v7, s3, hinv3, h_v7⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5
      ite_done hinv3 hG with (native_ite_false_rep _ hx_6 h_v7))
  store_step with h_ite_v8 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5
  case_done hinv3 hG with h_v8 in EoCases.__smtx_typeof_str_update.case_0 using

theorem case_1_eo__24smtx_5ftypeof_5fstr_2eupdate_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    case_1_eo__24smtx_5ftypeof_5fstr_2eupdate s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof_str_update.case_1 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof_str_update.case_1 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24smtx_5ftypeof_5fstr_2eupdate
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2
  case_done hinv1 hG with h_v0 in EoCases.__smtx_typeof_str_update.case_1 using

/-- logos's `__smtx_typeof_str_update` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24smtx_5ftypeof_5fstr_2eupdate.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __smtx_typeof_str_update x_a0 x_a1 x_a2 =
      (firstSome [EoCases.__smtx_typeof_str_update.case_0 x_a0 x_a1 x_a2, EoCases.__smtx_typeof_str_update.case_1 x_a0 x_a1 x_a2] default) := by
  conv => lhs; unfold __smtx_typeof_str_update
  unfold EoCases.__smtx_typeof_str_update.case_0 EoCases.__smtx_typeof_str_update.case_1
  logos_eq

theorem body_eo__24smtx_5ftypeof_5fstr_2eupdate_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24smtx_5ftypeof_5fstr_2eupdate s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_typeof_str_update x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24smtx_5ftypeof_5fstr_2eupdate.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24smtx_5ftypeof_5fstr_2eupdate
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24smtx_5ftypeof_5fstr_2eupdate_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 using
  case_step with case_1_eo__24smtx_5ftypeof_5fstr_2eupdate_spec n ih s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 using hc0
  body_stuck hinv2 hG using hc0 hc1 in EoCases.__smtx_typeof_str_update.case_0 EoCases.__smtx_typeof_str_update.case_1 splitting x_a0 x_a1 x_a2

theorem eo__24smtx_5ftypeof_5fstr_2eupdate_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24smtx_5ftypeof_5fstr_2eupdate.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24smtx_5ftypeof_5fstr_2eupdate
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24smtx_5ftypeof_5fstr_2eupdate s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__smtx_typeof_str_update x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24smtx_5ftypeof_5fstr_2eupdate_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24smtx_5ftypeof_5fzero_5fextend_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_0_eo__24smtx_5ftypeof_5fzero_5fextend s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof_zero_extend.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof_zero_extend.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24smtx_5ftypeof_5fzero_5fextend
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2eNumeral.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__smtx_typeof_zero_extend.case_0
  pat_destruct CtorSpec.eo__24emb_5ftsm_2eBitVec.destruct h_a1 as ⟨v3, x_v3, h_v3⟩ else hinv hG in EoCases.__smtx_typeof_zero_extend.case_0
  simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.raw_int_u32_spec s 0#u32 (0) (by scalar_tac) hinv h64 as ⟨v4, s1, hinv1, h_v4⟩ growing hG carrying h_a0 h_a1 h_v1 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with Store.native_spec_zleq s1 e_v5 (by rw [he_v5]; rfl) h_v4 h_v1 hinv1 h64 as ⟨v5, s2, hinv2, h_v5⟩ growing hG carrying h_a0 h_a1 h_v1 h_v3 h_v4
  rw [← Bridge.native_zleq] at h_v5
  have h_ite_v11 := (show if_0_eo__24smtx_5ftypeof_5fzero_5fextend s2 v5 v3 v1 ⦃ r s' => s'.Inv ∧ s2.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_0_eo__24smtx_5ftypeof_5fzero_5fextend
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s2
    rcases Store.boolean_value_native h_v5 with ⟨hx_6, hbv_6⟩ | ⟨hx_6, hbv_6⟩
    · ite_branch hbv_6
      step as ⟨e_v6, he_v6⟩
      store_step with Store.native_spec_nat_to_int s2 e_v6 (by rw [he_v6]; rfl) h_v3 hinv2 h64 as ⟨v6, s3, hinv3, h_v6⟩ growing hG carrying h_a0 h_a1 h_v1 h_v3 h_v4 h_v5
      rw [← Bridge.native_nat_to_int] at h_v6
      step as ⟨e_v7, he_v7⟩
      store_step with Store.native_spec_zplus s3 e_v7 (by rw [he_v7]; rfl) h_v1 h_v6 hinv3 h64 as ⟨v7, s4, hinv4, h_v7⟩ growing hG carrying h_a0 h_a1 h_v1 h_v3 h_v4 h_v5 h_v6
      rw [← Bridge.native_zplus] at h_v7
      step as ⟨e_v8, he_v8⟩
      store_step with Store.native_spec_int_to_nat s4 e_v8 (by rw [he_v8]; rfl) h_v7 hinv4 h64 as ⟨v8, s5, hinv5, h_v8⟩ growing hG carrying h_a0 h_a1 h_v1 h_v3 h_v4 h_v5 h_v6 h_v7
      rw [← Bridge.native_int_to_nat] at h_v8
      step as ⟨e_v9, he_v9⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eBitVec.construct s5 e_v9 (by rw [he_v9]; rfl) h_v8 hinv5 h64 as ⟨v9, s6, hinv6, h_v9⟩ growing hG carrying h_a0 h_a1 h_v1 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
      ite_done hinv6 hG with (native_ite_true_rep _ hx_6 h_v9)
    · ite_branch hbv_6
      step as ⟨e_v10, he_v10⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s2 e_v10 (by rw [he_v10]; exact empty_args) hinv2 h64 as ⟨v10, s3, hinv3, h_v10⟩ growing hG carrying h_a0 h_a1 h_v1 h_v3 h_v4 h_v5
      ite_done hinv3 hG with (native_ite_false_rep _ hx_6 h_v10))
  store_step with h_ite_v11 as ⟨v11, s3, hinv3, h_v11⟩ growing hG carrying h_a0 h_a1 h_v1 h_v3 h_v4 h_v5
  case_done hinv3 hG with h_v11 in EoCases.__smtx_typeof_zero_extend.case_0 using

theorem case_1_eo__24smtx_5ftypeof_5fzero_5fextend_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_1_eo__24smtx_5ftypeof_5fzero_5fextend s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof_zero_extend.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof_zero_extend.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24smtx_5ftypeof_5fzero_5fextend
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  case_done hinv1 hG with h_v0 in EoCases.__smtx_typeof_zero_extend.case_1 using

/-- logos's `__smtx_typeof_zero_extend` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24smtx_5ftypeof_5fzero_5fextend.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __smtx_typeof_zero_extend x_a0 x_a1 =
      (firstSome [EoCases.__smtx_typeof_zero_extend.case_0 x_a0 x_a1, EoCases.__smtx_typeof_zero_extend.case_1 x_a0 x_a1] default) := by
  conv => lhs; unfold __smtx_typeof_zero_extend
  unfold EoCases.__smtx_typeof_zero_extend.case_0 EoCases.__smtx_typeof_zero_extend.case_1
  logos_eq

theorem body_eo__24smtx_5ftypeof_5fzero_5fextend_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24smtx_5ftypeof_5fzero_5fextend s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_typeof_zero_extend x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24smtx_5ftypeof_5fzero_5fextend.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24smtx_5ftypeof_5fzero_5fextend
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24smtx_5ftypeof_5fzero_5fextend_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using
  case_step with case_1_eo__24smtx_5ftypeof_5fzero_5fextend_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 using hc0
  body_stuck hinv2 hG using hc0 hc1 in EoCases.__smtx_typeof_zero_extend.case_0 EoCases.__smtx_typeof_zero_extend.case_1 splitting x_a0 x_a1

theorem eo__24smtx_5ftypeof_5fzero_5fextend_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24smtx_5ftypeof_5fzero_5fextend.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24smtx_5ftypeof_5fzero_5fextend
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24smtx_5ftypeof_5fzero_5fextend s1 a0 a1) (fun s' t => Represents.rep s' t (__smtx_typeof_zero_extend x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24smtx_5ftypeof_5fzero_5fextend_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24str_5farith_5fentail_5fis_5fapprox_5flen_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24str_5farith_5fentail_5fis_5fapprox_5flen s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__str_arith_entail_is_approx_len.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__str_arith_entail_is_approx_len.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24str_5farith_5fentail_5fis_5fapprox_5flen
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__str_arith_entail_is_approx_len.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__str_arith_entail_is_approx_len.case_0
  pat_unapply h_v4 as ⟨v7, v8, x_v7, x_v8, h_v7, h_v8, hn_v7, hn_v8⟩ using hinv else hinv hG in EoCases.__str_arith_entail_is_approx_len.case_0
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s e_v9 (by rw [he_v9]; exact empty_args) hinv h64 as ⟨v9, s1, hinv1, h_v9⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8
  pat_same v7 v9 with h_v7 h_v9 using hinv1 else hinv1 hG in EoCases.__str_arith_entail_is_approx_len.case_0
  step as ⟨e_v10, he_v10⟩
  store_step with Store.builtin_spec_eq s1 e_v10 (by rw [he_v10]; rfl) h_a1 h_v2 hinv1 h64 as ⟨v10, s2, hinv2, h_v10⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9
  have h_ite_v66 := (show if_6_eo__24str_5farith_5fentail_5fis_5fapprox_5flen s2 v10 a2 v5 v8 v2 a1 ⦃ r s' => s'.Inv ∧ s2.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_6_eo__24str_5farith_5fentail_5fis_5fapprox_5flen
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s2
    rcases Store.boolean_value_term h_v10 with ⟨hx_11, hbv_11⟩ | ⟨hx_11, hbv_11⟩ | ⟨hx_11, hbv_11⟩
    · ite_branch hbv_11
      have h_ite_v29 := (show if_1_eo__24str_5farith_5fentail_5fis_5fapprox_5flen s2 a2 v5 v8 v2 ⦃ r s' => s'.Inv ∧ s2.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_1_eo__24str_5farith_5fentail_5fis_5fapprox_5flen more_0_eo__24str_5farith_5fentail_5fis_5fapprox_5flen
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s2
        rcases Store.boolean_value_term h_a2 with ⟨hx_11, hbv_11⟩ | ⟨hx_11, hbv_11⟩ | ⟨hx_11, hbv_11⟩
        · ite_branch hbv_11
          store_step with ih.eo__24get_5farith_5fpoly_5fnorm s2 v5 _ hinv2 h64 (hG.rem hrem) h_v5 as ⟨v11, s3, hinv3, h_v11⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10
          store_step with ih.eo__24str_5farith_5fentail_5fsimple_5frec s3 v11 _ hinv3 h64 (hG.rem hrem) h_v11 as ⟨v12, s4, hinv4, h_v12⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11
          step as ⟨e_v13, he_v13⟩
          store_step with CtorSpec.eo__3e_3d.construct s4 e_v13 (by rw [he_v13]; exact empty_args) hinv4 h64 as ⟨v13, s5, hinv5, h_v13⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
          step as ⟨e_v14, he_v14⟩
          store_step with CtorSpec.eo_str_2elen.construct s5 e_v14 (by rw [he_v14]; exact empty_args) hinv5 h64 as ⟨v14, s6, hinv6, h_v14⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13
          store_step with Store.apply_rep s6 v14 v8 _ _ hinv6 h64 h_v14 h_v8 (by ns_tac) (by ns_tac) as ⟨v15, s7, hinv7, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14
          store_step with Store.apply_rep s7 v13 v15 _ _ hinv7 h64 h_v13 h_v15 (by ns_tac) (by ns_tac) as ⟨v16, s8, hinv8, h_v16⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15
          step as ⟨e_v17, he_v17⟩
          store_step with CtorSpec.eo__2b.construct s8 e_v17 (by rw [he_v17]; exact empty_args) hinv8 h64 as ⟨v17, s9, hinv9, h_v17⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16
          store_step with Store.apply_rep s9 v17 v5 _ _ hinv9 h64 h_v17 h_v5 (by ns_tac) (by ns_tac) as ⟨v18, s10, hinv10, h_v18⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17
          step as ⟨e_v19, he_v19⟩
          store_step with CtorSpec.eo__2b.construct s10 e_v19 (by rw [he_v19]; exact empty_args) hinv10 h64 as ⟨v19, s11, hinv11, h_v19⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18
          store_step with Store.apply_rep s11 v19 v2 _ _ hinv11 h64 h_v19 h_v2 (by ns_tac) (by ns_tac) as ⟨v20, s12, hinv12, h_v20⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s12 0#u32 (0) (by scalar_tac) hinv12 h64 as ⟨v21, s13, hinv13, h_v21⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20
          store_step with Store.apply_rep s13 v20 v21 _ _ hinv13 h64 h_v20 h_v21 (by ns_tac) (by ns_tac) as ⟨v22, s14, hinv14, h_v22⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21
          store_step with Store.apply_rep s14 v18 v22 _ _ hinv14 h64 h_v18 h_v22 (by ns_tac) (by ns_tac) as ⟨v23, s15, hinv15, h_v23⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22
          store_step with Store.apply_rep s15 v16 v23 _ _ hinv15 h64 h_v16 h_v23 (by ns_tac) (by ns_tac) as ⟨v24, s16, hinv16, h_v24⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23
          store_step with ih.eo__24str_5farith_5fentail_5fsimple_5fpred s16 v24 _ hinv16 h64 (hG.rem hrem) h_v24 as ⟨v25, s17, hinv17, h_v25⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24
          step as ⟨e_v26, he_v26⟩
          store_step with Store.builtin_spec_and s17 e_v26 (by rw [he_v26]; rfl) h_v12 h_v25 hinv17 h64 as ⟨v26, s18, hinv18, h_v26⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25
          ite_done hinv18 hG with (eo_ite_true_rep _ hx_11 h_v26)
        · ite_branch hbv_11
          store_step with ih.eo__24get_5farith_5fpoly_5fnorm s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v27, s3, hinv3, h_v27⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10
          store_step with ih.eo__24str_5farith_5fentail_5fsimple_5frec s3 v27 _ hinv3 h64 (hG.rem hrem) h_v27 as ⟨v28, s4, hinv4, h_v28⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v27
          ite_done hinv4 hG with (eo_ite_false_rep _ hx_11 h_v28)
        · ite_branch hbv_11
          ite_stuck hinv2 hG with hx_11)
      store_step with h_ite_v29 as ⟨v29, s3, hinv3, h_v29⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10
      ite_done hinv3 hG with (eo_ite_true_rep _ hx_11 h_v29)
    · ite_branch hbv_11
      step as ⟨e_v30, he_v30⟩
      store_step with CtorSpec.eo_str_2elen.construct s2 e_v30 (by rw [he_v30]; exact empty_args) hinv2 h64 as ⟨v30, s3, hinv3, h_v30⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10
      store_step with Store.apply_rep s3 v30 v8 _ _ hinv3 h64 h_v30 h_v8 (by ns_tac) (by ns_tac) as ⟨v31, s4, hinv4, h_v31⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v30
      step as ⟨e_v32, he_v32⟩
      store_step with Store.builtin_spec_eq s4 e_v32 (by rw [he_v32]; rfl) h_a1 h_v31 hinv4 h64 as ⟨v32, s5, hinv5, h_v32⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v30 h_v31
      have h_ite_v65 := (show if_5_eo__24str_5farith_5fentail_5fis_5fapprox_5flen s5 v32 a2 v8 v5 a1 v2 ⦃ r s' => s'.Inv ∧ s5.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_5_eo__24str_5farith_5fentail_5fis_5fapprox_5flen
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s5
        rcases Store.boolean_value_term h_v32 with ⟨hx_33, hbv_33⟩ | ⟨hx_33, hbv_33⟩ | ⟨hx_33, hbv_33⟩
        · ite_branch hbv_33
          step as ⟨e_v33, he_v33⟩
          store_step with Store.builtin_spec_not s5 e_v33 (by rw [he_v33]; rfl) h_a2 hinv5 h64 as ⟨v33, s6, hinv6, h_v33⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v30 h_v31 h_v32
          ite_done hinv6 hG with (eo_ite_true_rep _ hx_33 h_v33)
        · ite_branch hbv_33
          step as ⟨e_v34, he_v34⟩
          store_step with CtorSpec.eo__2d.construct s5 e_v34 (by rw [he_v34]; exact empty_args) hinv5 h64 as ⟨v34, s6, hinv6, h_v34⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v30 h_v31 h_v32
          step as ⟨e_v35, he_v35⟩
          store_step with CtorSpec.eo_str_2elen.construct s6 e_v35 (by rw [he_v35]; exact empty_args) hinv6 h64 as ⟨v35, s7, hinv7, h_v35⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v30 h_v31 h_v32 h_v34
          store_step with Store.apply_rep s7 v35 v8 _ _ hinv7 h64 h_v35 h_v8 (by ns_tac) (by ns_tac) as ⟨v36, s8, hinv8, h_v36⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v30 h_v31 h_v32 h_v34 h_v35
          store_step with Store.apply_rep s8 v34 v36 _ _ hinv8 h64 h_v34 h_v36 (by ns_tac) (by ns_tac) as ⟨v37, s9, hinv9, h_v37⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v30 h_v31 h_v32 h_v34 h_v35 h_v36
          store_step with Store.apply_rep s9 v37 v5 _ _ hinv9 h64 h_v37 h_v5 (by ns_tac) (by ns_tac) as ⟨v38, s10, hinv10, h_v38⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v30 h_v31 h_v32 h_v34 h_v35 h_v36 h_v37
          step as ⟨e_v39, he_v39⟩
          store_step with Store.builtin_spec_eq s10 e_v39 (by rw [he_v39]; rfl) h_a1 h_v38 hinv10 h64 as ⟨v39, s11, hinv11, h_v39⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v30 h_v31 h_v32 h_v34 h_v35 h_v36 h_v37 h_v38
          have h_ite_v64 := (show if_4_eo__24str_5farith_5fentail_5fis_5fapprox_5flen s11 v39 a2 v5 v2 v8 ⦃ r s' => s'.Inv ∧ s11.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
            unfold if_4_eo__24str_5farith_5fentail_5fis_5fapprox_5flen
            have hrem := (hG.rem hrem)
            have hG := Store.Grows.refl s11
            rcases Store.boolean_value_term h_v39 with ⟨hx_40, hbv_40⟩ | ⟨hx_40, hbv_40⟩ | ⟨hx_40, hbv_40⟩
            · ite_branch hbv_40
              have h_ite_v62 := (show if_3_eo__24str_5farith_5fentail_5fis_5fapprox_5flen s11 a2 v5 v2 v8 ⦃ r s' => s'.Inv ∧ s11.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
                unfold if_3_eo__24str_5farith_5fentail_5fis_5fapprox_5flen more_2_eo__24str_5farith_5fentail_5fis_5fapprox_5flen
                have hrem := (hG.rem hrem)
                have hG := Store.Grows.refl s11
                rcases Store.boolean_value_term h_a2 with ⟨hx_40, hbv_40⟩ | ⟨hx_40, hbv_40⟩ | ⟨hx_40, hbv_40⟩
                · ite_branch hbv_40
                  store_step with ih.eo__24get_5farith_5fpoly_5fnorm s11 v5 _ hinv11 h64 (hG.rem hrem) h_v5 as ⟨v40, s12, hinv12, h_v40⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v30 h_v31 h_v32 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39
                  store_step with ih.eo__24str_5farith_5fentail_5fsimple_5frec s12 v40 _ hinv12 h64 (hG.rem hrem) h_v40 as ⟨v41, s13, hinv13, h_v41⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v30 h_v31 h_v32 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40
                  step as ⟨e_v42, he_v42⟩
                  store_step with CtorSpec.eo__3e_3d.construct s13 e_v42 (by rw [he_v42]; exact empty_args) hinv13 h64 as ⟨v42, s14, hinv14, h_v42⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v30 h_v31 h_v32 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41
                  step as ⟨e_v43, he_v43⟩
                  store_step with CtorSpec.eo__2b.construct s14 e_v43 (by rw [he_v43]; exact empty_args) hinv14 h64 as ⟨v43, s15, hinv15, h_v43⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v30 h_v31 h_v32 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42
                  store_step with Store.apply_rep s15 v43 v5 _ _ hinv15 h64 h_v43 h_v5 (by ns_tac) (by ns_tac) as ⟨v44, s16, hinv16, h_v44⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v30 h_v31 h_v32 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43
                  step as ⟨e_v45, he_v45⟩
                  store_step with CtorSpec.eo__2b.construct s16 e_v45 (by rw [he_v45]; exact empty_args) hinv16 h64 as ⟨v45, s17, hinv17, h_v45⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v30 h_v31 h_v32 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44
                  store_step with Store.apply_rep s17 v45 v2 _ _ hinv17 h64 h_v45 h_v2 (by ns_tac) (by ns_tac) as ⟨v46, s18, hinv18, h_v46⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v30 h_v31 h_v32 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45
                  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
                  store_step with Store.literal_int_u32_spec s18 0#u32 (0) (by scalar_tac) hinv18 h64 as ⟨v47, s19, hinv19, h_v47⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v30 h_v31 h_v32 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46
                  store_step with Store.apply_rep s19 v46 v47 _ _ hinv19 h64 h_v46 h_v47 (by ns_tac) (by ns_tac) as ⟨v48, s20, hinv20, h_v48⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v30 h_v31 h_v32 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47
                  store_step with Store.apply_rep s20 v44 v48 _ _ hinv20 h64 h_v44 h_v48 (by ns_tac) (by ns_tac) as ⟨v49, s21, hinv21, h_v49⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v30 h_v31 h_v32 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48
                  store_step with Store.apply_rep s21 v42 v49 _ _ hinv21 h64 h_v42 h_v49 (by ns_tac) (by ns_tac) as ⟨v50, s22, hinv22, h_v50⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v30 h_v31 h_v32 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49
                  step as ⟨e_v51, he_v51⟩
                  store_step with CtorSpec.eo_str_2elen.construct s22 e_v51 (by rw [he_v51]; exact empty_args) hinv22 h64 as ⟨v51, s23, hinv23, h_v51⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v30 h_v31 h_v32 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50
                  store_step with Store.apply_rep s23 v51 v8 _ _ hinv23 h64 h_v51 h_v8 (by ns_tac) (by ns_tac) as ⟨v52, s24, hinv24, h_v52⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v30 h_v31 h_v32 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51
                  store_step with Store.apply_rep s24 v50 v52 _ _ hinv24 h64 h_v50 h_v52 (by ns_tac) (by ns_tac) as ⟨v53, s25, hinv25, h_v53⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v30 h_v31 h_v32 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52
                  store_step with ih.eo__24str_5farith_5fentail_5fsimple_5fpred s25 v53 _ hinv25 h64 (hG.rem hrem) h_v53 as ⟨v54, s26, hinv26, h_v54⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v30 h_v31 h_v32 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53
                  step as ⟨e_v55, he_v55⟩
                  store_step with Store.builtin_spec_and s26 e_v55 (by rw [he_v55]; rfl) h_v41 h_v54 hinv26 h64 as ⟨v55, s27, hinv27, h_v55⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v30 h_v31 h_v32 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54
                  ite_done hinv27 hG with (eo_ite_true_rep _ hx_40 h_v55)
                · ite_branch hbv_40
                  step as ⟨e_v56, he_v56⟩
                  store_step with CtorSpec.eo__3e_3d.construct s11 e_v56 (by rw [he_v56]; exact empty_args) hinv11 h64 as ⟨v56, s12, hinv12, h_v56⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v30 h_v31 h_v32 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39
                  step as ⟨e_v57, he_v57⟩
                  store_step with CtorSpec.eo_str_2elen.construct s12 e_v57 (by rw [he_v57]; exact empty_args) hinv12 h64 as ⟨v57, s13, hinv13, h_v57⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v30 h_v31 h_v32 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v56
                  store_step with Store.apply_rep s13 v57 v8 _ _ hinv13 h64 h_v57 h_v8 (by ns_tac) (by ns_tac) as ⟨v58, s14, hinv14, h_v58⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v30 h_v31 h_v32 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v56 h_v57
                  store_step with Store.apply_rep s14 v56 v58 _ _ hinv14 h64 h_v56 h_v58 (by ns_tac) (by ns_tac) as ⟨v59, s15, hinv15, h_v59⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v30 h_v31 h_v32 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v56 h_v57 h_v58
                  store_step with Store.apply_rep s15 v59 v5 _ _ hinv15 h64 h_v59 h_v5 (by ns_tac) (by ns_tac) as ⟨v60, s16, hinv16, h_v60⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v30 h_v31 h_v32 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v56 h_v57 h_v58 h_v59
                  store_step with ih.eo__24str_5farith_5fentail_5fsimple_5fpred s16 v60 _ hinv16 h64 (hG.rem hrem) h_v60 as ⟨v61, s17, hinv17, h_v61⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v30 h_v31 h_v32 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v56 h_v57 h_v58 h_v59 h_v60
                  ite_done hinv17 hG with (eo_ite_false_rep _ hx_40 h_v61)
                · ite_branch hbv_40
                  ite_stuck hinv11 hG with hx_40)
              store_step with h_ite_v62 as ⟨v62, s12, hinv12, h_v62⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v30 h_v31 h_v32 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39
              ite_done hinv12 hG with (eo_ite_true_rep _ hx_40 h_v62)
            · ite_branch hbv_40
              store_step with Store.literal_boolean_spec s11 false hinv11 h64 as ⟨v63, s12, hinv12, h_v63⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v30 h_v31 h_v32 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39
              ite_done hinv12 hG with (eo_ite_false_rep _ hx_40 h_v63)
            · ite_branch hbv_40
              ite_stuck hinv11 hG with hx_40)
          store_step with h_ite_v64 as ⟨v64, s12, hinv12, h_v64⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v30 h_v31 h_v32 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39
          ite_done hinv12 hG with (eo_ite_false_rep _ hx_33 h_v64)
        · ite_branch hbv_33
          ite_stuck hinv5 hG with hx_33)
      store_step with h_ite_v65 as ⟨v65, s6, hinv6, h_v65⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v30 h_v31 h_v32
      ite_done hinv6 hG with (eo_ite_false_rep _ hx_11 h_v65)
    · ite_branch hbv_11
      ite_stuck hinv2 hG with hx_11)
  store_step with h_ite_v66 as ⟨v66, s3, hinv3, h_v66⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10
  case_done hinv3 hG with h_v66 in EoCases.__str_arith_entail_is_approx_len.case_0 using hn_a0 hn_a1 hn_a2 hn_v1 hn_v2 hn_v4 hn_v5 hn_v7 hn_v8

theorem case_1_eo__24str_5farith_5fentail_5fis_5fapprox_5flen_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_1_eo__24str_5farith_5fentail_5fis_5fapprox_5flen s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__str_arith_entail_is_approx_len.case_1 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__str_arith_entail_is_approx_len.case_1 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24str_5farith_5fentail_5fis_5fapprox_5flen
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__str_arith_entail_is_approx_len.case_1
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__str_arith_entail_is_approx_len.case_1
  pat_unapply h_v4 as ⟨v7, v8, x_v7, x_v8, h_v7, h_v8, hn_v7, hn_v8⟩ using hinv else hinv hG in EoCases.__str_arith_entail_is_approx_len.case_1
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_str_2ereplace.construct s e_v9 (by rw [he_v9]; exact empty_args) hinv h64 as ⟨v9, s1, hinv1, h_v9⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8
  pat_same v7 v9 with h_v7 h_v9 using hinv1 else hinv1 hG in EoCases.__str_arith_entail_is_approx_len.case_1
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo_str_2elen.construct s1 e_v10 (by rw [he_v10]; exact empty_args) hinv1 h64 as ⟨v10, s2, hinv2, h_v10⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9
  store_step with Store.apply_rep s2 v10 v8 _ _ hinv2 h64 h_v10 h_v8 (by ns_tac) (by ns_tac) as ⟨v11, s3, hinv3, h_v11⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10
  step as ⟨e_v12, he_v12⟩
  store_step with Store.builtin_spec_eq s3 e_v12 (by rw [he_v12]; rfl) h_a1 h_v11 hinv3 h64 as ⟨v12, s4, hinv4, h_v12⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11
  have h_ite_v63 := (show if_12_eo__24str_5farith_5fentail_5fis_5fapprox_5flen s4 v12 a2 v2 v5 v8 a1 ⦃ r s' => s'.Inv ∧ s4.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_12_eo__24str_5farith_5fentail_5fis_5fapprox_5flen more_11_eo__24str_5farith_5fentail_5fis_5fapprox_5flen
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s4
    rcases Store.boolean_value_term h_v12 with ⟨hx_13, hbv_13⟩ | ⟨hx_13, hbv_13⟩ | ⟨hx_13, hbv_13⟩
    · ite_branch hbv_13
      have h_ite_v38 := (show if_8_eo__24str_5farith_5fentail_5fis_5fapprox_5flen s4 a2 v2 v5 v8 ⦃ r s' => s'.Inv ∧ s4.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_8_eo__24str_5farith_5fentail_5fis_5fapprox_5flen more_7_eo__24str_5farith_5fentail_5fis_5fapprox_5flen
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s4
        rcases Store.boolean_value_term h_a2 with ⟨hx_13, hbv_13⟩ | ⟨hx_13, hbv_13⟩ | ⟨hx_13, hbv_13⟩
        · ite_branch hbv_13
          step as ⟨e_v13, he_v13⟩
          store_step with CtorSpec.eo__3e_3d.construct s4 e_v13 (by rw [he_v13]; exact empty_args) hinv4 h64 as ⟨v13, s5, hinv5, h_v13⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
          step as ⟨e_v14, he_v14⟩
          store_step with CtorSpec.eo_str_2elen.construct s5 e_v14 (by rw [he_v14]; exact empty_args) hinv5 h64 as ⟨v14, s6, hinv6, h_v14⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13
          store_step with Store.apply_rep s6 v14 v2 _ _ hinv6 h64 h_v14 h_v2 (by ns_tac) (by ns_tac) as ⟨v15, s7, hinv7, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14
          store_step with Store.apply_rep s7 v13 v15 _ _ hinv7 h64 h_v13 h_v15 (by ns_tac) (by ns_tac) as ⟨v16, s8, hinv8, h_v16⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15
          step as ⟨e_v17, he_v17⟩
          store_step with CtorSpec.eo_str_2elen.construct s8 e_v17 (by rw [he_v17]; exact empty_args) hinv8 h64 as ⟨v17, s9, hinv9, h_v17⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16
          store_step with Store.apply_rep s9 v17 v5 _ _ hinv9 h64 h_v17 h_v5 (by ns_tac) (by ns_tac) as ⟨v18, s10, hinv10, h_v18⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17
          store_step with Store.apply_rep s10 v16 v18 _ _ hinv10 h64 h_v16 h_v18 (by ns_tac) (by ns_tac) as ⟨v19, s11, hinv11, h_v19⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18
          store_step with ih.eo__24str_5farith_5fentail_5fsimple_5fpred s11 v19 _ hinv11 h64 (hG.rem hrem) h_v19 as ⟨v20, s12, hinv12, h_v20⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19
          step as ⟨e_v21, he_v21⟩
          store_step with CtorSpec.eo__3e_3d.construct s12 e_v21 (by rw [he_v21]; exact empty_args) hinv12 h64 as ⟨v21, s13, hinv13, h_v21⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20
          step as ⟨e_v22, he_v22⟩
          store_step with CtorSpec.eo_str_2elen.construct s13 e_v22 (by rw [he_v22]; exact empty_args) hinv13 h64 as ⟨v22, s14, hinv14, h_v22⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21
          store_step with Store.apply_rep s14 v22 v2 _ _ hinv14 h64 h_v22 h_v2 (by ns_tac) (by ns_tac) as ⟨v23, s15, hinv15, h_v23⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22
          store_step with Store.apply_rep s15 v21 v23 _ _ hinv15 h64 h_v21 h_v23 (by ns_tac) (by ns_tac) as ⟨v24, s16, hinv16, h_v24⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23
          step as ⟨e_v25, he_v25⟩
          store_step with CtorSpec.eo_str_2elen.construct s16 e_v25 (by rw [he_v25]; exact empty_args) hinv16 h64 as ⟨v25, s17, hinv17, h_v25⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24
          store_step with Store.apply_rep s17 v25 v8 _ _ hinv17 h64 h_v25 h_v8 (by ns_tac) (by ns_tac) as ⟨v26, s18, hinv18, h_v26⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25
          store_step with Store.apply_rep s18 v24 v26 _ _ hinv18 h64 h_v24 h_v26 (by ns_tac) (by ns_tac) as ⟨v27, s19, hinv19, h_v27⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26
          store_step with ih.eo__24str_5farith_5fentail_5fsimple_5fpred s19 v27 _ hinv19 h64 (hG.rem hrem) h_v27 as ⟨v28, s20, hinv20, h_v28⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27
          step as ⟨e_v29, he_v29⟩
          store_step with Store.builtin_spec_or s20 e_v29 (by rw [he_v29]; rfl) h_v20 h_v28 hinv20 h64 as ⟨v29, s21, hinv21, h_v29⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28
          ite_done hinv21 hG with (eo_ite_true_rep _ hx_13 h_v29)
        · ite_branch hbv_13
          step as ⟨e_v30, he_v30⟩
          store_step with CtorSpec.eo__3e_3d.construct s4 e_v30 (by rw [he_v30]; exact empty_args) hinv4 h64 as ⟨v30, s5, hinv5, h_v30⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
          step as ⟨e_v31, he_v31⟩
          store_step with CtorSpec.eo_str_2elen.construct s5 e_v31 (by rw [he_v31]; exact empty_args) hinv5 h64 as ⟨v31, s6, hinv6, h_v31⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v30
          store_step with Store.apply_rep s6 v31 v5 _ _ hinv6 h64 h_v31 h_v5 (by ns_tac) (by ns_tac) as ⟨v32, s7, hinv7, h_v32⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v30 h_v31
          store_step with Store.apply_rep s7 v30 v32 _ _ hinv7 h64 h_v30 h_v32 (by ns_tac) (by ns_tac) as ⟨v33, s8, hinv8, h_v33⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v30 h_v31 h_v32
          step as ⟨e_v34, he_v34⟩
          store_step with CtorSpec.eo_str_2elen.construct s8 e_v34 (by rw [he_v34]; exact empty_args) hinv8 h64 as ⟨v34, s9, hinv9, h_v34⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v30 h_v31 h_v32 h_v33
          store_step with Store.apply_rep s9 v34 v2 _ _ hinv9 h64 h_v34 h_v2 (by ns_tac) (by ns_tac) as ⟨v35, s10, hinv10, h_v35⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v30 h_v31 h_v32 h_v33 h_v34
          store_step with Store.apply_rep s10 v33 v35 _ _ hinv10 h64 h_v33 h_v35 (by ns_tac) (by ns_tac) as ⟨v36, s11, hinv11, h_v36⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35
          store_step with ih.eo__24str_5farith_5fentail_5fsimple_5fpred s11 v36 _ hinv11 h64 (hG.rem hrem) h_v36 as ⟨v37, s12, hinv12, h_v37⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36
          ite_done hinv12 hG with (eo_ite_false_rep _ hx_13 h_v37)
        · ite_branch hbv_13
          ite_stuck hinv4 hG with hx_13)
      store_step with h_ite_v38 as ⟨v38, s5, hinv5, h_v38⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
      ite_done hinv5 hG with (eo_ite_true_rep _ hx_13 h_v38)
    · ite_branch hbv_13
      step as ⟨e_v39, he_v39⟩
      store_step with CtorSpec.eo__2b.construct s4 e_v39 (by rw [he_v39]; exact empty_args) hinv4 h64 as ⟨v39, s5, hinv5, h_v39⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
      step as ⟨e_v40, he_v40⟩
      store_step with CtorSpec.eo_str_2elen.construct s5 e_v40 (by rw [he_v40]; exact empty_args) hinv5 h64 as ⟨v40, s6, hinv6, h_v40⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v39
      store_step with Store.apply_rep s6 v40 v8 _ _ hinv6 h64 h_v40 h_v8 (by ns_tac) (by ns_tac) as ⟨v41, s7, hinv7, h_v41⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v39 h_v40
      store_step with Store.apply_rep s7 v39 v41 _ _ hinv7 h64 h_v39 h_v41 (by ns_tac) (by ns_tac) as ⟨v42, s8, hinv8, h_v42⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v39 h_v40 h_v41
      step as ⟨e_v43, he_v43⟩
      store_step with CtorSpec.eo__2b.construct s8 e_v43 (by rw [he_v43]; exact empty_args) hinv8 h64 as ⟨v43, s9, hinv9, h_v43⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v39 h_v40 h_v41 h_v42
      step as ⟨e_v44, he_v44⟩
      store_step with CtorSpec.eo_str_2elen.construct s9 e_v44 (by rw [he_v44]; exact empty_args) hinv9 h64 as ⟨v44, s10, hinv10, h_v44⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v39 h_v40 h_v41 h_v42 h_v43
      store_step with Store.apply_rep s10 v44 v2 _ _ hinv10 h64 h_v44 h_v2 (by ns_tac) (by ns_tac) as ⟨v45, s11, hinv11, h_v45⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44
      store_step with Store.apply_rep s11 v43 v45 _ _ hinv11 h64 h_v43 h_v45 (by ns_tac) (by ns_tac) as ⟨v46, s12, hinv12, h_v46⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45
      try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
      store_step with Store.literal_int_u32_spec s12 0#u32 (0) (by scalar_tac) hinv12 h64 as ⟨v47, s13, hinv13, h_v47⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46
      store_step with Store.apply_rep s13 v46 v47 _ _ hinv13 h64 h_v46 h_v47 (by ns_tac) (by ns_tac) as ⟨v48, s14, hinv14, h_v48⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47
      store_step with Store.apply_rep s14 v42 v48 _ _ hinv14 h64 h_v42 h_v48 (by ns_tac) (by ns_tac) as ⟨v49, s15, hinv15, h_v49⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48
      step as ⟨e_v50, he_v50⟩
      store_step with Store.builtin_spec_eq s15 e_v50 (by rw [he_v50]; rfl) h_a1 h_v49 hinv15 h64 as ⟨v50, s16, hinv16, h_v50⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49
      have h_ite_v62 := (show if_10_eo__24str_5farith_5fentail_5fis_5fapprox_5flen s16 v50 a2 v8 v5 a1 ⦃ r s' => s'.Inv ∧ s16.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_10_eo__24str_5farith_5fentail_5fis_5fapprox_5flen
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s16
        rcases Store.boolean_value_term h_v50 with ⟨hx_51, hbv_51⟩ | ⟨hx_51, hbv_51⟩ | ⟨hx_51, hbv_51⟩
        · ite_branch hbv_51
          step as ⟨e_v51, he_v51⟩
          store_step with Store.builtin_spec_not s16 e_v51 (by rw [he_v51]; rfl) h_a2 hinv16 h64 as ⟨v51, s17, hinv17, h_v51⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50
          ite_done hinv17 hG with (eo_ite_true_rep _ hx_51 h_v51)
        · ite_branch hbv_51
          step as ⟨e_v52, he_v52⟩
          store_step with CtorSpec.eo__2d.construct s16 e_v52 (by rw [he_v52]; exact empty_args) hinv16 h64 as ⟨v52, s17, hinv17, h_v52⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50
          step as ⟨e_v53, he_v53⟩
          store_step with CtorSpec.eo_str_2elen.construct s17 e_v53 (by rw [he_v53]; exact empty_args) hinv17 h64 as ⟨v53, s18, hinv18, h_v53⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v52
          store_step with Store.apply_rep s18 v53 v8 _ _ hinv18 h64 h_v53 h_v8 (by ns_tac) (by ns_tac) as ⟨v54, s19, hinv19, h_v54⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v52 h_v53
          store_step with Store.apply_rep s19 v52 v54 _ _ hinv19 h64 h_v52 h_v54 (by ns_tac) (by ns_tac) as ⟨v55, s20, hinv20, h_v55⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v52 h_v53 h_v54
          step as ⟨e_v56, he_v56⟩
          store_step with CtorSpec.eo_str_2elen.construct s20 e_v56 (by rw [he_v56]; exact empty_args) hinv20 h64 as ⟨v56, s21, hinv21, h_v56⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v52 h_v53 h_v54 h_v55
          store_step with Store.apply_rep s21 v56 v5 _ _ hinv21 h64 h_v56 h_v5 (by ns_tac) (by ns_tac) as ⟨v57, s22, hinv22, h_v57⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v52 h_v53 h_v54 h_v55 h_v56
          store_step with Store.apply_rep s22 v55 v57 _ _ hinv22 h64 h_v55 h_v57 (by ns_tac) (by ns_tac) as ⟨v58, s23, hinv23, h_v58⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57
          step as ⟨e_v59, he_v59⟩
          store_step with Store.builtin_spec_eq s23 e_v59 (by rw [he_v59]; rfl) h_a1 h_v58 hinv23 h64 as ⟨v59, s24, hinv24, h_v59⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58
          have h_ite_v61 := (show if_9_eo__24str_5farith_5fentail_5fis_5fapprox_5flen s24 v59 a2 ⦃ r s' => s'.Inv ∧ s24.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
            unfold if_9_eo__24str_5farith_5fentail_5fis_5fapprox_5flen
            have hrem := (hG.rem hrem)
            have hG := Store.Grows.refl s24
            rcases Store.boolean_value_term h_v59 with ⟨hx_60, hbv_60⟩ | ⟨hx_60, hbv_60⟩ | ⟨hx_60, hbv_60⟩
            · ite_branch hbv_60
              ite_done hinv24 hG with (eo_ite_true_rep _ hx_60 h_a2)
            · ite_branch hbv_60
              store_step with Store.literal_boolean_spec s24 false hinv24 h64 as ⟨v60, s25, hinv25, h_v60⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59
              ite_done hinv25 hG with (eo_ite_false_rep _ hx_60 h_v60)
            · ite_branch hbv_60
              ite_stuck hinv24 hG with hx_60)
          store_step with h_ite_v61 as ⟨v61, s25, hinv25, h_v61⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59
          ite_done hinv25 hG with (eo_ite_false_rep _ hx_51 h_v61)
        · ite_branch hbv_51
          ite_stuck hinv16 hG with hx_51)
      store_step with h_ite_v62 as ⟨v62, s17, hinv17, h_v62⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50
      ite_done hinv17 hG with (eo_ite_false_rep _ hx_13 h_v62)
    · ite_branch hbv_13
      ite_stuck hinv4 hG with hx_13)
  store_step with h_ite_v63 as ⟨v63, s5, hinv5, h_v63⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
  case_done hinv5 hG with h_v63 in EoCases.__str_arith_entail_is_approx_len.case_1 using hn_a0 hn_a1 hn_a2 hn_v1 hn_v2 hn_v4 hn_v5 hn_v7 hn_v8

theorem case_2_eo__24str_5farith_5fentail_5fis_5fapprox_5flen_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_2_eo__24str_5farith_5fentail_5fis_5fapprox_5flen s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__str_arith_entail_is_approx_len.case_2 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__str_arith_entail_is_approx_len.case_2 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24str_5farith_5fentail_5fis_5fapprox_5flen more_16_eo__24str_5farith_5fentail_5fis_5fapprox_5flen
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__str_arith_entail_is_approx_len.case_2
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_str_2efrom_5fint.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__str_arith_entail_is_approx_len.case_2
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo__2b.construct s1 e_v4 (by rw [he_v4]; exact empty_args) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v3
  store_step with Store.apply_rep s2 v4 v2 _ _ hinv2 h64 h_v4 h_v2 (by ns_tac) (by ns_tac) as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v3 h_v4
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__2b.construct s3 e_v6 (by rw [he_v6]; exact empty_args) hinv3 h64 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v3 h_v4 h_v5
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s4 1#u32 (1) (by scalar_tac) hinv4 h64 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  store_step with Store.apply_rep s5 v6 v7 _ _ hinv5 h64 h_v6 h_v7 (by ns_tac) (by ns_tac) as ⟨v8, s6, hinv6, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s6 0#u32 (0) (by scalar_tac) hinv6 h64 as ⟨v9, s7, hinv7, h_v9⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
  store_step with Store.apply_rep s7 v8 v9 _ _ hinv7 h64 h_v8 h_v9 (by ns_tac) (by ns_tac) as ⟨v10, s8, hinv8, h_v10⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  store_step with Store.apply_rep s8 v5 v10 _ _ hinv8 h64 h_v5 h_v10 (by ns_tac) (by ns_tac) as ⟨v11, s9, hinv9, h_v11⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
  step as ⟨e_v12, he_v12⟩
  store_step with Store.builtin_spec_eq s9 e_v12 (by rw [he_v12]; rfl) h_a1 h_v11 hinv9 h64 as ⟨v12, s10, hinv10, h_v12⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11
  have h_ite_v33 := (show if_15_eo__24str_5farith_5fentail_5fis_5fapprox_5flen s10 v12 a2 v2 a1 ⦃ r s' => s'.Inv ∧ s10.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_15_eo__24str_5farith_5fentail_5fis_5fapprox_5flen
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s10
    rcases Store.boolean_value_term h_v12 with ⟨hx_13, hbv_13⟩ | ⟨hx_13, hbv_13⟩ | ⟨hx_13, hbv_13⟩
    · ite_branch hbv_13
      step as ⟨e_v13, he_v13⟩
      store_step with Store.builtin_spec_not s10 e_v13 (by rw [he_v13]; rfl) h_a2 hinv10 h64 as ⟨v13, s11, hinv11, h_v13⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
      store_step with ih.eo__24get_5farith_5fpoly_5fnorm s11 v2 _ hinv11 h64 (hG.rem hrem) h_v2 as ⟨v14, s12, hinv12, h_v14⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13
      store_step with ih.eo__24str_5farith_5fentail_5fsimple_5frec s12 v14 _ hinv12 h64 (hG.rem hrem) h_v14 as ⟨v15, s13, hinv13, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14
      step as ⟨e_v16, he_v16⟩
      store_step with Store.builtin_spec_and s13 e_v16 (by rw [he_v16]; rfl) h_v13 h_v15 hinv13 h64 as ⟨v16, s14, hinv14, h_v16⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15
      ite_done hinv14 hG with (eo_ite_true_rep _ hx_13 h_v16)
    · ite_branch hbv_13
      step as ⟨e_v17, he_v17⟩
      store_step with Store.builtin_spec_eq s10 e_v17 (by rw [he_v17]; rfl) h_a1 h_v2 hinv10 h64 as ⟨v17, s11, hinv11, h_v17⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
      have h_ite_v32 := (show if_14_eo__24str_5farith_5fentail_5fis_5fapprox_5flen s11 v17 a2 v2 a1 ⦃ r s' => s'.Inv ∧ s11.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_14_eo__24str_5farith_5fentail_5fis_5fapprox_5flen
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s11
        rcases Store.boolean_value_term h_v17 with ⟨hx_18, hbv_18⟩ | ⟨hx_18, hbv_18⟩ | ⟨hx_18, hbv_18⟩
        · ite_branch hbv_18
          step as ⟨e_v18, he_v18⟩
          store_step with Store.builtin_spec_not s11 e_v18 (by rw [he_v18]; rfl) h_a2 hinv11 h64 as ⟨v18, s12, hinv12, h_v18⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v17
          step as ⟨e_v19, he_v19⟩
          store_step with CtorSpec.eo__3e.construct s12 e_v19 (by rw [he_v19]; exact empty_args) hinv12 h64 as ⟨v19, s13, hinv13, h_v19⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v17 h_v18
          store_step with Store.apply_rep s13 v19 v2 _ _ hinv13 h64 h_v19 h_v2 (by ns_tac) (by ns_tac) as ⟨v20, s14, hinv14, h_v20⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v17 h_v18 h_v19
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s14 0#u32 (0) (by scalar_tac) hinv14 h64 as ⟨v21, s15, hinv15, h_v21⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v17 h_v18 h_v19 h_v20
          store_step with Store.apply_rep s15 v20 v21 _ _ hinv15 h64 h_v20 h_v21 (by ns_tac) (by ns_tac) as ⟨v22, s16, hinv16, h_v22⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v17 h_v18 h_v19 h_v20 h_v21
          store_step with ih.eo__24str_5farith_5fentail_5fsimple_5fpred s16 v22 _ hinv16 h64 (hG.rem hrem) h_v22 as ⟨v23, s17, hinv17, h_v23⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22
          step as ⟨e_v24, he_v24⟩
          store_step with Store.builtin_spec_and s17 e_v24 (by rw [he_v24]; rfl) h_v18 h_v23 hinv17 h64 as ⟨v24, s18, hinv18, h_v24⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23
          ite_done hinv18 hG with (eo_ite_true_rep _ hx_18 h_v24)
        · ite_branch hbv_18
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s11 1#u32 (1) (by scalar_tac) hinv11 h64 as ⟨v25, s12, hinv12, h_v25⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v17
          step as ⟨e_v26, he_v26⟩
          store_step with Store.builtin_spec_eq s12 e_v26 (by rw [he_v26]; rfl) h_a1 h_v25 hinv12 h64 as ⟨v26, s13, hinv13, h_v26⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v17 h_v25
          have h_ite_v31 := (show if_13_eo__24str_5farith_5fentail_5fis_5fapprox_5flen s13 v26 v2 a2 ⦃ r s' => s'.Inv ∧ s13.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
            unfold if_13_eo__24str_5farith_5fentail_5fis_5fapprox_5flen
            have hrem := (hG.rem hrem)
            have hG := Store.Grows.refl s13
            rcases Store.boolean_value_term h_v26 with ⟨hx_27, hbv_27⟩ | ⟨hx_27, hbv_27⟩ | ⟨hx_27, hbv_27⟩
            · ite_branch hbv_27
              store_step with ih.eo__24get_5farith_5fpoly_5fnorm s13 v2 _ hinv13 h64 (hG.rem hrem) h_v2 as ⟨v27, s14, hinv14, h_v27⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v17 h_v25 h_v26
              store_step with ih.eo__24str_5farith_5fentail_5fsimple_5frec s14 v27 _ hinv14 h64 (hG.rem hrem) h_v27 as ⟨v28, s15, hinv15, h_v28⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v17 h_v25 h_v26 h_v27
              step as ⟨e_v29, he_v29⟩
              store_step with Store.builtin_spec_and s15 e_v29 (by rw [he_v29]; rfl) h_a2 h_v28 hinv15 h64 as ⟨v29, s16, hinv16, h_v29⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v17 h_v25 h_v26 h_v27 h_v28
              ite_done hinv16 hG with (eo_ite_true_rep _ hx_27 h_v29)
            · ite_branch hbv_27
              store_step with Store.literal_boolean_spec s13 false hinv13 h64 as ⟨v30, s14, hinv14, h_v30⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v17 h_v25 h_v26
              ite_done hinv14 hG with (eo_ite_false_rep _ hx_27 h_v30)
            · ite_branch hbv_27
              ite_stuck hinv13 hG with hx_27)
          store_step with h_ite_v31 as ⟨v31, s14, hinv14, h_v31⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v17 h_v25 h_v26
          ite_done hinv14 hG with (eo_ite_false_rep _ hx_18 h_v31)
        · ite_branch hbv_18
          ite_stuck hinv11 hG with hx_18)
      store_step with h_ite_v32 as ⟨v32, s12, hinv12, h_v32⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v17
      ite_done hinv12 hG with (eo_ite_false_rep _ hx_13 h_v32)
    · ite_branch hbv_13
      ite_stuck hinv10 hG with hx_13)
  store_step with h_ite_v33 as ⟨v33, s11, hinv11, h_v33⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
  case_done hinv11 hG with h_v33 in EoCases.__str_arith_entail_is_approx_len.case_2 using hn_a0 hn_a1 hn_a2 hn_v1 hn_v2

/-- logos's `__str_arith_entail_is_approx_len` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24str_5farith_5fentail_5fis_5fapprox_5flen.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __str_arith_entail_is_approx_len x_a0 x_a1 x_a2 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__str_arith_entail_is_approx_len.case_0 x_a0 x_a1 x_a2, EoCases.__str_arith_entail_is_approx_len.case_1 x_a0 x_a1 x_a2, EoCases.__str_arith_entail_is_approx_len.case_2 x_a0 x_a1 x_a2] HasStuck.stuck) := by
  conv => lhs; unfold __str_arith_entail_is_approx_len
  unfold EoCases.__str_arith_entail_is_approx_len.case_0 EoCases.__str_arith_entail_is_approx_len.case_1 EoCases.__str_arith_entail_is_approx_len.case_2
  logos_eq

theorem body_eo__24str_5farith_5fentail_5fis_5fapprox_5flen_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24str_5farith_5fentail_5fis_5fapprox_5flen s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__str_arith_entail_is_approx_len x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24str_5farith_5fentail_5fis_5fapprox_5flen.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24str_5farith_5fentail_5fis_5fapprox_5flen
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24str_5farith_5fentail_5fis_5fapprox_5flen_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1 hn_a2
  case_step with case_1_eo__24str_5farith_5fentail_5fis_5fapprox_5flen_spec n ih s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1 hn_a2 hc0
  case_step with case_2_eo__24str_5farith_5fentail_5fis_5fapprox_5flen_spec n ih s2 a0 a1 a2 x_a0 x_a1 x_a2 hinv2 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1 hn_a2 hc0 hc1
  body_stuck hinv3 hG using hn_a0 hn_a1 hn_a2 hc0 hc1 hc2 in EoCases.__str_arith_entail_is_approx_len.case_0 EoCases.__str_arith_entail_is_approx_len.case_1 EoCases.__str_arith_entail_is_approx_len.case_2

theorem eo__24str_5farith_5fentail_5fis_5fapprox_5flen_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24str_5farith_5fentail_5fis_5fapprox_5flen.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24str_5farith_5fentail_5fis_5fapprox_5flen
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24str_5farith_5fentail_5fis_5fapprox_5flen s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__str_arith_entail_is_approx_len x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24str_5farith_5fentail_5fis_5fapprox_5flen_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24str_5farith_5fentail_5fsimple_5fpred_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24str_5farith_5fentail_5fsimple_5fpred s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__str_arith_entail_simple_pred.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__str_arith_entail_simple_pred.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24str_5farith_5fentail_5fsimple_5fpred
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__str_arith_entail_simple_pred.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__str_arith_entail_simple_pred.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__3e_3d.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__str_arith_entail_simple_pred.case_0
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo__2d.construct s1 e_v7 (by rw [he_v7]; exact empty_args) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with Store.apply_rep s2 v7 v5 _ _ hinv2 h64 h_v7 h_v5 (by ns_tac) (by ns_tac) as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with Store.apply_rep s3 v8 v2 _ _ hinv3 h64 h_v8 h_v2 (by ns_tac) (by ns_tac) as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  store_step with ih.eo__24get_5farith_5fpoly_5fnorm s4 v9 _ hinv4 h64 (hG.rem hrem) h_v9 as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  store_step with ih.eo__24str_5farith_5fentail_5fsimple_5frec s5 v10 _ hinv5 h64 (hG.rem hrem) h_v10 as ⟨v11, s6, hinv6, h_v11⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
  case_done hinv6 hG with h_v11 in EoCases.__str_arith_entail_simple_pred.case_0 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_1_eo__24str_5farith_5fentail_5fsimple_5fpred_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_1_eo__24str_5farith_5fentail_5fsimple_5fpred s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__str_arith_entail_simple_pred.case_1 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__str_arith_entail_simple_pred.case_1 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24str_5farith_5fentail_5fsimple_5fpred more_0_eo__24str_5farith_5fentail_5fsimple_5fpred
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__str_arith_entail_simple_pred.case_1
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__str_arith_entail_simple_pred.case_1
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__3e.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__str_arith_entail_simple_pred.case_1
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo__2d.construct s1 e_v7 (by rw [he_v7]; exact empty_args) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with Store.apply_rep s2 v7 v5 _ _ hinv2 h64 h_v7 h_v5 (by ns_tac) (by ns_tac) as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__2b.construct s3 e_v9 (by rw [he_v9]; exact empty_args) hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  store_step with Store.apply_rep s4 v9 v2 _ _ hinv4 h64 h_v9 h_v2 (by ns_tac) (by ns_tac) as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  step as ⟨e_v11, he_v11⟩
  store_step with CtorSpec.eo__2b.construct s5 e_v11 (by rw [he_v11]; exact empty_args) hinv5 h64 as ⟨v11, s6, hinv6, h_v11⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s6 1#u32 (1) (by scalar_tac) hinv6 h64 as ⟨v12, s7, hinv7, h_v12⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11
  store_step with Store.apply_rep s7 v11 v12 _ _ hinv7 h64 h_v11 h_v12 (by ns_tac) (by ns_tac) as ⟨v13, s8, hinv8, h_v13⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s8 0#u32 (0) (by scalar_tac) hinv8 h64 as ⟨v14, s9, hinv9, h_v14⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13
  store_step with Store.apply_rep s9 v13 v14 _ _ hinv9 h64 h_v13 h_v14 (by ns_tac) (by ns_tac) as ⟨v15, s10, hinv10, h_v15⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14
  store_step with Store.apply_rep s10 v10 v15 _ _ hinv10 h64 h_v10 h_v15 (by ns_tac) (by ns_tac) as ⟨v16, s11, hinv11, h_v16⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15
  store_step with Store.apply_rep s11 v8 v16 _ _ hinv11 h64 h_v8 h_v16 (by ns_tac) (by ns_tac) as ⟨v17, s12, hinv12, h_v17⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16
  store_step with ih.eo__24get_5farith_5fpoly_5fnorm s12 v17 _ hinv12 h64 (hG.rem hrem) h_v17 as ⟨v18, s13, hinv13, h_v18⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17
  store_step with ih.eo__24str_5farith_5fentail_5fsimple_5frec s13 v18 _ hinv13 h64 (hG.rem hrem) h_v18 as ⟨v19, s14, hinv14, h_v19⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18
  case_done hinv14 hG with h_v19 in EoCases.__str_arith_entail_simple_pred.case_1 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

/-- logos's `__str_arith_entail_simple_pred` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24str_5farith_5fentail_5fsimple_5fpred.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __str_arith_entail_simple_pred x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__str_arith_entail_simple_pred.case_0 x_a0, EoCases.__str_arith_entail_simple_pred.case_1 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __str_arith_entail_simple_pred
  unfold EoCases.__str_arith_entail_simple_pred.case_0 EoCases.__str_arith_entail_simple_pred.case_1
  logos_eq

theorem body_eo__24str_5farith_5fentail_5fsimple_5fpred_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24str_5farith_5fentail_5fsimple_5fpred s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__str_arith_entail_simple_pred x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24str_5farith_5fentail_5fsimple_5fpred.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24str_5farith_5fentail_5fsimple_5fpred
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24str_5farith_5fentail_5fsimple_5fpred_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  case_step with case_1_eo__24str_5farith_5fentail_5fsimple_5fpred_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 using hn_a0 hc0
  body_stuck hinv2 hG using hn_a0 hc0 hc1 in EoCases.__str_arith_entail_simple_pred.case_0 EoCases.__str_arith_entail_simple_pred.case_1

theorem eo__24str_5farith_5fentail_5fsimple_5fpred_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24str_5farith_5fentail_5fsimple_5fpred.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24str_5farith_5fentail_5fsimple_5fpred
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24str_5farith_5fentail_5fsimple_5fpred s1 a0) (fun s' t => Represents.rep s' t (__str_arith_entail_simple_pred x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24str_5farith_5fentail_5fsimple_5fpred_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24str_5farith_5fentail_5fsimple_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24str_5farith_5fentail_5fsimple_5frec s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__str_arith_entail_simple_rec.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__str_arith_entail_simple_rec.case_0 x_a0 = some (__str_arith_entail_simple_rec y0)
      | core.result.Result.Ok none => EoCases.__str_arith_entail_simple_rec.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24str_5farith_5fentail_5fsimple_5frec
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__40_40poly_2ezero.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__str_arith_entail_simple_rec.case_0
  store_step with Store.literal_boolean_spec s1 true hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__str_arith_entail_simple_rec.case_0 using hn_a0

theorem case_1_eo__24str_5farith_5fentail_5fsimple_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_1_eo__24str_5farith_5fentail_5fsimple_5frec s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__str_arith_entail_simple_rec.case_1 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__str_arith_entail_simple_rec.case_1 x_a0 = some (__str_arith_entail_simple_rec y0)
      | core.result.Result.Ok none => EoCases.__str_arith_entail_simple_rec.case_1 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24str_5farith_5fentail_5fsimple_5frec more_0_eo__24str_5farith_5fentail_5fsimple_5frec
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__str_arith_entail_simple_rec.case_1
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__str_arith_entail_simple_rec.case_1
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__40_40poly.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__str_arith_entail_simple_rec.case_1
  pat_unapply h_v5 as ⟨v8, v9, x_v8, x_v9, h_v8, h_v9, hn_v8, hn_v9⟩ using hinv1 else hinv1 hG in EoCases.__str_arith_entail_simple_rec.case_1
  pat_unapply h_v8 as ⟨v11, v12, x_v11, x_v12, h_v11, h_v12, hn_v11, hn_v12⟩ using hinv1 else hinv1 hG in EoCases.__str_arith_entail_simple_rec.case_1
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo__40_40mon.construct s1 e_v13 (by rw [he_v13]; exact empty_args) hinv1 h64 as ⟨v13, s2, hinv2, h_v13⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12
  pat_same v11 v13 with h_v11 h_v13 using hinv2 else hinv2 hG in EoCases.__str_arith_entail_simple_rec.case_1
  pat_unapply h_v12 as ⟨v15, v16, x_v15, x_v16, h_v15, h_v16, hn_v15, hn_v16⟩ using hinv2 else hinv2 hG in EoCases.__str_arith_entail_simple_rec.case_1
  pat_unapply h_v15 as ⟨v18, v19, x_v18, x_v19, h_v18, h_v19, hn_v18, hn_v19⟩ using hinv2 else hinv2 hG in EoCases.__str_arith_entail_simple_rec.case_1
  step as ⟨e_v20, he_v20⟩
  store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s2 e_v20 (by rw [he_v20]; exact empty_args) hinv2 h64 as ⟨v20, s3, hinv3, h_v20⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v15 h_v16 h_v18 h_v19
  pat_same v18 v20 with h_v18 h_v20 using hinv3 else hinv3 hG in EoCases.__str_arith_entail_simple_rec.case_1
  pat_unapply h_v19 as ⟨v22, v23, x_v22, x_v23, h_v22, h_v23, hn_v22, hn_v23⟩ using hinv3 else hinv3 hG in EoCases.__str_arith_entail_simple_rec.case_1
  step as ⟨e_v24, he_v24⟩
  store_step with CtorSpec.eo_str_2elen.construct s3 e_v24 (by rw [he_v24]; exact empty_args) hinv3 h64 as ⟨v24, s4, hinv4, h_v24⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v15 h_v16 h_v18 h_v19 h_v20 h_v22 h_v23
  pat_same v22 v24 with h_v22 h_v24 using hinv4 else hinv4 hG in EoCases.__str_arith_entail_simple_rec.case_1
  step as ⟨e_v25, he_v25⟩
  store_step with CtorSpec.eo__40_40poly.construct s4 e_v25 (by rw [he_v25]; exact empty_args) hinv4 h64 as ⟨v25, s5, hinv5, h_v25⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v15 h_v16 h_v18 h_v19 h_v20 h_v22 h_v23 h_v24
  step as ⟨e_v26, he_v26⟩
  store_step with CtorSpec.eo__40_40mon.construct s5 e_v26 (by rw [he_v26]; exact empty_args) hinv5 h64 as ⟨v26, s6, hinv6, h_v26⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v15 h_v16 h_v18 h_v19 h_v20 h_v22 h_v23 h_v24 h_v25
  store_step with Store.apply_rep s6 v26 v16 _ _ hinv6 h64 h_v26 h_v16 (by ns_tac) (by ns_tac) as ⟨v27, s7, hinv7, h_v27⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v15 h_v16 h_v18 h_v19 h_v20 h_v22 h_v23 h_v24 h_v25 h_v26
  store_step with Store.apply_rep s7 v27 v9 _ _ hinv7 h64 h_v27 h_v9 (by ns_tac) (by ns_tac) as ⟨v28, s8, hinv8, h_v28⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v15 h_v16 h_v18 h_v19 h_v20 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27
  store_step with Store.apply_rep s8 v25 v28 _ _ hinv8 h64 h_v25 h_v28 (by ns_tac) (by ns_tac) as ⟨v29, s9, hinv9, h_v29⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v15 h_v16 h_v18 h_v19 h_v20 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28
  store_step with Store.apply_rep s9 v29 v2 _ _ hinv9 h64 h_v29 h_v2 (by ns_tac) (by ns_tac) as ⟨v30, s10, hinv10, h_v30⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v15 h_v16 h_v18 h_v19 h_v20 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29
  case_again hinv10 hG with h_v30 in EoCases.__str_arith_entail_simple_rec.case_1 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5 hn_v8 hn_v9 hn_v11 hn_v12 hn_v15 hn_v16 hn_v18 hn_v19 hn_v22 hn_v23

theorem case_2_eo__24str_5farith_5fentail_5fsimple_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_2_eo__24str_5farith_5fentail_5fsimple_5frec s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__str_arith_entail_simple_rec.case_2 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__str_arith_entail_simple_rec.case_2 x_a0 = some (__str_arith_entail_simple_rec y0)
      | core.result.Result.Ok none => EoCases.__str_arith_entail_simple_rec.case_2 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24str_5farith_5fentail_5fsimple_5frec
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__str_arith_entail_simple_rec.case_2
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__str_arith_entail_simple_rec.case_2
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__40_40poly.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__str_arith_entail_simple_rec.case_2
  pat_unapply h_v5 as ⟨v8, v9, x_v8, x_v9, h_v8, h_v9, hn_v8, hn_v9⟩ using hinv1 else hinv1 hG in EoCases.__str_arith_entail_simple_rec.case_2
  pat_unapply h_v8 as ⟨v11, v12, x_v11, x_v12, h_v11, h_v12, hn_v11, hn_v12⟩ using hinv1 else hinv1 hG in EoCases.__str_arith_entail_simple_rec.case_2
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo__40_40mon.construct s1 e_v13 (by rw [he_v13]; exact empty_args) hinv1 h64 as ⟨v13, s2, hinv2, h_v13⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12
  pat_same v11 v13 with h_v11 h_v13 using hinv2 else hinv2 hG in EoCases.__str_arith_entail_simple_rec.case_2
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s2 e_v14 (by rw [he_v14]; exact empty_args) hinv2 h64 as ⟨v14, s3, hinv3, h_v14⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13
  pat_same v12 v14 with h_v12 h_v14 using hinv3 else hinv3 hG in EoCases.__str_arith_entail_simple_rec.case_2
  step as ⟨e_v15, he_v15⟩
  store_step with Store.builtin_spec_is_neg s3 e_v15 (by rw [he_v15]; rfl) h_v9 hinv3 h64 as ⟨v15, s4, hinv4, h_v15⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14
  have h_ite_v18 := (show if_1_eo__24str_5farith_5fentail_5fsimple_5frec s4 v15 v2 ⦃ r s' => s'.Inv ∧ s4.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_1_eo__24str_5farith_5fentail_5fsimple_5frec
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s4
    rcases Store.boolean_value_term h_v15 with ⟨hx_16, hbv_16⟩ | ⟨hx_16, hbv_16⟩ | ⟨hx_16, hbv_16⟩
    · ite_branch hbv_16
      store_step with Store.literal_boolean_spec s4 false hinv4 h64 as ⟨v16, s5, hinv5, h_v16⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15
      ite_done hinv5 hG with (eo_ite_true_rep _ hx_16 h_v16)
    · ite_branch hbv_16
      store_step with ih.eo__24str_5farith_5fentail_5fsimple_5frec s4 v2 _ hinv4 h64 (hG.rem hrem) h_v2 as ⟨v17, s5, hinv5, h_v17⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15
      ite_done hinv5 hG with (eo_ite_false_rep _ hx_16 h_v17)
    · ite_branch hbv_16
      ite_stuck hinv4 hG with hx_16)
  store_step with h_ite_v18 as ⟨v18, s5, hinv5, h_v18⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15
  case_done hinv5 hG with h_v18 in EoCases.__str_arith_entail_simple_rec.case_2 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5 hn_v8 hn_v9 hn_v11 hn_v12

/-- logos's `__str_arith_entail_simple_rec` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24str_5farith_5fentail_5fsimple_5frec.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __str_arith_entail_simple_rec x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__str_arith_entail_simple_rec.case_0 x_a0, EoCases.__str_arith_entail_simple_rec.case_1 x_a0, EoCases.__str_arith_entail_simple_rec.case_2 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __str_arith_entail_simple_rec
  unfold EoCases.__str_arith_entail_simple_rec.case_0 EoCases.__str_arith_entail_simple_rec.case_1 EoCases.__str_arith_entail_simple_rec.case_2
  logos_eq

theorem step_eo__24str_5farith_5fentail_5fsimple_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    step_eo__24str_5farith_5fentail_5fsimple_5frec s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (Next.Done t) => Represents.rep s' t (__str_arith_entail_simple_rec x_a0)
      | core.result.Result.Ok (Next.Again arr) =>
        s'.budget < s.budget ∧ ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          __str_arith_entail_simple_rec x_a0 = __str_arith_entail_simple_rec y0
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24str_5farith_5fentail_5fsimple_5frec.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold step_eo__24str_5farith_5fentail_5fsimple_5frec
  have hG := Store.Grows.refl s
  tick_step as ⟨s1, hinv1⟩ growing hG carrying h_a0
  stuck_check h_a0 : x_a0 as hn_a0 else hinv1 hG
  round_step with case_0_eo__24str_5farith_5fentail_5fsimple_5frec_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc0⟩ growing hG carrying h_a0 hbud using hn_a0
  round_step with case_1_eo__24str_5farith_5fentail_5fsimple_5frec_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc1⟩ growing hG carrying h_a0 hbud using hn_a0 hc0
  round_step with case_2_eo__24str_5farith_5fentail_5fsimple_5frec_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s4, hinv4, hc2⟩ growing hG carrying h_a0 hbud using hn_a0 hc0 hc1
  round_stuck hinv4 hG using hn_a0 hc0 hc1 hc2 in EoCases.__str_arith_entail_simple_rec.case_0 EoCases.__str_arith_entail_simple_rec.case_1 EoCases.__str_arith_entail_simple_rec.case_2

theorem body_eo__24str_5farith_5fentail_5fsimple_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24str_5farith_5fentail_5fsimple_5frec s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__str_arith_entail_simple_rec x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  refine (?_ : ∀ (k : Nat) (a0 : Term) (s : Store) (x_a0 : _), s.budget ≤ k → s.Inv → s.remaining ≤ n →
      Represents.rep s a0 x_a0 →
      body_eo__24str_5farith_5fentail_5fsimple_5frec s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__str_arith_entail_simple_rec x_a0)
      | core.result.Result.Err _ => True ⦄div) s.budget a0 s x_a0 le_rfl hinv hrem h_a0
  intro k
  refine Nat.strong_induction_on k ?_
  intro k ihl a0 s x_a0 hk hinv hrem h_a0
  unfold body_eo__24str_5farith_5fentail_5fsimple_5frec body_eo__24str_5farith_5fentail_5fsimple_5frec_loop
  step with step_eo__24str_5farith_5fentail_5fsimple_5frec_spec n ih s a0 x_a0 hinv h64 hrem h_a0 as ⟨r, s1, hinv1, hg1, hr⟩
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
      unfold body_eo__24str_5farith_5fentail_5fsimple_5frec at hrec
      apply WP.dspec_mono hrec
      loop_close hg1 heq

theorem eo__24str_5farith_5fentail_5fsimple_5frec_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24str_5farith_5fentail_5fsimple_5frec.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24str_5farith_5fentail_5fsimple_5frec
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 1049#u32 _ [a0] rfl
    (fun s1 => body_eo__24str_5farith_5fentail_5fsimple_5frec s1 a0) (fun s' t => Represents.rep s' t (__str_arith_entail_simple_rec x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, y0, hargs, hb0, hr⟩ := ProgramSem.of_1049 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_1049 ⟨a0, x_a0, rfl, Rep.mono hpre h_a0, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24str_5farith_5fentail_5fsimple_5frec_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24str_5ffixed_5flen_5fre_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24str_5ffixed_5flen_5fre s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__str_fixed_len_re.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__str_fixed_len_re.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24str_5ffixed_5flen_5fre
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__str_fixed_len_re.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__str_fixed_len_re.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_re_2e_2b_2b.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__str_fixed_len_re.case_0
  store_step with ih.eo__24str_5ffixed_5flen_5fre s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24str_5ffixed_5flen_5fre s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  step as ⟨e_v9, he_v9⟩
  store_step with Store.builtin_spec_add s3 e_v9 (by rw [he_v9]; rfl) h_v7 h_v8 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__str_fixed_len_re.case_0 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_1_eo__24str_5ffixed_5flen_5fre_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_1_eo__24str_5ffixed_5flen_5fre s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__str_fixed_len_re.case_1 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__str_fixed_len_re.case_1 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24str_5ffixed_5flen_5fre
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_re_2eallchar.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__str_fixed_len_re.case_1
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s1 1#u32 (1) (by scalar_tac) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__str_fixed_len_re.case_1 using hn_a0

theorem case_2_eo__24str_5ffixed_5flen_5fre_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_2_eo__24str_5ffixed_5flen_5fre s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__str_fixed_len_re.case_2 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__str_fixed_len_re.case_2 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24str_5ffixed_5flen_5fre
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__str_fixed_len_re.case_2
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__str_fixed_len_re.case_2
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_re_2erange.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__str_fixed_len_re.case_2
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s1 1#u32 (1) (by scalar_tac) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  case_done hinv2 hG with h_v7 in EoCases.__str_fixed_len_re.case_2 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_3_eo__24str_5ffixed_5flen_5fre_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_3_eo__24str_5ffixed_5flen_5fre s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__str_fixed_len_re.case_3 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__str_fixed_len_re.case_3 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_3_eo__24str_5ffixed_5flen_5fre
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__str_fixed_len_re.case_3
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_str_2eto_5fre.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__str_fixed_len_re.case_3
  step as ⟨e_v4, he_v4⟩
  store_step with Store.builtin_spec_len s1 e_v4 (by rw [he_v4]; rfl) h_v2 hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  case_done hinv2 hG with h_v4 in EoCases.__str_fixed_len_re.case_3 using hn_a0 hn_v1 hn_v2

theorem case_4_eo__24str_5ffixed_5flen_5fre_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_4_eo__24str_5ffixed_5flen_5fre s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__str_fixed_len_re.case_4 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__str_fixed_len_re.case_4 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_4_eo__24str_5ffixed_5flen_5fre
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__str_fixed_len_re.case_4
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__str_fixed_len_re.case_4
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_re_2eunion.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__str_fixed_len_re.case_4
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo_re_2enone.construct s1 e_v7 (by rw [he_v7]; exact empty_args) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  step as ⟨e_v8, he_v8⟩
  store_step with Store.builtin_spec_eq s2 e_v8 (by rw [he_v8]; rfl) h_v2 h_v7 hinv2 h64 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  have h_ite_v14 := (show if_1_eo__24str_5ffixed_5flen_5fre s3 v8 v5 v2 ⦃ r s' => s'.Inv ∧ s3.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_1_eo__24str_5ffixed_5flen_5fre
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s3
    rcases Store.boolean_value_term h_v8 with ⟨hx_9, hbv_9⟩ | ⟨hx_9, hbv_9⟩ | ⟨hx_9, hbv_9⟩
    · ite_branch hbv_9
      store_step with ih.eo__24str_5ffixed_5flen_5fre s3 v5 _ hinv3 h64 (hG.rem hrem) h_v5 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
      ite_done hinv4 hG with (eo_ite_true_rep _ hx_9 h_v9)
    · ite_branch hbv_9
      store_step with ih.eo__24str_5ffixed_5flen_5fre s3 v2 _ hinv3 h64 (hG.rem hrem) h_v2 as ⟨v10, s4, hinv4, h_v10⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
      store_step with ih.eo__24str_5ffixed_5flen_5fre s4 v5 _ hinv4 h64 (hG.rem hrem) h_v5 as ⟨v11, s5, hinv5, h_v11⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v10
      have h_req_v13 := (show requires_0_eo__24str_5ffixed_5flen_5fre s5 v10 v11 v5 ⦃ r s' => s'.Inv ∧ s5.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold requires_0_eo__24str_5ffixed_5flen_5fre
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s5
        req_same v10 v11 with h_v10 h_v11 using hinv5 hG
        req_stuck h_v10 as hq_v10 using hinv5 hG
        store_step with ih.eo__24str_5ffixed_5flen_5fre s5 v5 _ hinv5 h64 (hG.rem hrem) h_v5 as ⟨v12, s6, hinv6, h_v12⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v10 h_v11
        req_done hinv6 hG with h_v12 using hq_v10)
      store_step with h_req_v13 as ⟨v13, s7, hinv7, h_v13⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v10 h_v11
      ite_done hinv7 hG with (eo_ite_false_rep _ hx_9 h_v13)
    · ite_branch hbv_9
      ite_stuck hinv3 hG with hx_9)
  store_step with h_ite_v14 as ⟨v14, s4, hinv4, h_v14⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v14 in EoCases.__str_fixed_len_re.case_4 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_5_eo__24str_5ffixed_5flen_5fre_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_5_eo__24str_5ffixed_5flen_5fre s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__str_fixed_len_re.case_5 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__str_fixed_len_re.case_5 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_5_eo__24str_5ffixed_5flen_5fre
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__str_fixed_len_re.case_5
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__str_fixed_len_re.case_5
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_re_2einter.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__str_fixed_len_re.case_5
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo_re_2eall.construct s1 e_v7 (by rw [he_v7]; exact empty_args) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  step as ⟨e_v8, he_v8⟩
  store_step with Store.builtin_spec_eq s2 e_v8 (by rw [he_v8]; rfl) h_v2 h_v7 hinv2 h64 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  have h_ite_v14 := (show if_3_eo__24str_5ffixed_5flen_5fre s3 v8 v5 v2 ⦃ r s' => s'.Inv ∧ s3.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_3_eo__24str_5ffixed_5flen_5fre
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s3
    rcases Store.boolean_value_term h_v8 with ⟨hx_9, hbv_9⟩ | ⟨hx_9, hbv_9⟩ | ⟨hx_9, hbv_9⟩
    · ite_branch hbv_9
      store_step with ih.eo__24str_5ffixed_5flen_5fre s3 v5 _ hinv3 h64 (hG.rem hrem) h_v5 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
      ite_done hinv4 hG with (eo_ite_true_rep _ hx_9 h_v9)
    · ite_branch hbv_9
      store_step with ih.eo__24str_5ffixed_5flen_5fre s3 v2 _ hinv3 h64 (hG.rem hrem) h_v2 as ⟨v10, s4, hinv4, h_v10⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
      store_step with ih.eo__24str_5ffixed_5flen_5fre s4 v5 _ hinv4 h64 (hG.rem hrem) h_v5 as ⟨v11, s5, hinv5, h_v11⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v10
      have h_req_v13 := (show requires_2_eo__24str_5ffixed_5flen_5fre s5 v10 v11 v5 ⦃ r s' => s'.Inv ∧ s5.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold requires_2_eo__24str_5ffixed_5flen_5fre
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s5
        req_same v10 v11 with h_v10 h_v11 using hinv5 hG
        req_stuck h_v10 as hq_v10 using hinv5 hG
        store_step with ih.eo__24str_5ffixed_5flen_5fre s5 v5 _ hinv5 h64 (hG.rem hrem) h_v5 as ⟨v12, s6, hinv6, h_v12⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v10 h_v11
        req_done hinv6 hG with h_v12 using hq_v10)
      store_step with h_req_v13 as ⟨v13, s7, hinv7, h_v13⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v10 h_v11
      ite_done hinv7 hG with (eo_ite_false_rep _ hx_9 h_v13)
    · ite_branch hbv_9
      ite_stuck hinv3 hG with hx_9)
  store_step with h_ite_v14 as ⟨v14, s4, hinv4, h_v14⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v14 in EoCases.__str_fixed_len_re.case_5 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem cases_0_0_eo__24str_5ffixed_5flen_5fre_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    cases_0_0_eo__24str_5ffixed_5flen_5fre s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__str_fixed_len_re.case_0 x_a0, EoCases.__str_fixed_len_re.case_1 x_a0, EoCases.__str_fixed_len_re.case_2 x_a0, EoCases.__str_fixed_len_re.case_3 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__str_fixed_len_re.case_0 x_a0 = none ∧ EoCases.__str_fixed_len_re.case_1 x_a0 = none ∧ EoCases.__str_fixed_len_re.case_2 x_a0 = none ∧ EoCases.__str_fixed_len_re.case_3 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_0_eo__24str_5ffixed_5flen_5fre
  have hG := Store.Grows.refl s
  group_step with case_0_eo__24str_5ffixed_5flen_5fre_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__str_fixed_len_re.case_0 x_a0, EoCases.__str_fixed_len_re.case_1 x_a0, EoCases.__str_fixed_len_re.case_2 x_a0, EoCases.__str_fixed_len_re.case_3 x_a0] = [] ++ [EoCases.__str_fixed_len_re.case_0 x_a0] ++ [EoCases.__str_fixed_len_re.case_1 x_a0, EoCases.__str_fixed_len_re.case_2 x_a0, EoCases.__str_fixed_len_re.case_3 x_a0] from rfl)
    otherwise ⟨hl_0⟩ using hn_a0
  group_step with case_1_eo__24str_5ffixed_5flen_5fre_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__str_fixed_len_re.case_0 x_a0, EoCases.__str_fixed_len_re.case_1 x_a0, EoCases.__str_fixed_len_re.case_2 x_a0, EoCases.__str_fixed_len_re.case_3 x_a0] = [EoCases.__str_fixed_len_re.case_0 x_a0] ++ [EoCases.__str_fixed_len_re.case_1 x_a0] ++ [EoCases.__str_fixed_len_re.case_2 x_a0, EoCases.__str_fixed_len_re.case_3 x_a0] from rfl)
    otherwise ⟨hl_1⟩ using hn_a0 hl_0
  group_step with case_2_eo__24str_5ffixed_5flen_5fre_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__str_fixed_len_re.case_0 x_a0, EoCases.__str_fixed_len_re.case_1 x_a0, EoCases.__str_fixed_len_re.case_2 x_a0, EoCases.__str_fixed_len_re.case_3 x_a0] = [EoCases.__str_fixed_len_re.case_0 x_a0, EoCases.__str_fixed_len_re.case_1 x_a0] ++ [EoCases.__str_fixed_len_re.case_2 x_a0] ++ [EoCases.__str_fixed_len_re.case_3 x_a0] from rfl)
    otherwise ⟨hl_2⟩ using hn_a0 hl_0 hl_1
  group_step with case_3_eo__24str_5ffixed_5flen_5fre_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__str_fixed_len_re.case_0 x_a0, EoCases.__str_fixed_len_re.case_1 x_a0, EoCases.__str_fixed_len_re.case_2 x_a0, EoCases.__str_fixed_len_re.case_3 x_a0] = [EoCases.__str_fixed_len_re.case_0 x_a0, EoCases.__str_fixed_len_re.case_1 x_a0, EoCases.__str_fixed_len_re.case_2 x_a0] ++ [EoCases.__str_fixed_len_re.case_3 x_a0] ++ [] from rfl)
    otherwise ⟨hl_3⟩ using hn_a0 hl_0 hl_1 hl_2
  group_none hinv4 hG with ⟨hl_0, hl_1, hl_2, hl_3⟩

theorem cases_0_1_eo__24str_5ffixed_5flen_5fre_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    cases_0_1_eo__24str_5ffixed_5flen_5fre s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__str_fixed_len_re.case_4 x_a0, EoCases.__str_fixed_len_re.case_5 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__str_fixed_len_re.case_4 x_a0 = none ∧ EoCases.__str_fixed_len_re.case_5 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_1_eo__24str_5ffixed_5flen_5fre
  have hG := Store.Grows.refl s
  group_step with case_4_eo__24str_5ffixed_5flen_5fre_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__str_fixed_len_re.case_4 x_a0, EoCases.__str_fixed_len_re.case_5 x_a0] = [] ++ [EoCases.__str_fixed_len_re.case_4 x_a0] ++ [EoCases.__str_fixed_len_re.case_5 x_a0] from rfl)
    otherwise ⟨hl_4⟩ using hn_a0
  group_step with case_5_eo__24str_5ffixed_5flen_5fre_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__str_fixed_len_re.case_4 x_a0, EoCases.__str_fixed_len_re.case_5 x_a0] = [EoCases.__str_fixed_len_re.case_4 x_a0] ++ [EoCases.__str_fixed_len_re.case_5 x_a0] ++ [] from rfl)
    otherwise ⟨hl_5⟩ using hn_a0 hl_4
  group_none hinv2 hG with ⟨hl_4, hl_5⟩

/-- logos's `__str_fixed_len_re` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24str_5ffixed_5flen_5fre.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __str_fixed_len_re x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__str_fixed_len_re.case_0 x_a0, EoCases.__str_fixed_len_re.case_1 x_a0, EoCases.__str_fixed_len_re.case_2 x_a0, EoCases.__str_fixed_len_re.case_3 x_a0, EoCases.__str_fixed_len_re.case_4 x_a0, EoCases.__str_fixed_len_re.case_5 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __str_fixed_len_re
  unfold EoCases.__str_fixed_len_re.case_0 EoCases.__str_fixed_len_re.case_1 EoCases.__str_fixed_len_re.case_2 EoCases.__str_fixed_len_re.case_3 EoCases.__str_fixed_len_re.case_4 EoCases.__str_fixed_len_re.case_5
  logos_eq

theorem body_eo__24str_5ffixed_5flen_5fre_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24str_5ffixed_5flen_5fre s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__str_fixed_len_re x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24str_5ffixed_5flen_5fre.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24str_5ffixed_5flen_5fre
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  body_group_step with cases_0_0_eo__24str_5ffixed_5flen_5fre_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__str_fixed_len_re.case_0 x_a0, EoCases.__str_fixed_len_re.case_1 x_a0, EoCases.__str_fixed_len_re.case_2 x_a0, EoCases.__str_fixed_len_re.case_3 x_a0, EoCases.__str_fixed_len_re.case_4 x_a0, EoCases.__str_fixed_len_re.case_5 x_a0] = [] ++ [EoCases.__str_fixed_len_re.case_0 x_a0, EoCases.__str_fixed_len_re.case_1 x_a0, EoCases.__str_fixed_len_re.case_2 x_a0, EoCases.__str_fixed_len_re.case_3 x_a0] ++ [EoCases.__str_fixed_len_re.case_4 x_a0, EoCases.__str_fixed_len_re.case_5 x_a0] from rfl)
    otherwise ⟨hl_0, hl_1, hl_2, hl_3⟩ using hn_a0
  body_group_step with cases_0_1_eo__24str_5ffixed_5flen_5fre_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__str_fixed_len_re.case_0 x_a0, EoCases.__str_fixed_len_re.case_1 x_a0, EoCases.__str_fixed_len_re.case_2 x_a0, EoCases.__str_fixed_len_re.case_3 x_a0, EoCases.__str_fixed_len_re.case_4 x_a0, EoCases.__str_fixed_len_re.case_5 x_a0] = [EoCases.__str_fixed_len_re.case_0 x_a0, EoCases.__str_fixed_len_re.case_1 x_a0, EoCases.__str_fixed_len_re.case_2 x_a0, EoCases.__str_fixed_len_re.case_3 x_a0] ++ [EoCases.__str_fixed_len_re.case_4 x_a0, EoCases.__str_fixed_len_re.case_5 x_a0] ++ [] from rfl)
    otherwise ⟨hl_4, hl_5⟩ using hn_a0 hl_0 hl_1 hl_2 hl_3
  body_stuck hinv2 hG using hn_a0 hl_0 hl_1 hl_2 hl_3 hl_4 hl_5 in EoCases.__str_fixed_len_re.case_0 EoCases.__str_fixed_len_re.case_1 EoCases.__str_fixed_len_re.case_2 EoCases.__str_fixed_len_re.case_3 EoCases.__str_fixed_len_re.case_4 EoCases.__str_fixed_len_re.case_5

theorem eo__24str_5ffixed_5flen_5fre_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24str_5ffixed_5flen_5fre.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24str_5ffixed_5flen_5fre
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 1059#u32 _ [a0] rfl
    (fun s1 => body_eo__24str_5ffixed_5flen_5fre s1 a0) (fun s' t => Represents.rep s' t (__str_fixed_len_re x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, y0, hargs, hb0, hr⟩ := ProgramSem.of_1059 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_1059 ⟨a0, x_a0, rfl, Rep.mono hpre h_a0, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24str_5ffixed_5flen_5fre_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24str_5fis_5fcompatible_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24str_5fis_5fcompatible s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__str_is_compatible.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _), arr.val = [u0, u1] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧
          EoCases.__str_is_compatible.case_0 x_a0 x_a1 = some (__str_is_compatible y0 y1)
      | core.result.Result.Ok none => EoCases.__str_is_compatible.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24str_5fis_5fcompatible
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__str_is_compatible.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__str_is_compatible.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__str_is_compatible.case_0
  pat_unapply h_a1 as ⟨v8, v9, x_v8, x_v9, h_v8, h_v9, hn_v8, hn_v9⟩ using hinv1 else hinv1 hG in EoCases.__str_is_compatible.case_0
  pat_unapply h_v8 as ⟨v11, v12, x_v11, x_v12, h_v11, h_v12, hn_v11, hn_v12⟩ using hinv1 else hinv1 hG in EoCases.__str_is_compatible.case_0
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s1 e_v13 (by rw [he_v13]; exact empty_args) hinv1 h64 as ⟨v13, s2, hinv2, h_v13⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12
  pat_same v11 v13 with h_v11 h_v13 using hinv2 else hinv2 hG in EoCases.__str_is_compatible.case_0
  pat_same v12 v5 with h_v12 h_v5 using hinv2 else hinv2 hG in EoCases.__str_is_compatible.case_0
  case_again hinv2 hG with h_v2 h_v9 in EoCases.__str_is_compatible.case_0 using hn_a0 hn_a1 hn_v1 hn_v2 hn_v4 hn_v5 hn_v8 hn_v9 hn_v11 hn_v12

theorem case_1_eo__24str_5fis_5fcompatible_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_1_eo__24str_5fis_5fcompatible s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__str_is_compatible.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _), arr.val = [u0, u1] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧
          EoCases.__str_is_compatible.case_1 x_a0 x_a1 = some (__str_is_compatible y0 y1)
      | core.result.Result.Ok none => EoCases.__str_is_compatible.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24str_5fis_5fcompatible
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__str_is_compatible.case_1
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__str_is_compatible.case_1
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__str_is_compatible.case_1
  pat_unapply h_a1 as ⟨v8, v9, x_v8, x_v9, h_v8, h_v9, hn_v8, hn_v9⟩ using hinv1 else hinv1 hG in EoCases.__str_is_compatible.case_1
  pat_unapply h_v8 as ⟨v11, v12, x_v11, x_v12, h_v11, h_v12, hn_v11, hn_v12⟩ using hinv1 else hinv1 hG in EoCases.__str_is_compatible.case_1
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s1 e_v13 (by rw [he_v13]; exact empty_args) hinv1 h64 as ⟨v13, s2, hinv2, h_v13⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12
  pat_same v11 v13 with h_v11 h_v13 using hinv2 else hinv2 hG in EoCases.__str_is_compatible.case_1
  step as ⟨e_v14, he_v14⟩
  store_step with Store.builtin_spec_eq s2 e_v14 (by rw [he_v14]; rfl) h_v5 h_v12 hinv2 h64 as ⟨v14, s3, hinv3, h_v14⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13
  have h_ite_v18 := (show if_0_eo__24str_5fis_5fcompatible s3 v14 v5 v12 ⦃ r s' => s'.Inv ∧ s3.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_0_eo__24str_5fis_5fcompatible
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s3
    rcases Store.boolean_value_term h_v14 with ⟨hx_15, hbv_15⟩ | ⟨hx_15, hbv_15⟩ | ⟨hx_15, hbv_15⟩
    · ite_branch hbv_15
      store_step with Store.literal_boolean_spec s3 false hinv3 h64 as ⟨v15, s4, hinv4, h_v15⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14
      ite_done hinv4 hG with (eo_ite_true_rep _ hx_15 h_v15)
    · ite_branch hbv_15
      store_step with ih.eo__24eo_5ftypeof s3 v5 _ hinv3 h64 (hG.rem hrem) h_v5 as ⟨v16, s4, hinv4, h_v16⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14
      store_step with ih.eo__24are_5fdistinct_5fterms_5ftype s4 v5 v12 v16 _ _ _ hinv4 h64 (hG.rem hrem) h_v5 h_v12 h_v16 as ⟨v17, s5, hinv5, h_v17⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v16
      ite_done hinv5 hG with (eo_ite_false_rep _ hx_15 h_v17)
    · ite_branch hbv_15
      ite_stuck hinv3 hG with hx_15)
  store_step with h_ite_v18 as ⟨v18, s4, hinv4, h_v18⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14
  store_step with Store.literal_boolean_spec s4 true hinv4 h64 as ⟨v19, s5, hinv5, h_v19⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v18
  have h_req_v21 := (show requires_1_eo__24str_5fis_5fcompatible s5 v18 v19 ⦃ r s' => s'.Inv ∧ s5.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold requires_1_eo__24str_5fis_5fcompatible
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s5
    req_same v18 v19 with h_v18 h_v19 using hinv5 hG
    req_stuck h_v18 as hq_v18 using hinv5 hG
    store_step with Store.literal_boolean_spec s5 false hinv5 h64 as ⟨v20, s6, hinv6, h_v20⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v18 h_v19
    req_done hinv6 hG with h_v20 using hq_v18)
  store_step with h_req_v21 as ⟨v21, s7, hinv7, h_v21⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v18 h_v19
  case_done hinv7 hG with h_v21 in EoCases.__str_is_compatible.case_1 using hn_a0 hn_a1 hn_v1 hn_v2 hn_v4 hn_v5 hn_v8 hn_v9 hn_v11 hn_v12

theorem case_2_eo__24str_5fis_5fcompatible_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_2_eo__24str_5fis_5fcompatible s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__str_is_compatible.case_2 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _), arr.val = [u0, u1] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧
          EoCases.__str_is_compatible.case_2 x_a0 x_a1 = some (__str_is_compatible y0 y1)
      | core.result.Result.Ok none => EoCases.__str_is_compatible.case_2 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24str_5fis_5fcompatible
  have hG := Store.Grows.refl s
  store_step with ih.eo__24str_5fis_5fempty s a0 _ hinv h64 hrem h_a0 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  store_step with ih.eo__24str_5fis_5fempty s1 a1 _ hinv1 h64 (hG.rem hrem) h_a1 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  step as ⟨e_v2, he_v2⟩
  store_step with Store.builtin_spec_or s2 e_v2 (by rw [he_v2]; rfl) h_v0 h_v1 hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1
  case_done hinv3 hG with h_v2 in EoCases.__str_is_compatible.case_2 using hn_a0 hn_a1

/-- logos's `__str_is_compatible` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24str_5fis_5fcompatible.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __str_is_compatible x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__str_is_compatible.case_0 x_a0 x_a1, EoCases.__str_is_compatible.case_1 x_a0 x_a1, EoCases.__str_is_compatible.case_2 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __str_is_compatible
  unfold EoCases.__str_is_compatible.case_0 EoCases.__str_is_compatible.case_1 EoCases.__str_is_compatible.case_2
  try unfold Eo.__eo_l_1___str_is_compatible
  logos_eq_deep

theorem step_eo__24str_5fis_5fcompatible_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    step_eo__24str_5fis_5fcompatible s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (Next.Done t) => Represents.rep s' t (__str_is_compatible x_a0 x_a1)
      | core.result.Result.Ok (Next.Again arr) =>
        s'.budget < s.budget ∧ ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _), arr.val = [u0, u1] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧
          __str_is_compatible x_a0 x_a1 = __str_is_compatible y0 y1
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24str_5fis_5fcompatible.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold step_eo__24str_5fis_5fcompatible
  have hG := Store.Grows.refl s
  tick_step as ⟨s1, hinv1⟩ growing hG carrying h_a0 h_a1
  stuck_check h_a0 : x_a0 as hn_a0 else hinv1 hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv1 hG
  round_step with case_0_eo__24str_5fis_5fcompatible_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s2, hinv2, hc0⟩ growing hG carrying h_a0 h_a1 hbud using hn_a0 hn_a1
  round_step with case_1_eo__24str_5fis_5fcompatible_spec n ih s2 a0 a1 x_a0 x_a1 hinv2 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s3, hinv3, hc1⟩ growing hG carrying h_a0 h_a1 hbud using hn_a0 hn_a1 hc0
  round_step with case_2_eo__24str_5fis_5fcompatible_spec n ih s3 a0 a1 x_a0 x_a1 hinv3 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s4, hinv4, hc2⟩ growing hG carrying h_a0 h_a1 hbud using hn_a0 hn_a1 hc0 hc1
  round_stuck hinv4 hG using hn_a0 hn_a1 hc0 hc1 hc2 in EoCases.__str_is_compatible.case_0 EoCases.__str_is_compatible.case_1 EoCases.__str_is_compatible.case_2

theorem body_eo__24str_5fis_5fcompatible_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24str_5fis_5fcompatible s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__str_is_compatible x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  refine (?_ : ∀ (k : Nat) (a0 a1 : Term) (s : Store) (x_a0 : _) (x_a1 : _), s.budget ≤ k → s.Inv → s.remaining ≤ n →
      Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
      body_eo__24str_5fis_5fcompatible s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__str_is_compatible x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div) s.budget a0 a1 s x_a0 x_a1 le_rfl hinv hrem h_a0 h_a1
  intro k
  refine Nat.strong_induction_on k ?_
  intro k ihl a0 a1 s x_a0 x_a1 hk hinv hrem h_a0 h_a1
  unfold body_eo__24str_5fis_5fcompatible body_eo__24str_5fis_5fcompatible_loop
  step with step_eo__24str_5fis_5fcompatible_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 as ⟨r, s1, hinv1, hg1, hr⟩
  cases r with
  | Err e => simp only [WP.dspec_ok, WP.uncurry'_pair]; exact ⟨hinv1, hg1, trivial⟩
  | Ok nx =>
    cases nx with
    | Done value =>
      simp only [WP.dspec_ok, WP.uncurry'_pair]
      exact ⟨hinv1, hg1, hr⟩
    | Again next =>
      obtain ⟨hlt, u0, y0, u1, y1, hnext, hrep0, hrep1, heq⟩ := hr
      simp only
      have hlen : next.length = 2 := by simp [Array.length, hnext]
      step as ⟨b0, hb0⟩
      obtain rfl : b0 = u0 := by simp [hb0, hnext]
      step as ⟨b1, hb1⟩
      obtain rfl : b1 = u1 := by simp [hb1, hnext]
      have hrec := ihl s1.budget (by omega) b0 b1 s1 y0 y1 le_rfl hinv1 (hg1.rem hrem)  hrep0  hrep1
      unfold body_eo__24str_5fis_5fcompatible at hrec
      apply WP.dspec_mono hrec
      loop_close hg1 heq

theorem eo__24str_5fis_5fcompatible_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24str_5fis_5fcompatible.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24str_5fis_5fcompatible
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 1063#u32 _ [a0, a1] rfl
    (fun s1 => body_eo__24str_5fis_5fcompatible s1 a0 a1) (fun s' t => Represents.rep s' t (__str_is_compatible x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, y0, y1, hargs, hb0, hb1, hr⟩ := ProgramSem.of_1063 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_1063 ⟨a0, a1, x_a0, x_a1, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24str_5fis_5fcompatible_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24str_5fis_5fempty_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24str_5fis_5fempty s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__str_is_empty.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__str_is_empty.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24str_5fis_5fempty
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo_seq_2eempty.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__str_is_empty.case_0
  obtain hn_v1 := CtorSpec.eo_seq_2eempty.fields_ne_stuck hinv h_a0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__str_is_empty.case_0
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo_Seq.construct s e_v5 (by rw [he_v5]; exact empty_args) hinv h64 as ⟨v5, s1, hinv1, h_v5⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4
  pat_same v3 v5 with h_v3 h_v5 using hinv1 else hinv1 hG in EoCases.__str_is_empty.case_0
  store_step with Store.literal_boolean_spec s1 true hinv1 h64 as ⟨v6, s2, hinv2, h_v6⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5
  case_done hinv2 hG with h_v6 in EoCases.__str_is_empty.case_0 using hn_a0 hn_v1 hn_v3 hn_v4

theorem case_1_eo__24str_5fis_5fempty_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_1_eo__24str_5fis_5fempty s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__str_is_empty.case_1 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__str_is_empty.case_1 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24str_5fis_5fempty
  have hG := Store.Grows.refl s
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s _ _ rfl hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__str_is_empty.case_1
  store_step with Store.literal_boolean_spec s1 true hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__str_is_empty.case_1 using hn_a0

theorem case_2_eo__24str_5fis_5fempty_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_2_eo__24str_5fis_5fempty s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__str_is_empty.case_2 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__str_is_empty.case_2 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24str_5fis_5fempty
  have hG := Store.Grows.refl s
  store_step with Store.literal_boolean_spec s false hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  case_done hinv1 hG with h_v0 in EoCases.__str_is_empty.case_2 using hn_a0

/-- logos's `__str_is_empty` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24str_5fis_5fempty.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __str_is_empty x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__str_is_empty.case_0 x_a0, EoCases.__str_is_empty.case_1 x_a0, EoCases.__str_is_empty.case_2 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __str_is_empty
  unfold EoCases.__str_is_empty.case_0 EoCases.__str_is_empty.case_1 EoCases.__str_is_empty.case_2
  logos_eq

theorem body_eo__24str_5fis_5fempty_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24str_5fis_5fempty s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__str_is_empty x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24str_5fis_5fempty.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24str_5fis_5fempty
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24str_5fis_5fempty_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  case_step with case_1_eo__24str_5fis_5fempty_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 using hn_a0 hc0
  case_step with case_2_eo__24str_5fis_5fempty_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0 using hn_a0 hc0 hc1
  body_stuck hinv3 hG using hn_a0 hc0 hc1 hc2 in EoCases.__str_is_empty.case_0 EoCases.__str_is_empty.case_1 EoCases.__str_is_empty.case_2

theorem eo__24str_5fis_5fempty_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24str_5fis_5fempty.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24str_5fis_5fempty
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24str_5fis_5fempty s1 a0) (fun s' t => Represents.rep s' t (__str_is_empty x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24str_5fis_5fempty_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24str_5fis_5fmultiset_5fsubset_5fstrict_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24str_5fis_5fmultiset_5fsubset_5fstrict s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__str_is_multiset_subset_strict.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _), arr.val = [u0, u1, u2] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧
          EoCases.__str_is_multiset_subset_strict.case_0 x_a0 x_a1 x_a2 = some (__str_is_multiset_subset_strict y0 y1 y2)
      | core.result.Result.Ok none => EoCases.__str_is_multiset_subset_strict.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24str_5fis_5fmultiset_5fsubset_5fstrict
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__str_is_multiset_subset_strict.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__str_is_multiset_subset_strict.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__str_is_multiset_subset_strict.case_0
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo__40_40TypedList_2econs.construct s1 e_v7 (by rw [he_v7]; exact empty_args) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6
  step as ⟨e_v8, he_v8⟩
  store_step with Store.builtin_spec_list_erase n ih.eo__24eo_5fis_5flist_5fnil s2 e_v8 (by rw [he_v8]; rfl) h_v7 h_a1 h_v5 hinv2 h64 (hG.rem hrem) (by not_left_tac) as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__40_40TypedList_2econs.construct s3 e_v9 (by rw [he_v9]; exact empty_args) hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  step as ⟨e_v10, he_v10⟩
  store_step with Store.builtin_spec_list_erase n ih.eo__24eo_5fis_5flist_5fnil s4 e_v10 (by rw [he_v10]; rfl) h_v9 h_a1 h_v5 hinv4 h64 (hG.rem hrem) (by not_left_tac) as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  step as ⟨e_v11, he_v11⟩
  store_step with Store.builtin_spec_eq s5 e_v11 (by rw [he_v11]; rfl) h_a1 h_v10 hinv5 h64 as ⟨v11, s6, hinv6, h_v11⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
  have h_ite_v15 := (show if_0_eo__24str_5fis_5fmultiset_5fsubset_5fstrict s6 v11 v5 a2 ⦃ r s' => s'.Inv ∧ s6.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_0_eo__24str_5fis_5fmultiset_5fsubset_5fstrict
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s6
    rcases Store.boolean_value_term h_v11 with ⟨hx_12, hbv_12⟩ | ⟨hx_12, hbv_12⟩ | ⟨hx_12, hbv_12⟩
    · ite_branch hbv_12
      step as ⟨e_v12, he_v12⟩
      store_step with CtorSpec.eo__40_40TypedList_2econs.construct s6 e_v12 (by rw [he_v12]; exact empty_args) hinv6 h64 as ⟨v12, s7, hinv7, h_v12⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11
      store_step with Store.apply_rep s7 v12 v5 _ _ hinv7 h64 h_v12 h_v5 (by ns_tac) (by ns_tac) as ⟨v13, s8, hinv8, h_v13⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
      store_step with Store.apply_rep s8 v13 a2 _ _ hinv8 h64 h_v13 h_a2 (by ns_tac) (by ns_tac) as ⟨v14, s9, hinv9, h_v14⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13
      ite_done hinv9 hG with (eo_ite_true_rep _ hx_12 h_v14)
    · ite_branch hbv_12
      ite_done hinv6 hG with (eo_ite_false_rep _ hx_12 h_a2)
    · ite_branch hbv_12
      ite_stuck hinv6 hG with hx_12)
  store_step with h_ite_v15 as ⟨v15, s7, hinv7, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11
  case_again hinv7 hG with h_v2 h_v8 h_v15 in EoCases.__str_is_multiset_subset_strict.case_0 using hn_a0 hn_a1 hn_a2 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_1_eo__24str_5fis_5fmultiset_5fsubset_5fstrict_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_1_eo__24str_5fis_5fmultiset_5fsubset_5fstrict s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__str_is_multiset_subset_strict.case_1 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _), arr.val = [u0, u1, u2] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧
          EoCases.__str_is_multiset_subset_strict.case_1 x_a0 x_a1 x_a2 = some (__str_is_multiset_subset_strict y0 y1 y2)
      | core.result.Result.Ok none => EoCases.__str_is_multiset_subset_strict.case_1 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24str_5fis_5fmultiset_5fsubset_5fstrict
  have hG := Store.Grows.refl s
  store_step with ih.eo__24str_5fis_5fempty s a0 _ hinv h64 hrem h_a0 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2
  have h_ite_v12 := (show if_2_eo__24str_5fis_5fmultiset_5fsubset_5fstrict s1 v0 a1 a2 a0 ⦃ r s' => s'.Inv ∧ s1.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_2_eo__24str_5fis_5fmultiset_5fsubset_5fstrict
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s1
    rcases Store.boolean_value_term h_v0 with ⟨hx_1, hbv_1⟩ | ⟨hx_1, hbv_1⟩ | ⟨hx_1, hbv_1⟩
    · ite_branch hbv_1
      store_step with ih.eo__24str_5fis_5fmultiset_5fsubset_5fstrict_5fdone s1 a1 a2 _ _ hinv1 h64 (hG.rem hrem) h_a1 h_a2 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0
      ite_done hinv2 hG with (eo_ite_true_rep _ hx_1 h_v1)
    · ite_branch hbv_1
      step as ⟨e_v2, he_v2⟩
      store_step with CtorSpec.eo__40_40TypedList_2econs.construct s1 e_v2 (by rw [he_v2]; exact empty_args) hinv1 h64 as ⟨v2, s2, hinv2, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0
      step as ⟨e_v3, he_v3⟩
      store_step with Store.builtin_spec_list_erase n ih.eo__24eo_5fis_5flist_5fnil s2 e_v3 (by rw [he_v3]; rfl) h_v2 h_a1 h_a0 hinv2 h64 (hG.rem hrem) (by not_left_tac) as ⟨v3, s3, hinv3, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v2
      step as ⟨e_v4, he_v4⟩
      store_step with CtorSpec.eo__40_40TypedList_2econs.construct s3 e_v4 (by rw [he_v4]; exact empty_args) hinv3 h64 as ⟨v4, s4, hinv4, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v2 h_v3
      step as ⟨e_v5, he_v5⟩
      store_step with Store.builtin_spec_list_erase n ih.eo__24eo_5fis_5flist_5fnil s4 e_v5 (by rw [he_v5]; rfl) h_v4 h_a1 h_a0 hinv4 h64 (hG.rem hrem) (by not_left_tac) as ⟨v5, s5, hinv5, h_v5⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v2 h_v3 h_v4
      step as ⟨e_v6, he_v6⟩
      store_step with Store.builtin_spec_eq s5 e_v6 (by rw [he_v6]; rfl) h_a1 h_v5 hinv5 h64 as ⟨v6, s6, hinv6, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v2 h_v3 h_v4 h_v5
      have h_ite_v10 := (show if_1_eo__24str_5fis_5fmultiset_5fsubset_5fstrict s6 v6 a0 a2 ⦃ r s' => s'.Inv ∧ s6.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_1_eo__24str_5fis_5fmultiset_5fsubset_5fstrict
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s6
        rcases Store.boolean_value_term h_v6 with ⟨hx_7, hbv_7⟩ | ⟨hx_7, hbv_7⟩ | ⟨hx_7, hbv_7⟩
        · ite_branch hbv_7
          step as ⟨e_v7, he_v7⟩
          store_step with CtorSpec.eo__40_40TypedList_2econs.construct s6 e_v7 (by rw [he_v7]; exact empty_args) hinv6 h64 as ⟨v7, s7, hinv7, h_v7⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v2 h_v3 h_v4 h_v5 h_v6
          store_step with Store.apply_rep s7 v7 a0 _ _ hinv7 h64 h_v7 h_a0 (by ns_tac) (by ns_tac) as ⟨v8, s8, hinv8, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
          store_step with Store.apply_rep s8 v8 a2 _ _ hinv8 h64 h_v8 h_a2 (by ns_tac) (by ns_tac) as ⟨v9, s9, hinv9, h_v9⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
          ite_done hinv9 hG with (eo_ite_true_rep _ hx_7 h_v9)
        · ite_branch hbv_7
          ite_done hinv6 hG with (eo_ite_false_rep _ hx_7 h_a2)
        · ite_branch hbv_7
          ite_stuck hinv6 hG with hx_7)
      store_step with h_ite_v10 as ⟨v10, s7, hinv7, h_v10⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v2 h_v3 h_v4 h_v5 h_v6
      store_step with ih.eo__24str_5fis_5fmultiset_5fsubset_5fstrict_5fdone s7 v3 v10 _ _ hinv7 h64 (hG.rem hrem) h_v3 h_v10 as ⟨v11, s8, hinv8, h_v11⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v2 h_v3 h_v4 h_v5 h_v6 h_v10
      ite_done hinv8 hG with (eo_ite_false_rep _ hx_1 h_v11)
    · ite_branch hbv_1
      ite_stuck hinv1 hG with hx_1)
  store_step with h_ite_v12 as ⟨v12, s2, hinv2, h_v12⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0
  case_done hinv2 hG with h_v12 in EoCases.__str_is_multiset_subset_strict.case_1 using hn_a0 hn_a1 hn_a2

/-- logos's `__str_is_multiset_subset_strict` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24str_5fis_5fmultiset_5fsubset_5fstrict.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __str_is_multiset_subset_strict x_a0 x_a1 x_a2 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__str_is_multiset_subset_strict.case_0 x_a0 x_a1 x_a2, EoCases.__str_is_multiset_subset_strict.case_1 x_a0 x_a1 x_a2] HasStuck.stuck) := by
  conv => lhs; unfold __str_is_multiset_subset_strict
  unfold EoCases.__str_is_multiset_subset_strict.case_0 EoCases.__str_is_multiset_subset_strict.case_1
  logos_eq

theorem step_eo__24str_5fis_5fmultiset_5fsubset_5fstrict_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    step_eo__24str_5fis_5fmultiset_5fsubset_5fstrict s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (Next.Done t) => Represents.rep s' t (__str_is_multiset_subset_strict x_a0 x_a1 x_a2)
      | core.result.Result.Ok (Next.Again arr) =>
        s'.budget < s.budget ∧ ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _), arr.val = [u0, u1, u2] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧
          __str_is_multiset_subset_strict x_a0 x_a1 x_a2 = __str_is_multiset_subset_strict y0 y1 y2
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24str_5fis_5fmultiset_5fsubset_5fstrict.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold step_eo__24str_5fis_5fmultiset_5fsubset_5fstrict
  have hG := Store.Grows.refl s
  tick_step as ⟨s1, hinv1⟩ growing hG carrying h_a0 h_a1 h_a2
  stuck_check h_a0 : x_a0 as hn_a0 else hinv1 hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv1 hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv1 hG
  round_step with case_0_eo__24str_5fis_5fmultiset_5fsubset_5fstrict_spec n ih s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s2, hinv2, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 hbud using hn_a0 hn_a1 hn_a2
  round_step with case_1_eo__24str_5fis_5fmultiset_5fsubset_5fstrict_spec n ih s2 a0 a1 a2 x_a0 x_a1 x_a2 hinv2 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s3, hinv3, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 hbud using hn_a0 hn_a1 hn_a2 hc0
  round_stuck hinv3 hG using hn_a0 hn_a1 hn_a2 hc0 hc1 in EoCases.__str_is_multiset_subset_strict.case_0 EoCases.__str_is_multiset_subset_strict.case_1

theorem body_eo__24str_5fis_5fmultiset_5fsubset_5fstrict_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24str_5fis_5fmultiset_5fsubset_5fstrict s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__str_is_multiset_subset_strict x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  refine (?_ : ∀ (k : Nat) (a0 a1 a2 : Term) (s : Store) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.budget ≤ k → s.Inv → s.remaining ≤ n →
      Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
      body_eo__24str_5fis_5fmultiset_5fsubset_5fstrict s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__str_is_multiset_subset_strict x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div) s.budget a0 a1 a2 s x_a0 x_a1 x_a2 le_rfl hinv hrem h_a0 h_a1 h_a2
  intro k
  refine Nat.strong_induction_on k ?_
  intro k ihl a0 a1 a2 s x_a0 x_a1 x_a2 hk hinv hrem h_a0 h_a1 h_a2
  unfold body_eo__24str_5fis_5fmultiset_5fsubset_5fstrict body_eo__24str_5fis_5fmultiset_5fsubset_5fstrict_loop
  step with step_eo__24str_5fis_5fmultiset_5fsubset_5fstrict_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 as ⟨r, s1, hinv1, hg1, hr⟩
  cases r with
  | Err e => simp only [WP.dspec_ok, WP.uncurry'_pair]; exact ⟨hinv1, hg1, trivial⟩
  | Ok nx =>
    cases nx with
    | Done value =>
      simp only [WP.dspec_ok, WP.uncurry'_pair]
      exact ⟨hinv1, hg1, hr⟩
    | Again next =>
      obtain ⟨hlt, u0, y0, u1, y1, u2, y2, hnext, hrep0, hrep1, hrep2, heq⟩ := hr
      simp only
      have hlen : next.length = 3 := by simp [Array.length, hnext]
      step as ⟨b0, hb0⟩
      obtain rfl : b0 = u0 := by simp [hb0, hnext]
      step as ⟨b1, hb1⟩
      obtain rfl : b1 = u1 := by simp [hb1, hnext]
      step as ⟨b2, hb2⟩
      obtain rfl : b2 = u2 := by simp [hb2, hnext]
      have hrec := ihl s1.budget (by omega) b0 b1 b2 s1 y0 y1 y2 le_rfl hinv1 (hg1.rem hrem)  hrep0  hrep1  hrep2
      unfold body_eo__24str_5fis_5fmultiset_5fsubset_5fstrict at hrec
      apply WP.dspec_mono hrec
      loop_close hg1 heq

theorem eo__24str_5fis_5fmultiset_5fsubset_5fstrict_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24str_5fis_5fmultiset_5fsubset_5fstrict.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24str_5fis_5fmultiset_5fsubset_5fstrict
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 1065#u32 _ [a0, a1, a2] rfl
    (fun s1 => body_eo__24str_5fis_5fmultiset_5fsubset_5fstrict s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__str_is_multiset_subset_strict x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, b2, y0, y1, y2, hargs, hb0, hb1, hb2, hr⟩ := ProgramSem.of_1065 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      obtain rfl := Rep.functional hb2 (Represents.congr h_a2 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_1065 ⟨a0, a1, a2, x_a0, x_a1, x_a2, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, Rep.mono hpre h_a2, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24str_5fis_5fmultiset_5fsubset_5fstrict_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24str_5fis_5fmultiset_5fsubset_5fstrict_5fdone_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24str_5fis_5fmultiset_5fsubset_5fstrict_5fdone s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__str_is_multiset_subset_strict_done.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__str_is_multiset_subset_strict_done.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24str_5fis_5fmultiset_5fsubset_5fstrict_5fdone
  have hG := Store.Grows.refl s
  pat_unapply h_a1 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__str_is_multiset_subset_strict_done.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__str_is_multiset_subset_strict_done.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__40_40TypedList_2econs.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__str_is_multiset_subset_strict_done.case_0
  store_step with ih.eo__24str_5fvalue_5flen s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s2 1#u32 (1) (by scalar_tac) hinv2 h64 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  step as ⟨e_v9, he_v9⟩
  store_step with Store.builtin_spec_is_eq s3 e_v9 (by rw [he_v9]; rfl) h_v7 h_v8 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  store_step with ih.eo__24eo_5ftypeof s4 v5 _ hinv4 h64 (hG.rem hrem) h_v5 as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  store_step with ih.eo__24are_5fdistinct_5fterms_5flist_5frec s5 v5 a0 v10 _ _ _ hinv5 h64 (hG.rem hrem) h_v5 h_a0 h_v10 as ⟨v11, s6, hinv6, h_v11⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
  step as ⟨e_v12, he_v12⟩
  store_step with Store.builtin_spec_and s6 e_v12 (by rw [he_v12]; rfl) h_v9 h_v11 hinv6 h64 as ⟨v12, s7, hinv7, h_v12⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11
  have h_ite_v15 := (show if_0_eo__24str_5fis_5fmultiset_5fsubset_5fstrict_5fdone s7 v12 a0 v2 ⦃ r s' => s'.Inv ∧ s7.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_0_eo__24str_5fis_5fmultiset_5fsubset_5fstrict_5fdone
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s7
    rcases Store.boolean_value_term h_v12 with ⟨hx_13, hbv_13⟩ | ⟨hx_13, hbv_13⟩ | ⟨hx_13, hbv_13⟩
    · ite_branch hbv_13
      store_step with Store.literal_boolean_spec s7 true hinv7 h64 as ⟨v13, s8, hinv8, h_v13⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
      ite_done hinv8 hG with (eo_ite_true_rep _ hx_13 h_v13)
    · ite_branch hbv_13
      store_step with ih.eo__24str_5fis_5fmultiset_5fsubset_5fstrict_5fdone s7 a0 v2 _ _ hinv7 h64 (hG.rem hrem) h_a0 h_v2 as ⟨v14, s8, hinv8, h_v14⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
      ite_done hinv8 hG with (eo_ite_false_rep _ hx_13 h_v14)
    · ite_branch hbv_13
      ite_stuck hinv7 hG with hx_13)
  store_step with h_ite_v15 as ⟨v15, s8, hinv8, h_v15⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
  case_done hinv8 hG with h_v15 in EoCases.__str_is_multiset_subset_strict_done.case_0 using hn_a0 hn_a1 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_1_eo__24str_5fis_5fmultiset_5fsubset_5fstrict_5fdone_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_1_eo__24str_5fis_5fmultiset_5fsubset_5fstrict_5fdone s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__str_is_multiset_subset_strict_done.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__str_is_multiset_subset_strict_done.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24str_5fis_5fmultiset_5fsubset_5fstrict_5fdone
  have hG := Store.Grows.refl s
  store_step with Store.literal_boolean_spec s false hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  case_done hinv1 hG with h_v0 in EoCases.__str_is_multiset_subset_strict_done.case_1 using hn_a0 hn_a1

/-- logos's `__str_is_multiset_subset_strict_done` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24str_5fis_5fmultiset_5fsubset_5fstrict_5fdone.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __str_is_multiset_subset_strict_done x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__str_is_multiset_subset_strict_done.case_0 x_a0 x_a1, EoCases.__str_is_multiset_subset_strict_done.case_1 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __str_is_multiset_subset_strict_done
  unfold EoCases.__str_is_multiset_subset_strict_done.case_0 EoCases.__str_is_multiset_subset_strict_done.case_1
  logos_eq

theorem body_eo__24str_5fis_5fmultiset_5fsubset_5fstrict_5fdone_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24str_5fis_5fmultiset_5fsubset_5fstrict_5fdone s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__str_is_multiset_subset_strict_done x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24str_5fis_5fmultiset_5fsubset_5fstrict_5fdone.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24str_5fis_5fmultiset_5fsubset_5fstrict_5fdone
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24str_5fis_5fmultiset_5fsubset_5fstrict_5fdone_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  case_step with case_1_eo__24str_5fis_5fmultiset_5fsubset_5fstrict_5fdone_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1 hc0
  body_stuck hinv2 hG using hn_a0 hn_a1 hc0 hc1 in EoCases.__str_is_multiset_subset_strict_done.case_0 EoCases.__str_is_multiset_subset_strict_done.case_1

theorem eo__24str_5fis_5fmultiset_5fsubset_5fstrict_5fdone_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24str_5fis_5fmultiset_5fsubset_5fstrict_5fdone.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24str_5fis_5fmultiset_5fsubset_5fstrict_5fdone
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 1066#u32 _ [a0, a1] rfl
    (fun s1 => body_eo__24str_5fis_5fmultiset_5fsubset_5fstrict_5fdone s1 a0 a1) (fun s' t => Represents.rep s' t (__str_is_multiset_subset_strict_done x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, y0, y1, hargs, hb0, hb1, hr⟩ := ProgramSem.of_1066 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_1066 ⟨a0, a1, x_a0, x_a1, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24str_5fis_5fmultiset_5fsubset_5fstrict_5fdone_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

end pathos_compiled_checker
