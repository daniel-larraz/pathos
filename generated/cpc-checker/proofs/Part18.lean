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

theorem case_0_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct_lit Store.destruct_boolean_spec s a0 h_a0 hinv h64 as ⟨v1, x_v1, h_v1⟩ storing ⟨s1, hinv1⟩ growing hG carrying h_a0 in EoCases.__eo_typeof.case_0
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__24emb_5fBool.construct s1 e_v2 (by rw [he_v2]; exact empty_args) hinv1 h64 as ⟨v2, s2, hinv2, h_v2⟩ growing hG carrying h_a0 h_v1
  case_done hinv2 hG with h_v2 in EoCases.__eo_typeof.case_0 using hn_a0

theorem case_1_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_1_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_1 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_1 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct_lit Store.destruct_numeral_spec s a0 h_a0 hinv h64 as ⟨v1, x_v1, h_v1⟩ storing ⟨s1, hinv1⟩ growing hG carrying h_a0 in EoCases.__eo_typeof.case_1
  step as ⟨e_v2, he_v2⟩
  store_step with Store.construct_numeral_spec s1 e_v2 (by rw [he_v2]; rfl) h_v1 hinv1 h64 as ⟨v2, s2, hinv2, h_v2⟩ growing hG carrying h_a0 h_v1
  store_step with ih.eo__24eo_5flit_5ftype_5fNumeral s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v3, s3, hinv3, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  case_done hinv3 hG with h_v3 in EoCases.__eo_typeof.case_1 using hn_a0

theorem case_2_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_2_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_2 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_2 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct_lit Store.destruct_rational_spec s a0 h_a0 hinv h64 as ⟨v1, x_v1, h_v1⟩ storing ⟨s1, hinv1⟩ growing hG carrying h_a0 in EoCases.__eo_typeof.case_2
  step as ⟨e_v2, he_v2⟩
  store_step with Store.construct_rational_spec s1 e_v2 (by rw [he_v2]; rfl) h_v1 hinv1 h64 as ⟨v2, s2, hinv2, h_v2⟩ growing hG carrying h_a0 h_v1
  store_step with ih.eo__24eo_5flit_5ftype_5fRational s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v3, s3, hinv3, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  case_done hinv3 hG with h_v3 in EoCases.__eo_typeof.case_2 using hn_a0

theorem case_3_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_3_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_3 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_3 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_3_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct_lit Store.destruct_string_spec s a0 h_a0 hinv h64 as ⟨v1, x_v1, h_v1⟩ storing ⟨s1, hinv1⟩ growing hG carrying h_a0 in EoCases.__eo_typeof.case_3
  step as ⟨e_v2, he_v2⟩
  store_step with Store.construct_string_spec s1 e_v2 (by rw [he_v2]; rfl) h_v1 hinv1 h64 as ⟨v2, s2, hinv2, h_v2⟩ growing hG carrying h_a0 h_v1
  store_step with ih.eo__24eo_5flit_5ftype_5fString s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v3, s3, hinv3, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  case_done hinv3 hG with h_v3 in EoCases.__eo_typeof.case_3 using hn_a0

theorem case_4_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_4_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_4 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_4 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_4_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct_lit2 Store.destruct_binary_spec s a0 h_a0 hinv h64 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ storing ⟨s1, hinv1⟩ growing hG carrying h_a0 in EoCases.__eo_typeof.case_4
  step as ⟨e_v3, he_v3⟩
  store_step with Store.construct_binary_spec s1 e_v3 (by rw [he_v3]; rfl) h_v1 h_v2 (Store.rep_binary_okBv h_a0) hinv1 h64 as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24eo_5flit_5ftype_5fBinary s2 v3 _ hinv2 h64 (hG.rem hrem) h_v3 as ⟨v4, s3, hinv3, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  case_done hinv3 hG with h_v4 in EoCases.__eo_typeof.case_4 using hn_a0

theorem case_5_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_5_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_5 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_5 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_5_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fVar.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__eo_typeof.case_5
  obtain ⟨hn_v1, hn_v2⟩ := CtorSpec.eo__24emb_5fVar.fields_ne_stuck hinv h_a0
  pat_destruct_lit Store.destruct_string_spec s v1 h_v1 hinv h64 as ⟨v4, x_v4, h_v4⟩ storing ⟨s1, hinv1⟩ growing hG carrying h_a0 h_v1 h_v2 in EoCases.__eo_typeof.case_5
  case_done hinv1 hG with h_v2 in EoCases.__eo_typeof.case_5 using hn_a0 hn_v1 hn_v2

theorem case_6_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_6_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_6 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_6 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_6_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fDatatypeType.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__eo_typeof.case_6
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__24emb_5fType.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  case_done hinv1 hG with h_v3 in EoCases.__eo_typeof.case_6 using hn_a0

theorem case_7_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_7_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_7 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_7 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_7_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fDtCons.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ ⟨v3, x_v3, h_v3⟩ else hinv hG in EoCases.__eo_typeof.case_7
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo__24emb_5fDatatypeType.construct s e_v4 (by rw [he_v4]; rfl) h_v1 h_v2 hinv h64 as ⟨v4, s1, hinv1, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24eo_5fdd_5fresolve s1 v1 v2 _ _ hinv1 h64 (hG.rem hrem) h_v1 h_v2 as ⟨v5, s2, hinv2, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  store_step with ih.eo__24eo_5ftypeof_5fdt_5fcons_5frec s2 v4 v5 v3 _ _ _ hinv2 h64 (hG.rem hrem) h_v4 h_v5 h_v3 as ⟨v6, s3, hinv3, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  case_done hinv3 hG with h_v6 in EoCases.__eo_typeof.case_7 using hn_a0

theorem case_8_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_8_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_8 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_8 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_8_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fDtSel.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ ⟨v3, x_v3, h_v3⟩ ⟨v4, x_v4, h_v4⟩ else hinv hG in EoCases.__eo_typeof.case_8
  store_step with ih.eo__24eo_5fdd_5fresolve s v1 v2 _ _ hinv h64 hrem h_v1 h_v2 as ⟨v5, s1, hinv1, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  store_step with ih.eo__24eo_5ftypeof_5fdt_5fsel_5freturn s1 v5 v3 v4 _ _ _ hinv1 h64 (hG.rem hrem) h_v5 h_v3 h_v4 as ⟨v6, s2, hinv2, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo__24emb_5fDatatypeType.construct s2 e_v7 (by rw [he_v7]; rfl) h_v1 h_v2 hinv2 h64 as ⟨v7, s3, hinv3, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__24emb_5fFunType.construct s3 e_v8 (by rw [he_v8]; exact empty_args) hinv3 h64 as ⟨v8, s4, hinv4, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  store_step with Store.apply_mk_rep s4 v8 v7 _ _ hinv4 h64 h_v8 h_v7 as ⟨v9, s5, hinv5, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
  store_step with Store.apply_mk_rep s5 v9 v6 _ _ hinv5 h64 h_v9 h_v6 as ⟨v10, s6, hinv6, h_v10⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  case_done hinv6 hG with h_v10 in EoCases.__eo_typeof.case_8 using hn_a0

theorem case_9_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_9_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_9 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_9 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_9_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fUSort.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_typeof.case_9
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__24emb_5fType.construct s e_v2 (by rw [he_v2]; exact empty_args) hinv h64 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying h_a0 h_v1
  case_done hinv1 hG with h_v2 in EoCases.__eo_typeof.case_9 using hn_a0

theorem case_10_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_10_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_10 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_10 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_10_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fUConst.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__eo_typeof.case_10
  case_done hinv hG with h_v2 in EoCases.__eo_typeof.case_10 using hn_a0

theorem case_11_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_11_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_11 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_11 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_11_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fType.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_11
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24emb_5fType.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__eo_typeof.case_11 using hn_a0

theorem case_12_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_12_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_12 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_12 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_12_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_12
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_12
  pat_is_node h_v4 : x_v4 is Eo.Term.FunType by Embed.inv_Term_FunType else hinv hG in EoCases.__eo_typeof.case_12
  store_step with ih.eo__24eo_5ftypeof s v5 _ hinv h64 hrem h_v5 as ⟨v7, s1, hinv1, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  store_step with ih.eo__24eo_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v8, s2, hinv2, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7
  store_step with ih.eo__24eo_5ftypeof_5ffun_5ftype s2 v7 v8 _ _ hinv2 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s3, hinv3, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8
  case_done hinv3 hG with h_v9 in EoCases.__eo_typeof.case_12 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_13_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_13_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_13 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_13 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_13_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fBool.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_13
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24emb_5fType.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__eo_typeof.case_13 using hn_a0

theorem case_14_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_14_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_14 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_14 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_14_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24eo_5fList.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_14
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24emb_5fType.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__eo_typeof.case_14 using hn_a0

theorem case_15_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_15_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_15 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_15 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_15_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_15
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24eo_5fList.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__eo_typeof.case_15 using hn_a0

theorem case_16_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_16_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_16 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_16 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_16_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_16
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_16
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo__24eo_5fList.construct s1 e_v4 (by rw [he_v4]; exact empty_args) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24eo_5fList.construct s2 e_v5 (by rw [he_v5]; exact empty_args) hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__24emb_5fFunType.construct s3 e_v6 (by rw [he_v6]; exact empty_args) hinv3 h64 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with Store.apply_rep s4 v6 v5 _ _ hinv4 h64 h_v6 h_v5 (by ns_tac) (by ns_tac) as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  store_step with Store.apply_rep s5 v7 v4 _ _ hinv5 h64 h_v7 h_v4 (by ns_tac) (by ns_tac) as ⟨v8, s6, hinv6, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  case_done hinv6 hG with h_v8 in EoCases.__eo_typeof.case_16 using hn_a0 hn_v1 hn_v2

theorem case_17_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_17_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_17 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_17 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_17_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_Int.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_17
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24emb_5fType.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__eo_typeof.case_17 using hn_a0

theorem case_18_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_18_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_18 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_18 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_18_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_Real.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_18
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24emb_5fType.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__eo_typeof.case_18 using hn_a0

theorem case_19_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_19_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_19 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_19 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_19_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_19
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_BitVec.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_19
  store_step with ih.eo__24eo_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24eo_5ftypeof_5fBitVec s2 v4 _ hinv2 h64 (hG.rem hrem) h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_typeof.case_19 using hn_a0 hn_v1 hn_v2

theorem case_20_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_20_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_20 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_20 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_20_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_Char.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_20
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24emb_5fType.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__eo_typeof.case_20 using hn_a0

theorem case_21_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_21_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_21 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_21 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_21_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_21
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_Seq.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_21
  store_step with ih.eo__24eo_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24eo_5ftypeof_5fSeq s2 v4 _ hinv2 h64 (hG.rem hrem) h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_typeof.case_21 using hn_a0 hn_v1 hn_v2

theorem case_22_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_22_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_22 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_22 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_22_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_22
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_22
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__40_40Pair.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_22
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5f_40_40Pair s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_22 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_23_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_23_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_23 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_23 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_23_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_23
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_23
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__40_40pair.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_23
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5f_40_40pair s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_23 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_24_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_24_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_24 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_24 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_24_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_24
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__40_40TypedList.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_24
  store_step with ih.eo__24eo_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24eo_5ftypeof_5fSeq s2 v4 _ hinv2 h64 (hG.rem hrem) h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_typeof.case_24 using hn_a0 hn_v1 hn_v2

theorem case_25_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_25_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_25 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_25 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_25_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_25
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__40_40TypedList_2enil.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_25
  store_step with ih.eo__24eo_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24eo_5ftypeof_5f_40_40TypedList_2enil s2 v4 v2 _ _ hinv2 h64 (hG.rem hrem) h_v4 h_v2 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_typeof.case_25 using hn_a0 hn_v1 hn_v2

theorem case_26_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_26_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_26 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_26 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_26_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_26
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_26
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__40_40TypedList_2econs.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_26
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5f_40_40TypedList_2econs s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_26 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_27_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_27_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_27 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_27 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_27_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_27
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_27
  pat_unapply h_v4 as ⟨v7, v8, x_v7, x_v8, h_v7, h_v8, hn_v7, hn_v8⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_27
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_ite.construct s e_v9 (by rw [he_v9]; exact empty_args) hinv h64 as ⟨v9, s1, hinv1, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8
  pat_same v7 v9 with h_v7 h_v9 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_27
  store_step with ih.eo__24eo_5ftypeof s1 v8 _ hinv1 h64 (hG.rem hrem) h_v8 as ⟨v10, s2, hinv2, h_v10⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9
  store_step with ih.eo__24eo_5ftypeof s2 v5 _ hinv2 h64 (hG.rem hrem) h_v5 as ⟨v11, s3, hinv3, h_v11⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10
  store_step with ih.eo__24eo_5ftypeof s3 v2 _ hinv3 h64 (hG.rem hrem) h_v2 as ⟨v12, s4, hinv4, h_v12⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11
  store_step with ih.eo__24eo_5ftypeof_5fite s4 v10 v11 v12 _ _ _ hinv4 h64 (hG.rem hrem) h_v10 h_v11 h_v12 as ⟨v13, s5, hinv5, h_v13⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
  case_done hinv5 hG with h_v13 in EoCases.__eo_typeof.case_27 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5 hn_v7 hn_v8

theorem case_28_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_28_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_28 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_28 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_28_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_28
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_not.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_28
  store_step with ih.eo__24eo_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24eo_5ftypeof_5fnot s2 v4 _ hinv2 h64 (hG.rem hrem) h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_typeof.case_28 using hn_a0 hn_v1 hn_v2

theorem case_29_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_29_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_29 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_29 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_29_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_29
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_29
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_or.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_29
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5for s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_29 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_30_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_30_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_30 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_30 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_30_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_30
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_30
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_and.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_30
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5for s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_30 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_31_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_31_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_31 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_31 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_31_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_31
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_31
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__3d_3e.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_31
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5for s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_31 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_32_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_32_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_32 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_32 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_32_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_32
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_32
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_xor.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_32
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5for s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_32 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_33_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_33_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_33 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_33 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_33_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_33
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_33
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__3d.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_33
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5f_3d s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_33 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_34_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_34_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_34 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_34 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_34_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_34
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_34
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_lambda.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_34
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5flambda s3 v7 v5 v8 _ _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v5 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_34 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_35_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_35_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_35 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_35 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_35_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_35
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_distinct.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_35
  store_step with ih.eo__24eo_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24eo_5ftypeof_5fdistinct s2 v4 _ hinv2 h64 (hG.rem hrem) h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_typeof.case_35 using hn_a0 hn_v1 hn_v2

theorem case_36_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_36_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_36 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_36 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_36_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_36
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__40purify.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_36
  store_step with ih.eo__24eo_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24eo_5ftypeof_5f_40purify s2 v4 _ hinv2 h64 (hG.rem hrem) h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_typeof.case_36 using hn_a0 hn_v1 hn_v2

theorem case_37_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_37_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_37 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_37 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_37_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_37
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_37
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__2b.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_37
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5f_2b s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_37 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_38_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_38_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_38 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_38 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_38_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_38
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_38
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__2d.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_38
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5f_2b s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_38 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_39_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_39_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_39 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_39 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_39_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_39
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_39
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__2a.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_39
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5f_2b s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_39 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_40_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_40_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_40 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_40 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_40_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_40
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_40
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__3c.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_40
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5f_3c s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_40 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_41_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_41_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_41 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_41 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_41_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_41
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_41
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__3c_3d.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_41
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5f_3c s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_41 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_42_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_42_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_42 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_42 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_42_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_42
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_42
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__3e.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_42
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5f_3c s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_42 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_43_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_43_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_43 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_43 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_43_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_43
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_43
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__3e_3d.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_43
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5f_3c s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_43 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_44_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_44_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_44 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_44 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_44_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_44
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_to_5freal.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_44
  store_step with ih.eo__24eo_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24eo_5ftypeof_5fto_5freal s2 v4 _ hinv2 h64 (hG.rem hrem) h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_typeof.case_44 using hn_a0 hn_v1 hn_v2

theorem case_45_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_45_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_45 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_45 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_45_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_45
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_to_5fint.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_45
  store_step with ih.eo__24eo_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24eo_5ftypeof_5fto_5fint s2 v4 _ hinv2 h64 (hG.rem hrem) h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_typeof.case_45 using hn_a0 hn_v1 hn_v2

theorem case_46_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_46_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_46 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_46 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_46_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_46
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_is_5fint.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_46
  store_step with ih.eo__24eo_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24eo_5ftypeof_5fis_5fint s2 v4 _ hinv2 h64 (hG.rem hrem) h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_typeof.case_46 using hn_a0 hn_v1 hn_v2

theorem case_47_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_47_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_47 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_47 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_47_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_47
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_abs.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_47
  store_step with ih.eo__24eo_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24eo_5ftypeof_5fabs s2 v4 _ hinv2 h64 (hG.rem hrem) h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_typeof.case_47 using hn_a0 hn_v1 hn_v2

theorem case_48_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_48_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_48 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_48 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_48_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_48
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__24eoo_5f_2d_2e2.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_48
  store_step with ih.eo__24eo_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24eo_5ftypeof_5fabs s2 v4 _ hinv2 h64 (hG.rem hrem) h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_typeof.case_48 using hn_a0 hn_v1 hn_v2

theorem case_49_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_49_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_49 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_49 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_49_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_49
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_49
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_div.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_49
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5fdiv s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_49 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_50_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_50_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_50 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_50 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_50_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_50
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_50
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_mod.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_50
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5fdiv s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_50 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_51_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_51_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_51 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_51 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_51_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_51
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_51
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_divisible.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_51
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5fdivisible s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_51 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_52_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_52_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_52 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_52 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_52_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_52
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_int_2epow2.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_52
  store_step with ih.eo__24eo_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24eo_5ftypeof_5fint_2epow2 s2 v4 _ hinv2 h64 (hG.rem hrem) h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_typeof.case_52 using hn_a0 hn_v1 hn_v2

theorem case_53_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_53_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_53 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_53 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_53_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_53
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_int_2elog2.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_53
  store_step with ih.eo__24eo_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24eo_5ftypeof_5fint_2epow2 s2 v4 _ hinv2 h64 (hG.rem hrem) h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_typeof.case_53 using hn_a0 hn_v1 hn_v2

theorem case_54_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_54_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_54 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_54 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_54_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_54
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_int_2eispow2.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_54
  store_step with ih.eo__24eo_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24eo_5ftypeof_5fint_2eispow2 s2 v4 _ hinv2 h64 (hG.rem hrem) h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_typeof.case_54 using hn_a0 hn_v1 hn_v2

theorem case_55_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_55_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_55 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_55 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_55_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_55
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_55
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_div_5ftotal.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_55
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5fdiv s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_55 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_56_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_56_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_56 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_56 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_56_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_56
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_56
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_mod_5ftotal.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_56
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5fdiv s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_56 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_57_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_57_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_57 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_57 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_57_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_57
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__40int_5fdiv_5fby_5fzero.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_57
  store_step with ih.eo__24eo_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24eo_5ftypeof_5fint_2epow2 s2 v4 _ hinv2 h64 (hG.rem hrem) h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_typeof.case_57 using hn_a0 hn_v1 hn_v2

theorem case_58_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_58_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_58 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_58 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_58_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_58
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__40mod_5fby_5fzero.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_58
  store_step with ih.eo__24eo_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24eo_5ftypeof_5fint_2epow2 s2 v4 _ hinv2 h64 (hG.rem hrem) h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_typeof.case_58 using hn_a0 hn_v1 hn_v2

theorem case_59_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_59_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_59 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_59 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_59_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_59
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_59
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_Array.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_59
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5f_40_40Pair s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_59 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_60_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_60_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_60 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_60 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_60_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_60
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_60
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_select.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_60
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5fselect s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_60 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_61_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_61_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_61 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_61 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_61_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_61
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_61
  pat_unapply h_v4 as ⟨v7, v8, x_v7, x_v8, h_v7, h_v8, hn_v7, hn_v8⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_61
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_store.construct s e_v9 (by rw [he_v9]; exact empty_args) hinv h64 as ⟨v9, s1, hinv1, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8
  pat_same v7 v9 with h_v7 h_v9 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_61
  store_step with ih.eo__24eo_5ftypeof s1 v8 _ hinv1 h64 (hG.rem hrem) h_v8 as ⟨v10, s2, hinv2, h_v10⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9
  store_step with ih.eo__24eo_5ftypeof s2 v5 _ hinv2 h64 (hG.rem hrem) h_v5 as ⟨v11, s3, hinv3, h_v11⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10
  store_step with ih.eo__24eo_5ftypeof s3 v2 _ hinv3 h64 (hG.rem hrem) h_v2 as ⟨v12, s4, hinv4, h_v12⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11
  store_step with ih.eo__24eo_5ftypeof_5fstore s4 v10 v11 v12 _ _ _ hinv4 h64 (hG.rem hrem) h_v10 h_v11 h_v12 as ⟨v13, s5, hinv5, h_v13⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
  case_done hinv5 hG with h_v13 in EoCases.__eo_typeof.case_61 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5 hn_v7 hn_v8

theorem case_62_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_62_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_62 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_62 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_62_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_62
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_62
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__40array_5fdeq_5fdiff.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_62
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5f_40array_5fdeq_5fdiff s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_62 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_63_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_63_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_63 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_63 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_63_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_63
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__40bvsize.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_63
  store_step with ih.eo__24eo_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24eo_5ftypeof_5f_40bvsize s2 v4 _ hinv2 h64 (hG.rem hrem) h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_typeof.case_63 using hn_a0 hn_v1 hn_v2

theorem case_64_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_64_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_64 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_64 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_64_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_64
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_64
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_concat.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_64
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5fconcat s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_64 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_65_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_65_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_65 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_65 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_65_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_65
  pat_destruct CtorSpec.eo_extract.destruct h_v1 as ⟨v4, x_v4, h_v4⟩ ⟨v5, x_v5, h_v5⟩ else hinv hG in EoCases.__eo_typeof.case_65
  obtain ⟨hn_v4, hn_v5⟩ := CtorSpec.eo_extract.fields_ne_stuck hinv h_v1
  store_step with ih.eo__24eo_5ftypeof s v4 _ hinv h64 hrem h_v4 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5fextract s3 v6 v4 v7 v5 v8 _ _ _ _ _ hinv3 h64 (hG.rem hrem) h_v6 h_v4 h_v7 h_v5 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_65 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_66_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_66_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_66 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_66 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_66_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_66
  pat_destruct CtorSpec.eo_repeat.destruct h_v1 as ⟨v4, x_v4, h_v4⟩ else hinv hG in EoCases.__eo_typeof.case_66
  obtain hn_v4 := CtorSpec.eo_repeat.fields_ne_stuck hinv h_v1
  store_step with ih.eo__24eo_5ftypeof s v4 _ hinv h64 hrem h_v4 as ⟨v5, s1, hinv1, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4
  store_step with ih.eo__24eo_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v6, s2, hinv2, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  store_step with ih.eo__24eo_5ftypeof_5frepeat s2 v5 v4 v6 _ _ _ hinv2 h64 (hG.rem hrem) h_v5 h_v4 h_v6 as ⟨v7, s3, hinv3, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  case_done hinv3 hG with h_v7 in EoCases.__eo_typeof.case_66 using hn_a0 hn_v1 hn_v2 hn_v4

theorem case_67_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_67_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_67 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_67 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_67_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_67
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_bvnot.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_67
  store_step with ih.eo__24eo_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24eo_5ftypeof_5fbvnot s2 v4 _ hinv2 h64 (hG.rem hrem) h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_typeof.case_67 using hn_a0 hn_v1 hn_v2

theorem case_68_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_68_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_68 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_68 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_68_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_68
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_68
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_bvand.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_68
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5fbvand s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_68 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_69_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_69_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_69 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_69 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_69_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_69
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_69
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_bvor.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_69
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5fbvand s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_69 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_70_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_70_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_70 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_70 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_70_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_70
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_70
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_bvnand.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_70
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5fbvand s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_70 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_71_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_71_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_71 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_71 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_71_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_71
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_71
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_bvnor.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_71
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5fbvand s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_71 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_72_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_72_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_72 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_72 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_72_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_72
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_72
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_bvxor.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_72
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5fbvand s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_72 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_73_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_73_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_73 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_73 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_73_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_73
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_73
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_bvxnor.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_73
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5fbvand s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_73 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_74_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_74_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_74 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_74 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_74_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_74
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_74
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_bvcomp.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_74
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5fbvcomp s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_74 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_75_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_75_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_75 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_75 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_75_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_75
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_bvneg.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_75
  store_step with ih.eo__24eo_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24eo_5ftypeof_5fbvnot s2 v4 _ hinv2 h64 (hG.rem hrem) h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_typeof.case_75 using hn_a0 hn_v1 hn_v2

theorem case_76_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_76_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_76 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_76 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_76_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_76
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_76
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_bvadd.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_76
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5fbvand s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_76 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_77_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_77_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_77 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_77 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_77_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_77
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_77
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_bvmul.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_77
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5fbvand s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_77 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_78_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_78_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_78 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_78 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_78_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_78
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_78
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_bvudiv.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_78
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5fbvand s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_78 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_79_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_79_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_79 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_79 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_79_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_79
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_79
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_bvurem.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_79
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5fbvand s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_79 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_80_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_80_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_80 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_80 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_80_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_80
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_80
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_bvsub.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_80
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5fbvand s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_80 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_81_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_81_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_81 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_81 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_81_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_81
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_81
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_bvsdiv.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_81
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5fbvand s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_81 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_82_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_82_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_82 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_82 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_82_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_82
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_82
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_bvsrem.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_82
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5fbvand s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_82 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_83_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_83_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_83 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_83 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_83_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_83
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_83
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_bvsmod.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_83
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5fbvand s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_83 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_84_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_84_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_84 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_84 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_84_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_84
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_84
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_bvult.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_84
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5fbvult s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_84 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_85_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_85_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_85 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_85 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_85_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_85
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_85
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_bvule.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_85
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5fbvult s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_85 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_86_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_86_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_86 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_86 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_86_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_86
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_86
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_bvugt.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_86
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5fbvult s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_86 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_87_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_87_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_87 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_87 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_87_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_87
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_87
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_bvuge.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_87
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5fbvult s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_87 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_88_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_88_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_88 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_88 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_88_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_88
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_88
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_bvslt.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_88
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5fbvult s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_88 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_89_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_89_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_89 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_89 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_89_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_89
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_89
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_bvsle.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_89
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5fbvult s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_89 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_90_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_90_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_90 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_90 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_90_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_90
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_90
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_bvsgt.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_90
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5fbvult s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_90 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_91_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_91_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_91 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_91 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_91_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_91
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_91
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_bvsge.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_91
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5fbvult s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_91 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_92_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_92_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_92 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_92 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_92_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_92
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_92
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_bvshl.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_92
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5fbvand s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_92 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_93_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_93_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_93 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_93 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_93_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_93
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_93
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_bvlshr.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_93
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5fbvand s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_93 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_94_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_94_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_94 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_94 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_94_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_94
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_94
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_bvashr.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_94
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5fbvand s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_94 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_95_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_95_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_95 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_95 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_95_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_95
  pat_destruct CtorSpec.eo_zero_5fextend.destruct h_v1 as ⟨v4, x_v4, h_v4⟩ else hinv hG in EoCases.__eo_typeof.case_95
  obtain hn_v4 := CtorSpec.eo_zero_5fextend.fields_ne_stuck hinv h_v1
  store_step with ih.eo__24eo_5ftypeof s v4 _ hinv h64 hrem h_v4 as ⟨v5, s1, hinv1, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4
  store_step with ih.eo__24eo_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v6, s2, hinv2, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  store_step with ih.eo__24eo_5ftypeof_5fzero_5fextend s2 v5 v4 v6 _ _ _ hinv2 h64 (hG.rem hrem) h_v5 h_v4 h_v6 as ⟨v7, s3, hinv3, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  case_done hinv3 hG with h_v7 in EoCases.__eo_typeof.case_95 using hn_a0 hn_v1 hn_v2 hn_v4

theorem case_96_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_96_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_96 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_96 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_96_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_96
  pat_destruct CtorSpec.eo_sign_5fextend.destruct h_v1 as ⟨v4, x_v4, h_v4⟩ else hinv hG in EoCases.__eo_typeof.case_96
  obtain hn_v4 := CtorSpec.eo_sign_5fextend.fields_ne_stuck hinv h_v1
  store_step with ih.eo__24eo_5ftypeof s v4 _ hinv h64 hrem h_v4 as ⟨v5, s1, hinv1, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4
  store_step with ih.eo__24eo_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v6, s2, hinv2, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  store_step with ih.eo__24eo_5ftypeof_5fzero_5fextend s2 v5 v4 v6 _ _ _ hinv2 h64 (hG.rem hrem) h_v5 h_v4 h_v6 as ⟨v7, s3, hinv3, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  case_done hinv3 hG with h_v7 in EoCases.__eo_typeof.case_96 using hn_a0 hn_v1 hn_v2 hn_v4

theorem case_97_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_97_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_97 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_97 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_97_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_97
  pat_destruct CtorSpec.eo_rotate_5fleft.destruct h_v1 as ⟨v4, x_v4, h_v4⟩ else hinv hG in EoCases.__eo_typeof.case_97
  obtain hn_v4 := CtorSpec.eo_rotate_5fleft.fields_ne_stuck hinv h_v1
  store_step with ih.eo__24eo_5ftypeof s v4 _ hinv h64 hrem h_v4 as ⟨v5, s1, hinv1, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4
  store_step with ih.eo__24eo_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v6, s2, hinv2, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  store_step with ih.eo__24eo_5ftypeof_5frotate_5fleft s2 v5 v4 v6 _ _ _ hinv2 h64 (hG.rem hrem) h_v5 h_v4 h_v6 as ⟨v7, s3, hinv3, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  case_done hinv3 hG with h_v7 in EoCases.__eo_typeof.case_97 using hn_a0 hn_v1 hn_v2 hn_v4

theorem case_98_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_98_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_98 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_98 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_98_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_98
  pat_destruct CtorSpec.eo_rotate_5fright.destruct h_v1 as ⟨v4, x_v4, h_v4⟩ else hinv hG in EoCases.__eo_typeof.case_98
  obtain hn_v4 := CtorSpec.eo_rotate_5fright.fields_ne_stuck hinv h_v1
  store_step with ih.eo__24eo_5ftypeof s v4 _ hinv h64 hrem h_v4 as ⟨v5, s1, hinv1, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4
  store_step with ih.eo__24eo_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v6, s2, hinv2, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  store_step with ih.eo__24eo_5ftypeof_5frotate_5fleft s2 v5 v4 v6 _ _ _ hinv2 h64 (hG.rem hrem) h_v5 h_v4 h_v6 as ⟨v7, s3, hinv3, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  case_done hinv3 hG with h_v7 in EoCases.__eo_typeof.case_98 using hn_a0 hn_v1 hn_v2 hn_v4

theorem case_99_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_99_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_99 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_99 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_99_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_99
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_99
  pat_unapply h_v4 as ⟨v7, v8, x_v7, x_v8, h_v7, h_v8, hn_v7, hn_v8⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_99
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_bvite.construct s e_v9 (by rw [he_v9]; exact empty_args) hinv h64 as ⟨v9, s1, hinv1, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8
  pat_same v7 v9 with h_v7 h_v9 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_99
  store_step with ih.eo__24eo_5ftypeof s1 v8 _ hinv1 h64 (hG.rem hrem) h_v8 as ⟨v10, s2, hinv2, h_v10⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9
  store_step with ih.eo__24eo_5ftypeof s2 v5 _ hinv2 h64 (hG.rem hrem) h_v5 as ⟨v11, s3, hinv3, h_v11⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10
  store_step with ih.eo__24eo_5ftypeof s3 v2 _ hinv3 h64 (hG.rem hrem) h_v2 as ⟨v12, s4, hinv4, h_v12⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11
  store_step with ih.eo__24eo_5ftypeof_5fbvite s4 v10 v11 v12 _ _ _ hinv4 h64 (hG.rem hrem) h_v10 h_v11 h_v12 as ⟨v13, s5, hinv5, h_v13⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
  case_done hinv5 hG with h_v13 in EoCases.__eo_typeof.case_99 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5 hn_v7 hn_v8

theorem case_100_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_100_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_100 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_100 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_100_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_100
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_100
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_bvuaddo.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_100
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5fbvult s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_100 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_101_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_101_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_101 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_101 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_101_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_101
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_bvnego.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_101
  store_step with ih.eo__24eo_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24eo_5ftypeof_5fbvnego s2 v4 _ hinv2 h64 (hG.rem hrem) h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_typeof.case_101 using hn_a0 hn_v1 hn_v2

theorem case_102_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_102_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_102 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_102 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_102_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_102
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_102
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_bvsaddo.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_102
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5fbvult s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_102 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_103_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_103_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_103 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_103 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_103_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_103
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_103
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_bvumulo.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_103
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5fbvult s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_103 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_104_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_104_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_104 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_104 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_104_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_104
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_104
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_bvsmulo.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_104
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5fbvult s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_104 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_105_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_105_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_105 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_105 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_105_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_105
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_105
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_bvusubo.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_105
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5fbvult s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_105 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_106_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_106_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_106 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_106 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_106_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_106
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_106
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_bvssubo.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_106
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5fbvult s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_106 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_107_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_107_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_107 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_107 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_107_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_107
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_107
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_bvsdivo.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_107
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5fbvult s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_107 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_108_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_108_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_108 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_108 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_108_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_108
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_108
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_bvultbv.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_108
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5fbvcomp s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_108 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_109_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_109_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_109 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_109 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_109_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_109
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_109
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_bvsltbv.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_109
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5fbvcomp s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_109 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_110_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_110_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_110 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_110 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_110_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_110
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_bvredand.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_110
  store_step with ih.eo__24eo_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24eo_5ftypeof_5fbvredand s2 v4 _ hinv2 h64 (hG.rem hrem) h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_typeof.case_110 using hn_a0 hn_v1 hn_v2

theorem case_111_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_111_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_111 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_111 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_111_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_111
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_bvredor.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_111
  store_step with ih.eo__24eo_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24eo_5ftypeof_5fbvredand s2 v4 _ hinv2 h64 (hG.rem hrem) h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_typeof.case_111 using hn_a0 hn_v1 hn_v2

theorem case_112_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_112_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_112 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_112 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_112_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_112
  pat_destruct CtorSpec.eo__40bit.destruct h_v1 as ⟨v4, x_v4, h_v4⟩ else hinv hG in EoCases.__eo_typeof.case_112
  obtain hn_v4 := CtorSpec.eo__40bit.fields_ne_stuck hinv h_v1
  store_step with ih.eo__24eo_5ftypeof s v4 _ hinv h64 hrem h_v4 as ⟨v5, s1, hinv1, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4
  store_step with ih.eo__24eo_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v6, s2, hinv2, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  store_step with ih.eo__24eo_5ftypeof_5f_40bit s2 v5 v6 _ _ hinv2 h64 (hG.rem hrem) h_v5 h_v6 as ⟨v7, s3, hinv3, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  case_done hinv3 hG with h_v7 in EoCases.__eo_typeof.case_112 using hn_a0 hn_v1 hn_v2 hn_v4

theorem case_113_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_113_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_113 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_113 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_113_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_113
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_113
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_113
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5f_40from_5fbools s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_113 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_114_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_114_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_114 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_114 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_114_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_RegLan.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_114
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24emb_5fType.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__eo_typeof.case_114 using hn_a0

theorem case_115_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_115_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_115 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_115 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_115_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo_seq_2eempty.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_typeof.case_115
  obtain hn_v1 := CtorSpec.eo_seq_2eempty.fields_ne_stuck hinv h_a0
  store_step with ih.eo__24eo_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying h_a0 h_v1
  store_step with ih.eo__24eo_5ftypeof_5fseq_2eempty s1 v2 v1 _ _ hinv1 h64 (hG.rem hrem) h_v2 h_v1 as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  case_done hinv2 hG with h_v3 in EoCases.__eo_typeof.case_115 using hn_a0 hn_v1

theorem case_116_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_116_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_116 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_116 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_116_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_116
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_str_2elen.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_116
  store_step with ih.eo__24eo_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24eo_5ftypeof_5fstr_2elen s2 v4 _ hinv2 h64 (hG.rem hrem) h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_typeof.case_116 using hn_a0 hn_v1 hn_v2

theorem case_117_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_117_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_117 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_117 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_117_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_117
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_117
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_117
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5fstr_2e_2b_2b s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_117 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_118_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_118_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_118 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_118 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_118_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_118
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_118
  pat_unapply h_v4 as ⟨v7, v8, x_v7, x_v8, h_v7, h_v8, hn_v7, hn_v8⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_118
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s e_v9 (by rw [he_v9]; exact empty_args) hinv h64 as ⟨v9, s1, hinv1, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8
  pat_same v7 v9 with h_v7 h_v9 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_118
  store_step with ih.eo__24eo_5ftypeof s1 v8 _ hinv1 h64 (hG.rem hrem) h_v8 as ⟨v10, s2, hinv2, h_v10⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9
  store_step with ih.eo__24eo_5ftypeof s2 v5 _ hinv2 h64 (hG.rem hrem) h_v5 as ⟨v11, s3, hinv3, h_v11⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10
  store_step with ih.eo__24eo_5ftypeof s3 v2 _ hinv3 h64 (hG.rem hrem) h_v2 as ⟨v12, s4, hinv4, h_v12⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11
  store_step with ih.eo__24eo_5ftypeof_5fstr_2esubstr s4 v10 v11 v12 _ _ _ hinv4 h64 (hG.rem hrem) h_v10 h_v11 h_v12 as ⟨v13, s5, hinv5, h_v13⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
  case_done hinv5 hG with h_v13 in EoCases.__eo_typeof.case_118 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5 hn_v7 hn_v8

theorem case_119_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_119_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_119 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_119 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_119_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_119
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_119
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_str_2econtains.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_119
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5fstr_2econtains s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_119 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_120_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_120_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_120 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_120 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_120_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_120
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_120
  pat_unapply h_v4 as ⟨v7, v8, x_v7, x_v8, h_v7, h_v8, hn_v7, hn_v8⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_120
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_str_2ereplace.construct s e_v9 (by rw [he_v9]; exact empty_args) hinv h64 as ⟨v9, s1, hinv1, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8
  pat_same v7 v9 with h_v7 h_v9 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_120
  store_step with ih.eo__24eo_5ftypeof s1 v8 _ hinv1 h64 (hG.rem hrem) h_v8 as ⟨v10, s2, hinv2, h_v10⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9
  store_step with ih.eo__24eo_5ftypeof s2 v5 _ hinv2 h64 (hG.rem hrem) h_v5 as ⟨v11, s3, hinv3, h_v11⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10
  store_step with ih.eo__24eo_5ftypeof s3 v2 _ hinv3 h64 (hG.rem hrem) h_v2 as ⟨v12, s4, hinv4, h_v12⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11
  store_step with ih.eo__24eo_5ftypeof_5fstr_2ereplace s4 v10 v11 v12 _ _ _ hinv4 h64 (hG.rem hrem) h_v10 h_v11 h_v12 as ⟨v13, s5, hinv5, h_v13⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
  case_done hinv5 hG with h_v13 in EoCases.__eo_typeof.case_120 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5 hn_v7 hn_v8

theorem case_121_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_121_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_121 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_121 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_121_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_121
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_121
  pat_unapply h_v4 as ⟨v7, v8, x_v7, x_v8, h_v7, h_v8, hn_v7, hn_v8⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_121
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_str_2eindexof.construct s e_v9 (by rw [he_v9]; exact empty_args) hinv h64 as ⟨v9, s1, hinv1, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8
  pat_same v7 v9 with h_v7 h_v9 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_121
  store_step with ih.eo__24eo_5ftypeof s1 v8 _ hinv1 h64 (hG.rem hrem) h_v8 as ⟨v10, s2, hinv2, h_v10⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9
  store_step with ih.eo__24eo_5ftypeof s2 v5 _ hinv2 h64 (hG.rem hrem) h_v5 as ⟨v11, s3, hinv3, h_v11⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10
  store_step with ih.eo__24eo_5ftypeof s3 v2 _ hinv3 h64 (hG.rem hrem) h_v2 as ⟨v12, s4, hinv4, h_v12⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11
  store_step with ih.eo__24eo_5ftypeof_5fstr_2eindexof s4 v10 v11 v12 _ _ _ hinv4 h64 (hG.rem hrem) h_v10 h_v11 h_v12 as ⟨v13, s5, hinv5, h_v13⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
  case_done hinv5 hG with h_v13 in EoCases.__eo_typeof.case_121 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5 hn_v7 hn_v8

theorem case_122_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_122_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_122 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_122 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_122_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_122
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_122
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_str_2eat.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_122
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5fstr_2eat s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_122 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_123_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_123_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_123 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_123 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_123_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_123
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_123
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_str_2eprefixof.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_123
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5fstr_2econtains s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_123 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_124_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_124_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_124 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_124 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_124_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_124
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_124
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_str_2esuffixof.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_124
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5fstr_2econtains s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_124 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_125_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_125_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_125 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_125 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_125_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_125
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_str_2erev.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_125
  store_step with ih.eo__24eo_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24eo_5ftypeof_5fstr_2erev s2 v4 _ hinv2 h64 (hG.rem hrem) h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_typeof.case_125 using hn_a0 hn_v1 hn_v2

theorem case_126_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_126_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_126 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_126 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_126_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_126
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_126
  pat_unapply h_v4 as ⟨v7, v8, x_v7, x_v8, h_v7, h_v8, hn_v7, hn_v8⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_126
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_str_2eupdate.construct s e_v9 (by rw [he_v9]; exact empty_args) hinv h64 as ⟨v9, s1, hinv1, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8
  pat_same v7 v9 with h_v7 h_v9 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_126
  store_step with ih.eo__24eo_5ftypeof s1 v8 _ hinv1 h64 (hG.rem hrem) h_v8 as ⟨v10, s2, hinv2, h_v10⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9
  store_step with ih.eo__24eo_5ftypeof s2 v5 _ hinv2 h64 (hG.rem hrem) h_v5 as ⟨v11, s3, hinv3, h_v11⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10
  store_step with ih.eo__24eo_5ftypeof s3 v2 _ hinv3 h64 (hG.rem hrem) h_v2 as ⟨v12, s4, hinv4, h_v12⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11
  store_step with ih.eo__24eo_5ftypeof_5fstr_2eupdate s4 v10 v11 v12 _ _ _ hinv4 h64 (hG.rem hrem) h_v10 h_v11 h_v12 as ⟨v13, s5, hinv5, h_v13⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
  case_done hinv5 hG with h_v13 in EoCases.__eo_typeof.case_126 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5 hn_v7 hn_v8

theorem case_127_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_127_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_127 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_127 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_127_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_127
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_str_2eto_5flower.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_127
  store_step with ih.eo__24eo_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24eo_5ftypeof_5fstr_2eto_5flower s2 v4 _ hinv2 h64 (hG.rem hrem) h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_typeof.case_127 using hn_a0 hn_v1 hn_v2

theorem case_128_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_128_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_128 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_128 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_128_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_128
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_str_2eto_5fupper.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_128
  store_step with ih.eo__24eo_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24eo_5ftypeof_5fstr_2eto_5flower s2 v4 _ hinv2 h64 (hG.rem hrem) h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_typeof.case_128 using hn_a0 hn_v1 hn_v2

theorem case_129_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_129_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_129 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_129 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_129_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_129
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_str_2eto_5fcode.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_129
  store_step with ih.eo__24eo_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24eo_5ftypeof_5fstr_2eto_5fcode s2 v4 _ hinv2 h64 (hG.rem hrem) h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_typeof.case_129 using hn_a0 hn_v1 hn_v2

theorem case_130_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_130_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_130 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_130 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_130_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_130
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_str_2efrom_5fcode.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_130
  store_step with ih.eo__24eo_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24eo_5ftypeof_5fstr_2efrom_5fcode s2 v4 _ hinv2 h64 (hG.rem hrem) h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_typeof.case_130 using hn_a0 hn_v1 hn_v2

theorem case_131_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_131_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_131 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_131 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_131_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_131
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_str_2eis_5fdigit.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_131
  store_step with ih.eo__24eo_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24eo_5ftypeof_5fstr_2eis_5fdigit s2 v4 _ hinv2 h64 (hG.rem hrem) h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_typeof.case_131 using hn_a0 hn_v1 hn_v2

theorem case_132_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_132_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_132 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_132 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_132_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_132
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_str_2eto_5fint.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_132
  store_step with ih.eo__24eo_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24eo_5ftypeof_5fstr_2eto_5fcode s2 v4 _ hinv2 h64 (hG.rem hrem) h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_typeof.case_132 using hn_a0 hn_v1 hn_v2

theorem case_133_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_133_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_133 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_133 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_133_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_133
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_str_2efrom_5fint.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_133
  store_step with ih.eo__24eo_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24eo_5ftypeof_5fstr_2efrom_5fcode s2 v4 _ hinv2 h64 (hG.rem hrem) h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_typeof.case_133 using hn_a0 hn_v1 hn_v2

theorem case_134_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_134_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_134 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_134 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_134_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_134
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_134
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_str_2e_3c.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_134
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5fstr_2e_3c s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_134 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_135_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_135_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_135 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_135 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_135_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_135
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_135
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_str_2e_3c_3d.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_135
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5fstr_2e_3c s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_135 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_136_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_136_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_136 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_136 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_136_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_136
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_136
  pat_unapply h_v4 as ⟨v7, v8, x_v7, x_v8, h_v7, h_v8, hn_v7, hn_v8⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_136
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_str_2ereplace_5fall.construct s e_v9 (by rw [he_v9]; exact empty_args) hinv h64 as ⟨v9, s1, hinv1, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8
  pat_same v7 v9 with h_v7 h_v9 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_136
  store_step with ih.eo__24eo_5ftypeof s1 v8 _ hinv1 h64 (hG.rem hrem) h_v8 as ⟨v10, s2, hinv2, h_v10⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9
  store_step with ih.eo__24eo_5ftypeof s2 v5 _ hinv2 h64 (hG.rem hrem) h_v5 as ⟨v11, s3, hinv3, h_v11⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10
  store_step with ih.eo__24eo_5ftypeof s3 v2 _ hinv3 h64 (hG.rem hrem) h_v2 as ⟨v12, s4, hinv4, h_v12⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11
  store_step with ih.eo__24eo_5ftypeof_5fstr_2ereplace s4 v10 v11 v12 _ _ _ hinv4 h64 (hG.rem hrem) h_v10 h_v11 h_v12 as ⟨v13, s5, hinv5, h_v13⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
  case_done hinv5 hG with h_v13 in EoCases.__eo_typeof.case_136 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5 hn_v7 hn_v8

theorem case_137_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_137_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_137 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_137 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_137_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_137
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_137
  pat_unapply h_v4 as ⟨v7, v8, x_v7, x_v8, h_v7, h_v8, hn_v7, hn_v8⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_137
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_str_2ereplace_5fre.construct s e_v9 (by rw [he_v9]; exact empty_args) hinv h64 as ⟨v9, s1, hinv1, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8
  pat_same v7 v9 with h_v7 h_v9 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_137
  store_step with ih.eo__24eo_5ftypeof s1 v8 _ hinv1 h64 (hG.rem hrem) h_v8 as ⟨v10, s2, hinv2, h_v10⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9
  store_step with ih.eo__24eo_5ftypeof s2 v5 _ hinv2 h64 (hG.rem hrem) h_v5 as ⟨v11, s3, hinv3, h_v11⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10
  store_step with ih.eo__24eo_5ftypeof s3 v2 _ hinv3 h64 (hG.rem hrem) h_v2 as ⟨v12, s4, hinv4, h_v12⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11
  store_step with ih.eo__24eo_5ftypeof_5fstr_2ereplace_5fre s4 v10 v11 v12 _ _ _ hinv4 h64 (hG.rem hrem) h_v10 h_v11 h_v12 as ⟨v13, s5, hinv5, h_v13⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
  case_done hinv5 hG with h_v13 in EoCases.__eo_typeof.case_137 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5 hn_v7 hn_v8

theorem case_138_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_138_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_138 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_138 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_138_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_138
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_138
  pat_unapply h_v4 as ⟨v7, v8, x_v7, x_v8, h_v7, h_v8, hn_v7, hn_v8⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_138
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_str_2ereplace_5fre_5fall.construct s e_v9 (by rw [he_v9]; exact empty_args) hinv h64 as ⟨v9, s1, hinv1, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8
  pat_same v7 v9 with h_v7 h_v9 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_138
  store_step with ih.eo__24eo_5ftypeof s1 v8 _ hinv1 h64 (hG.rem hrem) h_v8 as ⟨v10, s2, hinv2, h_v10⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9
  store_step with ih.eo__24eo_5ftypeof s2 v5 _ hinv2 h64 (hG.rem hrem) h_v5 as ⟨v11, s3, hinv3, h_v11⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10
  store_step with ih.eo__24eo_5ftypeof s3 v2 _ hinv3 h64 (hG.rem hrem) h_v2 as ⟨v12, s4, hinv4, h_v12⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11
  store_step with ih.eo__24eo_5ftypeof_5fstr_2ereplace_5fre s4 v10 v11 v12 _ _ _ hinv4 h64 (hG.rem hrem) h_v10 h_v11 h_v12 as ⟨v13, s5, hinv5, h_v13⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
  case_done hinv5 hG with h_v13 in EoCases.__eo_typeof.case_138 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5 hn_v7 hn_v8

theorem case_139_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_139_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_139 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_139 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_139_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_139
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_139
  pat_unapply h_v4 as ⟨v7, v8, x_v7, x_v8, h_v7, h_v8, hn_v7, hn_v8⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_139
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_str_2eindexof_5fre.construct s e_v9 (by rw [he_v9]; exact empty_args) hinv h64 as ⟨v9, s1, hinv1, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8
  pat_same v7 v9 with h_v7 h_v9 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_139
  store_step with ih.eo__24eo_5ftypeof s1 v8 _ hinv1 h64 (hG.rem hrem) h_v8 as ⟨v10, s2, hinv2, h_v10⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9
  store_step with ih.eo__24eo_5ftypeof s2 v5 _ hinv2 h64 (hG.rem hrem) h_v5 as ⟨v11, s3, hinv3, h_v11⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10
  store_step with ih.eo__24eo_5ftypeof s3 v2 _ hinv3 h64 (hG.rem hrem) h_v2 as ⟨v12, s4, hinv4, h_v12⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11
  store_step with ih.eo__24eo_5ftypeof_5fstr_2eindexof_5fre s4 v10 v11 v12 _ _ _ hinv4 h64 (hG.rem hrem) h_v10 h_v11 h_v12 as ⟨v13, s5, hinv5, h_v13⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
  case_done hinv5 hG with h_v13 in EoCases.__eo_typeof.case_139 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5 hn_v7 hn_v8

theorem case_140_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_140_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_140 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_140 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_140_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_re_2eallchar.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_140
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_RegLan.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__eo_typeof.case_140 using hn_a0

theorem case_141_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_141_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_141 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_141 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_141_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_re_2enone.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_141
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_RegLan.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__eo_typeof.case_141 using hn_a0

theorem case_142_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_142_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_142 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_142 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_142_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_re_2eall.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_142
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_RegLan.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__eo_typeof.case_142 using hn_a0

theorem case_143_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_143_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_143 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_143 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_143_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_143
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_str_2eto_5fre.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_143
  store_step with ih.eo__24eo_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24eo_5ftypeof_5fstr_2eto_5fre s2 v4 _ hinv2 h64 (hG.rem hrem) h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_typeof.case_143 using hn_a0 hn_v1 hn_v2

theorem case_144_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_144_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_144 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_144 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_144_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_144
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_re_2e_2a.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_144
  store_step with ih.eo__24eo_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24eo_5ftypeof_5fre_2e_2a s2 v4 _ hinv2 h64 (hG.rem hrem) h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_typeof.case_144 using hn_a0 hn_v1 hn_v2

theorem case_145_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_145_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_145 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_145 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_145_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_145
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_re_2e_2b.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_145
  store_step with ih.eo__24eo_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24eo_5ftypeof_5fre_2e_2a s2 v4 _ hinv2 h64 (hG.rem hrem) h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_typeof.case_145 using hn_a0 hn_v1 hn_v2

theorem case_146_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_146_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_146 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_146 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_146_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_146
  pat_destruct CtorSpec.eo_re_2e_5e.destruct h_v1 as ⟨v4, x_v4, h_v4⟩ else hinv hG in EoCases.__eo_typeof.case_146
  obtain hn_v4 := CtorSpec.eo_re_2e_5e.fields_ne_stuck hinv h_v1
  store_step with ih.eo__24eo_5ftypeof s v4 _ hinv h64 hrem h_v4 as ⟨v5, s1, hinv1, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4
  store_step with ih.eo__24eo_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v6, s2, hinv2, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  store_step with ih.eo__24eo_5ftypeof_5fre_2e_5e s2 v5 v4 v6 _ _ _ hinv2 h64 (hG.rem hrem) h_v5 h_v4 h_v6 as ⟨v7, s3, hinv3, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  case_done hinv3 hG with h_v7 in EoCases.__eo_typeof.case_146 using hn_a0 hn_v1 hn_v2 hn_v4

theorem case_147_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_147_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_147 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_147 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_147_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_147
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_re_2eopt.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_147
  store_step with ih.eo__24eo_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24eo_5ftypeof_5fre_2e_2a s2 v4 _ hinv2 h64 (hG.rem hrem) h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_typeof.case_147 using hn_a0 hn_v1 hn_v2

theorem case_148_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_148_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_148 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_148 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_148_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_148
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_re_2ecomp.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_148
  store_step with ih.eo__24eo_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24eo_5ftypeof_5fre_2e_2a s2 v4 _ hinv2 h64 (hG.rem hrem) h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_typeof.case_148 using hn_a0 hn_v1 hn_v2

theorem case_149_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_149_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_149 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_149 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_149_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_149
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_149
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_re_2erange.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_149
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5fre_2erange s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_149 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_150_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_150_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_150 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_150 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_150_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_150
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_150
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_re_2e_2b_2b.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_150
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5fre_2e_2b_2b s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_150 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_151_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_151_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_151 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_151 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_151_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_151
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_151
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_re_2einter.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_151
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5fre_2e_2b_2b s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_151 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_152_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_152_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_152 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_152 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_152_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_152
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_152
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_re_2eunion.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_152
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5fre_2e_2b_2b s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_152 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_153_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_153_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_153 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_153 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_153_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_153
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_153
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_re_2ediff.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_153
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5fre_2e_2b_2b s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_153 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_154_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_154_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_154 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_154 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_154_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_154
  pat_destruct CtorSpec.eo_re_2eloop.destruct h_v1 as ⟨v4, x_v4, h_v4⟩ ⟨v5, x_v5, h_v5⟩ else hinv hG in EoCases.__eo_typeof.case_154
  obtain ⟨hn_v4, hn_v5⟩ := CtorSpec.eo_re_2eloop.fields_ne_stuck hinv h_v1
  store_step with ih.eo__24eo_5ftypeof s v4 _ hinv h64 hrem h_v4 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5fre_2eloop s3 v6 v4 v7 v5 v8 _ _ _ _ _ hinv3 h64 (hG.rem hrem) h_v6 h_v4 h_v7 h_v5 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_154 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_155_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_155_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_155 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_155 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_155_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_155
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_155
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_str_2ein_5fre.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_155
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5fstr_2ein_5fre s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_155 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_156_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_156_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_156 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_156 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_156_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_156
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_seq_2eunit.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_156
  store_step with ih.eo__24eo_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24eo_5ftypeof_5fseq_2eunit s2 v4 _ hinv2 h64 (hG.rem hrem) h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_typeof.case_156 using hn_a0 hn_v1 hn_v2

theorem case_157_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_157_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_157 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_157 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_157_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_157
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_157
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_seq_2enth.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_157
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5fseq_2enth s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_157 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_158_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_158_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_158 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_158 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_158_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__40re_5funfold_5fpos_5fcomponent.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ ⟨v3, x_v3, h_v3⟩ else hinv hG in EoCases.__eo_typeof.case_158
  obtain ⟨hn_v1, hn_v2, hn_v3⟩ := CtorSpec.eo__40re_5funfold_5fpos_5fcomponent.fields_ne_stuck hinv h_a0
  store_step with ih.eo__24eo_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v4, s1, hinv1, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24eo_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v5, s2, hinv2, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  store_step with ih.eo__24eo_5ftypeof s2 v3 _ hinv2 h64 (hG.rem hrem) h_v3 as ⟨v6, s3, hinv3, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with ih.eo__24eo_5ftypeof_5f_40re_5funfold_5fpos_5fcomponent s3 v4 v5 v6 _ _ _ hinv3 h64 (hG.rem hrem) h_v4 h_v5 h_v6 as ⟨v7, s4, hinv4, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  case_done hinv4 hG with h_v7 in EoCases.__eo_typeof.case_158 using hn_a0 hn_v1 hn_v2 hn_v3

theorem case_159_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_159_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_159 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_159 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_159_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_159
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_159
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__40strings_5fdeq_5fdiff.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_159
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5f_40strings_5fdeq_5fdiff s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_159 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_160_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_160_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_160 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_160 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_160_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_160
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_160
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__40strings_5fstoi_5fresult.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_160
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5f_40strings_5fstoi_5fresult s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_160 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_161_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_161_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_161 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_161 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_161_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_161
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__40strings_5fstoi_5fnon_5fdigit.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_161
  store_step with ih.eo__24eo_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24eo_5ftypeof_5fstr_2eto_5fcode s2 v4 _ hinv2 h64 (hG.rem hrem) h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_typeof.case_161 using hn_a0 hn_v1 hn_v2

theorem case_162_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_162_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_162 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_162 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_162_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_162
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_162
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__40strings_5fitos_5fresult.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_162
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5fdiv s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_162 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_163_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_163_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_163 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_163 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_163_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_163
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_163
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__40strings_5fnum_5foccur.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_163
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5f_40strings_5fdeq_5fdiff s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_163 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_164_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_164_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_164 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_164 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_164_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_164
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_164
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__40strings_5fnum_5foccur_5fre.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_164
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5f_40strings_5fnum_5foccur_5fre s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_164 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_165_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_165_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_165 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_165 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_165_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_165
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_165
  pat_unapply h_v4 as ⟨v7, v8, x_v7, x_v8, h_v7, h_v8, hn_v7, hn_v8⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_165
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__40strings_5foccur_5findex.construct s e_v9 (by rw [he_v9]; exact empty_args) hinv h64 as ⟨v9, s1, hinv1, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8
  pat_same v7 v9 with h_v7 h_v9 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_165
  store_step with ih.eo__24eo_5ftypeof s1 v8 _ hinv1 h64 (hG.rem hrem) h_v8 as ⟨v10, s2, hinv2, h_v10⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9
  store_step with ih.eo__24eo_5ftypeof s2 v5 _ hinv2 h64 (hG.rem hrem) h_v5 as ⟨v11, s3, hinv3, h_v11⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10
  store_step with ih.eo__24eo_5ftypeof s3 v2 _ hinv3 h64 (hG.rem hrem) h_v2 as ⟨v12, s4, hinv4, h_v12⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11
  store_step with ih.eo__24eo_5ftypeof_5fstr_2eindexof s4 v10 v11 v12 _ _ _ hinv4 h64 (hG.rem hrem) h_v10 h_v11 h_v12 as ⟨v13, s5, hinv5, h_v13⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
  case_done hinv5 hG with h_v13 in EoCases.__eo_typeof.case_165 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5 hn_v7 hn_v8

theorem case_166_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_166_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_166 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_166 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_166_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_166
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_166
  pat_unapply h_v4 as ⟨v7, v8, x_v7, x_v8, h_v7, h_v8, hn_v7, hn_v8⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_166
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__40strings_5foccur_5findex_5fre.construct s e_v9 (by rw [he_v9]; exact empty_args) hinv h64 as ⟨v9, s1, hinv1, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8
  pat_same v7 v9 with h_v7 h_v9 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_166
  store_step with ih.eo__24eo_5ftypeof s1 v8 _ hinv1 h64 (hG.rem hrem) h_v8 as ⟨v10, s2, hinv2, h_v10⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9
  store_step with ih.eo__24eo_5ftypeof s2 v5 _ hinv2 h64 (hG.rem hrem) h_v5 as ⟨v11, s3, hinv3, h_v11⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10
  store_step with ih.eo__24eo_5ftypeof s3 v2 _ hinv3 h64 (hG.rem hrem) h_v2 as ⟨v12, s4, hinv4, h_v12⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11
  store_step with ih.eo__24eo_5ftypeof_5fstr_2eindexof_5fre s4 v10 v11 v12 _ _ _ hinv4 h64 (hG.rem hrem) h_v10 h_v11 h_v12 as ⟨v13, s5, hinv5, h_v13⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
  case_done hinv5 hG with h_v13 in EoCases.__eo_typeof.case_166 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5 hn_v7 hn_v8

theorem case_167_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_167_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_167 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_167 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_167_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_167
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_167
  pat_unapply h_v4 as ⟨v7, v8, x_v7, x_v8, h_v7, h_v8, hn_v7, hn_v8⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_167
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_167
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo__40strings_5freplace_5fall_5fresult.construct s e_v12 (by rw [he_v12]; exact empty_args) hinv h64 as ⟨v12, s1, hinv1, h_v12⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11
  pat_same v10 v12 with h_v10 h_v12 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_167
  store_step with ih.eo__24eo_5ftypeof s1 v11 _ hinv1 h64 (hG.rem hrem) h_v11 as ⟨v13, s2, hinv2, h_v13⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12
  store_step with ih.eo__24eo_5ftypeof s2 v8 _ hinv2 h64 (hG.rem hrem) h_v8 as ⟨v14, s3, hinv3, h_v14⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13
  store_step with ih.eo__24eo_5ftypeof s3 v5 _ hinv3 h64 (hG.rem hrem) h_v5 as ⟨v15, s4, hinv4, h_v15⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14
  store_step with ih.eo__24eo_5ftypeof s4 v2 _ hinv4 h64 (hG.rem hrem) h_v2 as ⟨v16, s5, hinv5, h_v16⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15
  store_step with ih.eo__24eo_5ftypeof_5f_40strings_5freplace_5fall_5fresult s5 v13 v14 v15 v16 _ _ _ _ hinv5 h64 (hG.rem hrem) h_v13 h_v14 h_v15 h_v16 as ⟨v17, s6, hinv6, h_v17⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16
  case_done hinv6 hG with h_v17 in EoCases.__eo_typeof.case_167 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5 hn_v7 hn_v8 hn_v10 hn_v11

theorem case_168_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_168_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_168 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_168 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_168_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_168
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_168
  pat_unapply h_v4 as ⟨v7, v8, x_v7, x_v8, h_v7, h_v8, hn_v7, hn_v8⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_168
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_168
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo__40strings_5freplace_5fre_5fall_5fresult.construct s e_v12 (by rw [he_v12]; exact empty_args) hinv h64 as ⟨v12, s1, hinv1, h_v12⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11
  pat_same v10 v12 with h_v10 h_v12 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_168
  store_step with ih.eo__24eo_5ftypeof s1 v11 _ hinv1 h64 (hG.rem hrem) h_v11 as ⟨v13, s2, hinv2, h_v13⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12
  store_step with ih.eo__24eo_5ftypeof s2 v8 _ hinv2 h64 (hG.rem hrem) h_v8 as ⟨v14, s3, hinv3, h_v14⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13
  store_step with ih.eo__24eo_5ftypeof s3 v5 _ hinv3 h64 (hG.rem hrem) h_v5 as ⟨v15, s4, hinv4, h_v15⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14
  store_step with ih.eo__24eo_5ftypeof s4 v2 _ hinv4 h64 (hG.rem hrem) h_v2 as ⟨v16, s5, hinv5, h_v16⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15
  store_step with ih.eo__24eo_5ftypeof_5f_40strings_5freplace_5fre_5fall_5fresult s5 v13 v14 v15 v16 _ _ _ _ hinv5 h64 (hG.rem hrem) h_v13 h_v14 h_v15 h_v16 as ⟨v17, s6, hinv6, h_v17⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16
  case_done hinv6 hG with h_v17 in EoCases.__eo_typeof.case_168 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5 hn_v7 hn_v8 hn_v10 hn_v11

theorem case_169_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_169_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_169 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_169 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_169_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__40witness_5fstring_5flength.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ ⟨v3, x_v3, h_v3⟩ else hinv hG in EoCases.__eo_typeof.case_169
  obtain ⟨hn_v1, hn_v2, hn_v3⟩ := CtorSpec.eo__40witness_5fstring_5flength.fields_ne_stuck hinv h_a0
  store_step with ih.eo__24eo_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v4, s1, hinv1, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24eo_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v5, s2, hinv2, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  store_step with ih.eo__24eo_5ftypeof s2 v3 _ hinv2 h64 (hG.rem hrem) h_v3 as ⟨v6, s3, hinv3, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with ih.eo__24eo_5ftypeof_5f_40witness_5fstring_5flength s3 v4 v1 v5 v6 _ _ _ _ hinv3 h64 (hG.rem hrem) h_v4 h_v1 h_v5 h_v6 as ⟨v7, s4, hinv4, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  case_done hinv4 hG with h_v7 in EoCases.__eo_typeof.case_169 using hn_a0 hn_v1 hn_v2 hn_v3

theorem case_170_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_170_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_170 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_170 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_170_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_170
  pat_destruct CtorSpec.eo_is.destruct h_v1 as ⟨v4, x_v4, h_v4⟩ else hinv hG in EoCases.__eo_typeof.case_170
  obtain hn_v4 := CtorSpec.eo_is.fields_ne_stuck hinv h_v1
  store_step with ih.eo__24eo_5ftypeof s v4 _ hinv h64 hrem h_v4 as ⟨v5, s1, hinv1, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4
  store_step with ih.eo__24eo_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v6, s2, hinv2, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  store_step with ih.eo__24eo_5ftypeof_5fis s2 v5 v6 _ _ hinv2 h64 (hG.rem hrem) h_v5 h_v6 as ⟨v7, s3, hinv3, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  case_done hinv3 hG with h_v7 in EoCases.__eo_typeof.case_170 using hn_a0 hn_v1 hn_v2 hn_v4

theorem case_171_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_171_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_171 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_171 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_171_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_171
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_171
  pat_destruct CtorSpec.eo_update.destruct h_v4 as ⟨v7, x_v7, h_v7⟩ else hinv hG in EoCases.__eo_typeof.case_171
  obtain hn_v7 := CtorSpec.eo_update.fields_ne_stuck hinv h_v4
  store_step with ih.eo__24eo_5ftypeof s v7 _ hinv h64 hrem h_v7 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v9, s2, hinv2, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v10, s3, hinv3, h_v10⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9
  store_step with ih.eo__24eo_5ftypeof_5fupdate s3 v8 v9 v10 _ _ _ hinv3 h64 (hG.rem hrem) h_v8 h_v9 h_v10 as ⟨v11, s4, hinv4, h_v11⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10
  case_done hinv4 hG with h_v11 in EoCases.__eo_typeof.case_171 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5 hn_v7

theorem case_172_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_172_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_172 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_172 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_172_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_UnitTuple.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_172
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24emb_5fType.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__eo_typeof.case_172 using hn_a0

theorem case_173_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_173_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_173 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_173 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_173_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_173
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_173
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_Tuple.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_173
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5f_40_40Pair s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_173 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_174_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_174_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_174 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_174 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_174_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_tuple_2eunit.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_174
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_UnitTuple.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__eo_typeof.case_174 using hn_a0

theorem case_175_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_175_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_175 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_175 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_175_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_175
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_175
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_tuple.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_175
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5ftuple s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_175 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_176_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_176_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_176 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_176 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_176_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_176
  pat_destruct CtorSpec.eo_tuple_2eselect.destruct h_v1 as ⟨v4, x_v4, h_v4⟩ else hinv hG in EoCases.__eo_typeof.case_176
  obtain hn_v4 := CtorSpec.eo_tuple_2eselect.fields_ne_stuck hinv h_v1
  store_step with ih.eo__24eo_5ftypeof s v4 _ hinv h64 hrem h_v4 as ⟨v5, s1, hinv1, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4
  store_step with ih.eo__24eo_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v6, s2, hinv2, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  store_step with ih.eo__24eo_5ftypeof_5ftuple_2eselect s2 v5 v4 v6 _ _ _ hinv2 h64 (hG.rem hrem) h_v5 h_v4 h_v6 as ⟨v7, s3, hinv3, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  case_done hinv3 hG with h_v7 in EoCases.__eo_typeof.case_176 using hn_a0 hn_v1 hn_v2 hn_v4

theorem case_177_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_177_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_177 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_177 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_177_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_177
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_177
  pat_destruct CtorSpec.eo_tuple_2eupdate.destruct h_v4 as ⟨v7, x_v7, h_v7⟩ else hinv hG in EoCases.__eo_typeof.case_177
  obtain hn_v7 := CtorSpec.eo_tuple_2eupdate.fields_ne_stuck hinv h_v4
  store_step with ih.eo__24eo_5ftypeof s v7 _ hinv h64 hrem h_v7 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v9, s2, hinv2, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v10, s3, hinv3, h_v10⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9
  store_step with ih.eo__24eo_5ftypeof_5ftuple_2eupdate s3 v8 v7 v9 v10 _ _ _ _ hinv3 h64 (hG.rem hrem) h_v8 h_v7 h_v9 h_v10 as ⟨v11, s4, hinv4, h_v11⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10
  case_done hinv4 hG with h_v11 in EoCases.__eo_typeof.case_177 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5 hn_v7

theorem case_178_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_178_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_178 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_178 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_178_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_178
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_Set.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_178
  store_step with ih.eo__24eo_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24eo_5ftypeof_5fSeq s2 v4 _ hinv2 h64 (hG.rem hrem) h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_typeof.case_178 using hn_a0 hn_v1 hn_v2

theorem case_179_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_179_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_179 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_179 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_179_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo_set_2eempty.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_typeof.case_179
  obtain hn_v1 := CtorSpec.eo_set_2eempty.fields_ne_stuck hinv h_a0
  store_step with ih.eo__24eo_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying h_a0 h_v1
  store_step with ih.eo__24eo_5ftypeof_5fset_2eempty s1 v2 v1 _ _ hinv1 h64 (hG.rem hrem) h_v2 h_v1 as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  case_done hinv2 hG with h_v3 in EoCases.__eo_typeof.case_179 using hn_a0 hn_v1

theorem case_180_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_180_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_180 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_180 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_180_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_180
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_set_2esingleton.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_180
  store_step with ih.eo__24eo_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24eo_5ftypeof_5fset_2esingleton s2 v4 _ hinv2 h64 (hG.rem hrem) h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_typeof.case_180 using hn_a0 hn_v1 hn_v2

theorem case_181_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_181_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_181 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_181 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_181_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_181
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_181
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_set_2eunion.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_181
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5fset_2eunion s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_181 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_182_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_182_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_182 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_182 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_182_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_182
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_182
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_set_2einter.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_182
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5fset_2eunion s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_182 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_183_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_183_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_183 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_183 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_183_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_183
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_183
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_set_2eminus.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_183
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5fset_2eunion s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_183 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_184_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_184_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_184 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_184 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_184_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_184
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_184
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_set_2emember.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_184
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5fset_2emember s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_184 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_185_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_185_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_185 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_185 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_185_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_185
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_185
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_set_2esubset.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_185
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5fset_2esubset s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_185 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_186_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_186_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_186 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_186 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_186_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_186
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_set_2echoose.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_186
  store_step with ih.eo__24eo_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24eo_5ftypeof_5fset_2echoose s2 v4 _ hinv2 h64 (hG.rem hrem) h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_typeof.case_186 using hn_a0 hn_v1 hn_v2

theorem case_187_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_187_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_187 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_187 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_187_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_187
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_set_2eis_5fempty.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_187
  store_step with ih.eo__24eo_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24eo_5ftypeof_5fset_2eis_5fempty s2 v4 _ hinv2 h64 (hG.rem hrem) h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_typeof.case_187 using hn_a0 hn_v1 hn_v2

theorem case_188_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_188_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_188 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_188 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_188_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_188
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_set_2eis_5fsingleton.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_188
  store_step with ih.eo__24eo_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24eo_5ftypeof_5fset_2eis_5fempty s2 v4 _ hinv2 h64 (hG.rem hrem) h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_typeof.case_188 using hn_a0 hn_v1 hn_v2

theorem case_189_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_189_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_189 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_189 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_189_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_189
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_189
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_set_2einsert.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_189
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5fset_2einsert s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_189 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_190_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_190_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_190 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_190 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_190_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_190
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_190
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__40sets_5fdeq_5fdiff.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_190
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5f_40sets_5fdeq_5fdiff s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_190 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_191_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_191_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_191 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_191 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_191_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_191
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_191
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__2f.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_191
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5f_2f s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_191 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_192_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_192_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_192 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_192 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_192_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_192
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_192
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__2f_5ftotal.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_192
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5f_2f s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_192 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_193_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_193_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_193 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_193 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_193_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_193
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__40div_5fby_5fzero.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_193
  store_step with ih.eo__24eo_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24eo_5ftypeof_5f_40div_5fby_5fzero s2 v4 _ hinv2 h64 (hG.rem hrem) h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_typeof.case_193 using hn_a0 hn_v1 hn_v2

theorem case_194_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_194_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_194 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_194 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_194_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__40_40Monomial.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_194
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24emb_5fType.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__eo_typeof.case_194 using hn_a0

theorem case_195_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_195_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_195 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_195 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_195_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_195
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_195
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__40_40mon.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_195
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5f_40_40mon s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_195 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_196_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_196_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_196 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_196 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_196_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__40_40Polynomial.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_196
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24emb_5fType.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__eo_typeof.case_196 using hn_a0

theorem case_197_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_197_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_197 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_197 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_197_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__40_40poly_2ezero.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_197
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__40_40Polynomial.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__eo_typeof.case_197 using hn_a0

theorem case_198_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_198_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_198 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_198 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_198_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_198
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_198
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__40_40poly.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_198
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5f_40_40poly s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_198 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_199_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_199_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_199 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_199 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_199_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_199
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_199
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_forall.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_199
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5fforall s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_199 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_200_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_200_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_200 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_200 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_200_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_200
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_200
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_exists.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_200
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5fforall s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_200 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_201_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_201_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_201 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_201 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_201_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__40quantifiers_5fskolemize.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__eo_typeof.case_201
  obtain ⟨hn_v1, hn_v2⟩ := CtorSpec.eo__40quantifiers_5fskolemize.fields_ne_stuck hinv h_a0
  store_step with ih.eo__24eo_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24eo_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24eo_5ftypeof_5f_40quantifiers_5fskolemize s2 v3 v1 v4 v2 _ _ _ _ hinv2 h64 (hG.rem hrem) h_v3 h_v1 h_v4 h_v2 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_typeof.case_201 using hn_a0 hn_v1 hn_v2

theorem case_202_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_202_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_202 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_202 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_202_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_202
  pat_destruct CtorSpec.eo_int_5fto_5fbv.destruct h_v1 as ⟨v4, x_v4, h_v4⟩ else hinv hG in EoCases.__eo_typeof.case_202
  obtain hn_v4 := CtorSpec.eo_int_5fto_5fbv.fields_ne_stuck hinv h_v1
  store_step with ih.eo__24eo_5ftypeof s v4 _ hinv h64 hrem h_v4 as ⟨v5, s1, hinv1, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4
  store_step with ih.eo__24eo_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v6, s2, hinv2, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  store_step with ih.eo__24eo_5ftypeof_5fint_5fto_5fbv s2 v5 v4 v6 _ _ _ hinv2 h64 (hG.rem hrem) h_v5 h_v4 h_v6 as ⟨v7, s3, hinv3, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  case_done hinv3 hG with h_v7 in EoCases.__eo_typeof.case_202 using hn_a0 hn_v1 hn_v2 hn_v4

theorem case_203_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_203_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_203 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_203 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_203_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_203
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_ubv_5fto_5fint.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_203
  store_step with ih.eo__24eo_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24eo_5ftypeof_5f_40bvsize s2 v4 _ hinv2 h64 (hG.rem hrem) h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_typeof.case_203 using hn_a0 hn_v1 hn_v2

theorem case_204_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_204_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_204 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_204 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_204_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_204
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_sbv_5fto_5fint.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_204
  store_step with ih.eo__24eo_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24eo_5ftypeof_5f_40bvsize s2 v4 _ hinv2 h64 (hG.rem hrem) h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_typeof.case_204 using hn_a0 hn_v1 hn_v2

theorem case_205_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_205_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_205 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_205 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_205_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_205
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_205
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__40_40aci_5fsorted.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof.case_205
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5ftypeof_5f_40_40aci_5fsorted s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof.case_205 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_206_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_206_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_206 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_206 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_206_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__40const.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__eo_typeof.case_206
  obtain ⟨hn_v1, hn_v2⟩ := CtorSpec.eo__40const.fields_ne_stuck hinv h_a0
  store_step with ih.eo__24eo_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24eo_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24eo_5ftypeof_5f_40const s2 v3 v4 v2 _ _ _ hinv2 h64 (hG.rem hrem) h_v3 h_v4 h_v2 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_typeof.case_206 using hn_a0 hn_v1 hn_v2

theorem case_207_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_207_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof.case_207 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_207 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_207_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof.case_207
  store_step with ih.eo__24eo_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24eo_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24eo_5ftypeof_5fapply s2 v3 v4 _ _ hinv2 h64 (hG.rem hrem) h_v3 h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_typeof.case_207 using hn_a0 hn_v1 hn_v2

theorem cases_0_0_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    cases_0_0_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_typeof.case_0 x_a0, EoCases.__eo_typeof.case_1 x_a0, EoCases.__eo_typeof.case_2 x_a0, EoCases.__eo_typeof.case_3 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_0 x_a0 = none ∧ EoCases.__eo_typeof.case_1 x_a0 = none ∧ EoCases.__eo_typeof.case_2 x_a0 = none ∧ EoCases.__eo_typeof.case_3 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_0_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  group_step with case_0_eo__24eo_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_0 x_a0, EoCases.__eo_typeof.case_1 x_a0, EoCases.__eo_typeof.case_2 x_a0, EoCases.__eo_typeof.case_3 x_a0] = [] ++ [EoCases.__eo_typeof.case_0 x_a0] ++ [EoCases.__eo_typeof.case_1 x_a0, EoCases.__eo_typeof.case_2 x_a0, EoCases.__eo_typeof.case_3 x_a0] from rfl)
    otherwise ⟨hl_0⟩ using hn_a0
  group_step with case_1_eo__24eo_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_0 x_a0, EoCases.__eo_typeof.case_1 x_a0, EoCases.__eo_typeof.case_2 x_a0, EoCases.__eo_typeof.case_3 x_a0] = [EoCases.__eo_typeof.case_0 x_a0] ++ [EoCases.__eo_typeof.case_1 x_a0] ++ [EoCases.__eo_typeof.case_2 x_a0, EoCases.__eo_typeof.case_3 x_a0] from rfl)
    otherwise ⟨hl_1⟩ using hn_a0 hl_0
  group_step with case_2_eo__24eo_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_0 x_a0, EoCases.__eo_typeof.case_1 x_a0, EoCases.__eo_typeof.case_2 x_a0, EoCases.__eo_typeof.case_3 x_a0] = [EoCases.__eo_typeof.case_0 x_a0, EoCases.__eo_typeof.case_1 x_a0] ++ [EoCases.__eo_typeof.case_2 x_a0] ++ [EoCases.__eo_typeof.case_3 x_a0] from rfl)
    otherwise ⟨hl_2⟩ using hn_a0 hl_0 hl_1
  group_step with case_3_eo__24eo_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_0 x_a0, EoCases.__eo_typeof.case_1 x_a0, EoCases.__eo_typeof.case_2 x_a0, EoCases.__eo_typeof.case_3 x_a0] = [EoCases.__eo_typeof.case_0 x_a0, EoCases.__eo_typeof.case_1 x_a0, EoCases.__eo_typeof.case_2 x_a0] ++ [EoCases.__eo_typeof.case_3 x_a0] ++ [] from rfl)
    otherwise ⟨hl_3⟩ using hn_a0 hl_0 hl_1 hl_2
  group_none hinv4 hG with ⟨hl_0, hl_1, hl_2, hl_3⟩

theorem cases_0_1_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    cases_0_1_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_typeof.case_4 x_a0, EoCases.__eo_typeof.case_5 x_a0, EoCases.__eo_typeof.case_6 x_a0, EoCases.__eo_typeof.case_7 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_4 x_a0 = none ∧ EoCases.__eo_typeof.case_5 x_a0 = none ∧ EoCases.__eo_typeof.case_6 x_a0 = none ∧ EoCases.__eo_typeof.case_7 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_1_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  group_step with case_4_eo__24eo_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_4 x_a0, EoCases.__eo_typeof.case_5 x_a0, EoCases.__eo_typeof.case_6 x_a0, EoCases.__eo_typeof.case_7 x_a0] = [] ++ [EoCases.__eo_typeof.case_4 x_a0] ++ [EoCases.__eo_typeof.case_5 x_a0, EoCases.__eo_typeof.case_6 x_a0, EoCases.__eo_typeof.case_7 x_a0] from rfl)
    otherwise ⟨hl_4⟩ using hn_a0
  group_step with case_5_eo__24eo_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_4 x_a0, EoCases.__eo_typeof.case_5 x_a0, EoCases.__eo_typeof.case_6 x_a0, EoCases.__eo_typeof.case_7 x_a0] = [EoCases.__eo_typeof.case_4 x_a0] ++ [EoCases.__eo_typeof.case_5 x_a0] ++ [EoCases.__eo_typeof.case_6 x_a0, EoCases.__eo_typeof.case_7 x_a0] from rfl)
    otherwise ⟨hl_5⟩ using hn_a0 hl_4
  group_step with case_6_eo__24eo_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_4 x_a0, EoCases.__eo_typeof.case_5 x_a0, EoCases.__eo_typeof.case_6 x_a0, EoCases.__eo_typeof.case_7 x_a0] = [EoCases.__eo_typeof.case_4 x_a0, EoCases.__eo_typeof.case_5 x_a0] ++ [EoCases.__eo_typeof.case_6 x_a0] ++ [EoCases.__eo_typeof.case_7 x_a0] from rfl)
    otherwise ⟨hl_6⟩ using hn_a0 hl_4 hl_5
  group_step with case_7_eo__24eo_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_4 x_a0, EoCases.__eo_typeof.case_5 x_a0, EoCases.__eo_typeof.case_6 x_a0, EoCases.__eo_typeof.case_7 x_a0] = [EoCases.__eo_typeof.case_4 x_a0, EoCases.__eo_typeof.case_5 x_a0, EoCases.__eo_typeof.case_6 x_a0] ++ [EoCases.__eo_typeof.case_7 x_a0] ++ [] from rfl)
    otherwise ⟨hl_7⟩ using hn_a0 hl_4 hl_5 hl_6
  group_none hinv4 hG with ⟨hl_4, hl_5, hl_6, hl_7⟩

theorem cases_0_2_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    cases_0_2_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_typeof.case_8 x_a0, EoCases.__eo_typeof.case_9 x_a0, EoCases.__eo_typeof.case_10 x_a0, EoCases.__eo_typeof.case_11 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_8 x_a0 = none ∧ EoCases.__eo_typeof.case_9 x_a0 = none ∧ EoCases.__eo_typeof.case_10 x_a0 = none ∧ EoCases.__eo_typeof.case_11 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_2_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  group_step with case_8_eo__24eo_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_8 x_a0, EoCases.__eo_typeof.case_9 x_a0, EoCases.__eo_typeof.case_10 x_a0, EoCases.__eo_typeof.case_11 x_a0] = [] ++ [EoCases.__eo_typeof.case_8 x_a0] ++ [EoCases.__eo_typeof.case_9 x_a0, EoCases.__eo_typeof.case_10 x_a0, EoCases.__eo_typeof.case_11 x_a0] from rfl)
    otherwise ⟨hl_8⟩ using hn_a0
  group_step with case_9_eo__24eo_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_8 x_a0, EoCases.__eo_typeof.case_9 x_a0, EoCases.__eo_typeof.case_10 x_a0, EoCases.__eo_typeof.case_11 x_a0] = [EoCases.__eo_typeof.case_8 x_a0] ++ [EoCases.__eo_typeof.case_9 x_a0] ++ [EoCases.__eo_typeof.case_10 x_a0, EoCases.__eo_typeof.case_11 x_a0] from rfl)
    otherwise ⟨hl_9⟩ using hn_a0 hl_8
  group_step with case_10_eo__24eo_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_8 x_a0, EoCases.__eo_typeof.case_9 x_a0, EoCases.__eo_typeof.case_10 x_a0, EoCases.__eo_typeof.case_11 x_a0] = [EoCases.__eo_typeof.case_8 x_a0, EoCases.__eo_typeof.case_9 x_a0] ++ [EoCases.__eo_typeof.case_10 x_a0] ++ [EoCases.__eo_typeof.case_11 x_a0] from rfl)
    otherwise ⟨hl_10⟩ using hn_a0 hl_8 hl_9
  group_step with case_11_eo__24eo_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_8 x_a0, EoCases.__eo_typeof.case_9 x_a0, EoCases.__eo_typeof.case_10 x_a0, EoCases.__eo_typeof.case_11 x_a0] = [EoCases.__eo_typeof.case_8 x_a0, EoCases.__eo_typeof.case_9 x_a0, EoCases.__eo_typeof.case_10 x_a0] ++ [EoCases.__eo_typeof.case_11 x_a0] ++ [] from rfl)
    otherwise ⟨hl_11⟩ using hn_a0 hl_8 hl_9 hl_10
  group_none hinv4 hG with ⟨hl_8, hl_9, hl_10, hl_11⟩

theorem cases_0_3_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    cases_0_3_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_typeof.case_12 x_a0, EoCases.__eo_typeof.case_13 x_a0, EoCases.__eo_typeof.case_14 x_a0, EoCases.__eo_typeof.case_15 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_12 x_a0 = none ∧ EoCases.__eo_typeof.case_13 x_a0 = none ∧ EoCases.__eo_typeof.case_14 x_a0 = none ∧ EoCases.__eo_typeof.case_15 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_3_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  group_step with case_12_eo__24eo_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_12 x_a0, EoCases.__eo_typeof.case_13 x_a0, EoCases.__eo_typeof.case_14 x_a0, EoCases.__eo_typeof.case_15 x_a0] = [] ++ [EoCases.__eo_typeof.case_12 x_a0] ++ [EoCases.__eo_typeof.case_13 x_a0, EoCases.__eo_typeof.case_14 x_a0, EoCases.__eo_typeof.case_15 x_a0] from rfl)
    otherwise ⟨hl_12⟩ using hn_a0
  group_step with case_13_eo__24eo_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_12 x_a0, EoCases.__eo_typeof.case_13 x_a0, EoCases.__eo_typeof.case_14 x_a0, EoCases.__eo_typeof.case_15 x_a0] = [EoCases.__eo_typeof.case_12 x_a0] ++ [EoCases.__eo_typeof.case_13 x_a0] ++ [EoCases.__eo_typeof.case_14 x_a0, EoCases.__eo_typeof.case_15 x_a0] from rfl)
    otherwise ⟨hl_13⟩ using hn_a0 hl_12
  group_step with case_14_eo__24eo_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_12 x_a0, EoCases.__eo_typeof.case_13 x_a0, EoCases.__eo_typeof.case_14 x_a0, EoCases.__eo_typeof.case_15 x_a0] = [EoCases.__eo_typeof.case_12 x_a0, EoCases.__eo_typeof.case_13 x_a0] ++ [EoCases.__eo_typeof.case_14 x_a0] ++ [EoCases.__eo_typeof.case_15 x_a0] from rfl)
    otherwise ⟨hl_14⟩ using hn_a0 hl_12 hl_13
  group_step with case_15_eo__24eo_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_12 x_a0, EoCases.__eo_typeof.case_13 x_a0, EoCases.__eo_typeof.case_14 x_a0, EoCases.__eo_typeof.case_15 x_a0] = [EoCases.__eo_typeof.case_12 x_a0, EoCases.__eo_typeof.case_13 x_a0, EoCases.__eo_typeof.case_14 x_a0] ++ [EoCases.__eo_typeof.case_15 x_a0] ++ [] from rfl)
    otherwise ⟨hl_15⟩ using hn_a0 hl_12 hl_13 hl_14
  group_none hinv4 hG with ⟨hl_12, hl_13, hl_14, hl_15⟩

theorem cases_0_4_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    cases_0_4_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_typeof.case_16 x_a0, EoCases.__eo_typeof.case_17 x_a0, EoCases.__eo_typeof.case_18 x_a0, EoCases.__eo_typeof.case_19 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_16 x_a0 = none ∧ EoCases.__eo_typeof.case_17 x_a0 = none ∧ EoCases.__eo_typeof.case_18 x_a0 = none ∧ EoCases.__eo_typeof.case_19 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_4_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  group_step with case_16_eo__24eo_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_16 x_a0, EoCases.__eo_typeof.case_17 x_a0, EoCases.__eo_typeof.case_18 x_a0, EoCases.__eo_typeof.case_19 x_a0] = [] ++ [EoCases.__eo_typeof.case_16 x_a0] ++ [EoCases.__eo_typeof.case_17 x_a0, EoCases.__eo_typeof.case_18 x_a0, EoCases.__eo_typeof.case_19 x_a0] from rfl)
    otherwise ⟨hl_16⟩ using hn_a0
  group_step with case_17_eo__24eo_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_16 x_a0, EoCases.__eo_typeof.case_17 x_a0, EoCases.__eo_typeof.case_18 x_a0, EoCases.__eo_typeof.case_19 x_a0] = [EoCases.__eo_typeof.case_16 x_a0] ++ [EoCases.__eo_typeof.case_17 x_a0] ++ [EoCases.__eo_typeof.case_18 x_a0, EoCases.__eo_typeof.case_19 x_a0] from rfl)
    otherwise ⟨hl_17⟩ using hn_a0 hl_16
  group_step with case_18_eo__24eo_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_16 x_a0, EoCases.__eo_typeof.case_17 x_a0, EoCases.__eo_typeof.case_18 x_a0, EoCases.__eo_typeof.case_19 x_a0] = [EoCases.__eo_typeof.case_16 x_a0, EoCases.__eo_typeof.case_17 x_a0] ++ [EoCases.__eo_typeof.case_18 x_a0] ++ [EoCases.__eo_typeof.case_19 x_a0] from rfl)
    otherwise ⟨hl_18⟩ using hn_a0 hl_16 hl_17
  group_step with case_19_eo__24eo_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_16 x_a0, EoCases.__eo_typeof.case_17 x_a0, EoCases.__eo_typeof.case_18 x_a0, EoCases.__eo_typeof.case_19 x_a0] = [EoCases.__eo_typeof.case_16 x_a0, EoCases.__eo_typeof.case_17 x_a0, EoCases.__eo_typeof.case_18 x_a0] ++ [EoCases.__eo_typeof.case_19 x_a0] ++ [] from rfl)
    otherwise ⟨hl_19⟩ using hn_a0 hl_16 hl_17 hl_18
  group_none hinv4 hG with ⟨hl_16, hl_17, hl_18, hl_19⟩

theorem cases_0_5_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    cases_0_5_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_typeof.case_20 x_a0, EoCases.__eo_typeof.case_21 x_a0, EoCases.__eo_typeof.case_22 x_a0, EoCases.__eo_typeof.case_23 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_20 x_a0 = none ∧ EoCases.__eo_typeof.case_21 x_a0 = none ∧ EoCases.__eo_typeof.case_22 x_a0 = none ∧ EoCases.__eo_typeof.case_23 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_5_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  group_step with case_20_eo__24eo_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_20 x_a0, EoCases.__eo_typeof.case_21 x_a0, EoCases.__eo_typeof.case_22 x_a0, EoCases.__eo_typeof.case_23 x_a0] = [] ++ [EoCases.__eo_typeof.case_20 x_a0] ++ [EoCases.__eo_typeof.case_21 x_a0, EoCases.__eo_typeof.case_22 x_a0, EoCases.__eo_typeof.case_23 x_a0] from rfl)
    otherwise ⟨hl_20⟩ using hn_a0
  group_step with case_21_eo__24eo_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_20 x_a0, EoCases.__eo_typeof.case_21 x_a0, EoCases.__eo_typeof.case_22 x_a0, EoCases.__eo_typeof.case_23 x_a0] = [EoCases.__eo_typeof.case_20 x_a0] ++ [EoCases.__eo_typeof.case_21 x_a0] ++ [EoCases.__eo_typeof.case_22 x_a0, EoCases.__eo_typeof.case_23 x_a0] from rfl)
    otherwise ⟨hl_21⟩ using hn_a0 hl_20
  group_step with case_22_eo__24eo_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_20 x_a0, EoCases.__eo_typeof.case_21 x_a0, EoCases.__eo_typeof.case_22 x_a0, EoCases.__eo_typeof.case_23 x_a0] = [EoCases.__eo_typeof.case_20 x_a0, EoCases.__eo_typeof.case_21 x_a0] ++ [EoCases.__eo_typeof.case_22 x_a0] ++ [EoCases.__eo_typeof.case_23 x_a0] from rfl)
    otherwise ⟨hl_22⟩ using hn_a0 hl_20 hl_21
  group_step with case_23_eo__24eo_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_20 x_a0, EoCases.__eo_typeof.case_21 x_a0, EoCases.__eo_typeof.case_22 x_a0, EoCases.__eo_typeof.case_23 x_a0] = [EoCases.__eo_typeof.case_20 x_a0, EoCases.__eo_typeof.case_21 x_a0, EoCases.__eo_typeof.case_22 x_a0] ++ [EoCases.__eo_typeof.case_23 x_a0] ++ [] from rfl)
    otherwise ⟨hl_23⟩ using hn_a0 hl_20 hl_21 hl_22
  group_none hinv4 hG with ⟨hl_20, hl_21, hl_22, hl_23⟩

theorem cases_0_6_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    cases_0_6_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_typeof.case_24 x_a0, EoCases.__eo_typeof.case_25 x_a0, EoCases.__eo_typeof.case_26 x_a0, EoCases.__eo_typeof.case_27 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_24 x_a0 = none ∧ EoCases.__eo_typeof.case_25 x_a0 = none ∧ EoCases.__eo_typeof.case_26 x_a0 = none ∧ EoCases.__eo_typeof.case_27 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_6_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  group_step with case_24_eo__24eo_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_24 x_a0, EoCases.__eo_typeof.case_25 x_a0, EoCases.__eo_typeof.case_26 x_a0, EoCases.__eo_typeof.case_27 x_a0] = [] ++ [EoCases.__eo_typeof.case_24 x_a0] ++ [EoCases.__eo_typeof.case_25 x_a0, EoCases.__eo_typeof.case_26 x_a0, EoCases.__eo_typeof.case_27 x_a0] from rfl)
    otherwise ⟨hl_24⟩ using hn_a0
  group_step with case_25_eo__24eo_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_24 x_a0, EoCases.__eo_typeof.case_25 x_a0, EoCases.__eo_typeof.case_26 x_a0, EoCases.__eo_typeof.case_27 x_a0] = [EoCases.__eo_typeof.case_24 x_a0] ++ [EoCases.__eo_typeof.case_25 x_a0] ++ [EoCases.__eo_typeof.case_26 x_a0, EoCases.__eo_typeof.case_27 x_a0] from rfl)
    otherwise ⟨hl_25⟩ using hn_a0 hl_24
  group_step with case_26_eo__24eo_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_24 x_a0, EoCases.__eo_typeof.case_25 x_a0, EoCases.__eo_typeof.case_26 x_a0, EoCases.__eo_typeof.case_27 x_a0] = [EoCases.__eo_typeof.case_24 x_a0, EoCases.__eo_typeof.case_25 x_a0] ++ [EoCases.__eo_typeof.case_26 x_a0] ++ [EoCases.__eo_typeof.case_27 x_a0] from rfl)
    otherwise ⟨hl_26⟩ using hn_a0 hl_24 hl_25
  group_step with case_27_eo__24eo_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_24 x_a0, EoCases.__eo_typeof.case_25 x_a0, EoCases.__eo_typeof.case_26 x_a0, EoCases.__eo_typeof.case_27 x_a0] = [EoCases.__eo_typeof.case_24 x_a0, EoCases.__eo_typeof.case_25 x_a0, EoCases.__eo_typeof.case_26 x_a0] ++ [EoCases.__eo_typeof.case_27 x_a0] ++ [] from rfl)
    otherwise ⟨hl_27⟩ using hn_a0 hl_24 hl_25 hl_26
  group_none hinv4 hG with ⟨hl_24, hl_25, hl_26, hl_27⟩

theorem cases_0_7_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    cases_0_7_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_typeof.case_28 x_a0, EoCases.__eo_typeof.case_29 x_a0, EoCases.__eo_typeof.case_30 x_a0, EoCases.__eo_typeof.case_31 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_28 x_a0 = none ∧ EoCases.__eo_typeof.case_29 x_a0 = none ∧ EoCases.__eo_typeof.case_30 x_a0 = none ∧ EoCases.__eo_typeof.case_31 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_7_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  group_step with case_28_eo__24eo_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_28 x_a0, EoCases.__eo_typeof.case_29 x_a0, EoCases.__eo_typeof.case_30 x_a0, EoCases.__eo_typeof.case_31 x_a0] = [] ++ [EoCases.__eo_typeof.case_28 x_a0] ++ [EoCases.__eo_typeof.case_29 x_a0, EoCases.__eo_typeof.case_30 x_a0, EoCases.__eo_typeof.case_31 x_a0] from rfl)
    otherwise ⟨hl_28⟩ using hn_a0
  group_step with case_29_eo__24eo_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_28 x_a0, EoCases.__eo_typeof.case_29 x_a0, EoCases.__eo_typeof.case_30 x_a0, EoCases.__eo_typeof.case_31 x_a0] = [EoCases.__eo_typeof.case_28 x_a0] ++ [EoCases.__eo_typeof.case_29 x_a0] ++ [EoCases.__eo_typeof.case_30 x_a0, EoCases.__eo_typeof.case_31 x_a0] from rfl)
    otherwise ⟨hl_29⟩ using hn_a0 hl_28
  group_step with case_30_eo__24eo_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_28 x_a0, EoCases.__eo_typeof.case_29 x_a0, EoCases.__eo_typeof.case_30 x_a0, EoCases.__eo_typeof.case_31 x_a0] = [EoCases.__eo_typeof.case_28 x_a0, EoCases.__eo_typeof.case_29 x_a0] ++ [EoCases.__eo_typeof.case_30 x_a0] ++ [EoCases.__eo_typeof.case_31 x_a0] from rfl)
    otherwise ⟨hl_30⟩ using hn_a0 hl_28 hl_29
  group_step with case_31_eo__24eo_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_28 x_a0, EoCases.__eo_typeof.case_29 x_a0, EoCases.__eo_typeof.case_30 x_a0, EoCases.__eo_typeof.case_31 x_a0] = [EoCases.__eo_typeof.case_28 x_a0, EoCases.__eo_typeof.case_29 x_a0, EoCases.__eo_typeof.case_30 x_a0] ++ [EoCases.__eo_typeof.case_31 x_a0] ++ [] from rfl)
    otherwise ⟨hl_31⟩ using hn_a0 hl_28 hl_29 hl_30
  group_none hinv4 hG with ⟨hl_28, hl_29, hl_30, hl_31⟩

theorem cases_0_8_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    cases_0_8_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_typeof.case_32 x_a0, EoCases.__eo_typeof.case_33 x_a0, EoCases.__eo_typeof.case_34 x_a0, EoCases.__eo_typeof.case_35 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_32 x_a0 = none ∧ EoCases.__eo_typeof.case_33 x_a0 = none ∧ EoCases.__eo_typeof.case_34 x_a0 = none ∧ EoCases.__eo_typeof.case_35 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_8_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  group_step with case_32_eo__24eo_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_32 x_a0, EoCases.__eo_typeof.case_33 x_a0, EoCases.__eo_typeof.case_34 x_a0, EoCases.__eo_typeof.case_35 x_a0] = [] ++ [EoCases.__eo_typeof.case_32 x_a0] ++ [EoCases.__eo_typeof.case_33 x_a0, EoCases.__eo_typeof.case_34 x_a0, EoCases.__eo_typeof.case_35 x_a0] from rfl)
    otherwise ⟨hl_32⟩ using hn_a0
  group_step with case_33_eo__24eo_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_32 x_a0, EoCases.__eo_typeof.case_33 x_a0, EoCases.__eo_typeof.case_34 x_a0, EoCases.__eo_typeof.case_35 x_a0] = [EoCases.__eo_typeof.case_32 x_a0] ++ [EoCases.__eo_typeof.case_33 x_a0] ++ [EoCases.__eo_typeof.case_34 x_a0, EoCases.__eo_typeof.case_35 x_a0] from rfl)
    otherwise ⟨hl_33⟩ using hn_a0 hl_32
  group_step with case_34_eo__24eo_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_32 x_a0, EoCases.__eo_typeof.case_33 x_a0, EoCases.__eo_typeof.case_34 x_a0, EoCases.__eo_typeof.case_35 x_a0] = [EoCases.__eo_typeof.case_32 x_a0, EoCases.__eo_typeof.case_33 x_a0] ++ [EoCases.__eo_typeof.case_34 x_a0] ++ [EoCases.__eo_typeof.case_35 x_a0] from rfl)
    otherwise ⟨hl_34⟩ using hn_a0 hl_32 hl_33
  group_step with case_35_eo__24eo_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_32 x_a0, EoCases.__eo_typeof.case_33 x_a0, EoCases.__eo_typeof.case_34 x_a0, EoCases.__eo_typeof.case_35 x_a0] = [EoCases.__eo_typeof.case_32 x_a0, EoCases.__eo_typeof.case_33 x_a0, EoCases.__eo_typeof.case_34 x_a0] ++ [EoCases.__eo_typeof.case_35 x_a0] ++ [] from rfl)
    otherwise ⟨hl_35⟩ using hn_a0 hl_32 hl_33 hl_34
  group_none hinv4 hG with ⟨hl_32, hl_33, hl_34, hl_35⟩

theorem cases_0_9_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    cases_0_9_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_typeof.case_36 x_a0, EoCases.__eo_typeof.case_37 x_a0, EoCases.__eo_typeof.case_38 x_a0, EoCases.__eo_typeof.case_39 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_36 x_a0 = none ∧ EoCases.__eo_typeof.case_37 x_a0 = none ∧ EoCases.__eo_typeof.case_38 x_a0 = none ∧ EoCases.__eo_typeof.case_39 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_9_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  group_step with case_36_eo__24eo_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_36 x_a0, EoCases.__eo_typeof.case_37 x_a0, EoCases.__eo_typeof.case_38 x_a0, EoCases.__eo_typeof.case_39 x_a0] = [] ++ [EoCases.__eo_typeof.case_36 x_a0] ++ [EoCases.__eo_typeof.case_37 x_a0, EoCases.__eo_typeof.case_38 x_a0, EoCases.__eo_typeof.case_39 x_a0] from rfl)
    otherwise ⟨hl_36⟩ using hn_a0
  group_step with case_37_eo__24eo_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_36 x_a0, EoCases.__eo_typeof.case_37 x_a0, EoCases.__eo_typeof.case_38 x_a0, EoCases.__eo_typeof.case_39 x_a0] = [EoCases.__eo_typeof.case_36 x_a0] ++ [EoCases.__eo_typeof.case_37 x_a0] ++ [EoCases.__eo_typeof.case_38 x_a0, EoCases.__eo_typeof.case_39 x_a0] from rfl)
    otherwise ⟨hl_37⟩ using hn_a0 hl_36
  group_step with case_38_eo__24eo_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_36 x_a0, EoCases.__eo_typeof.case_37 x_a0, EoCases.__eo_typeof.case_38 x_a0, EoCases.__eo_typeof.case_39 x_a0] = [EoCases.__eo_typeof.case_36 x_a0, EoCases.__eo_typeof.case_37 x_a0] ++ [EoCases.__eo_typeof.case_38 x_a0] ++ [EoCases.__eo_typeof.case_39 x_a0] from rfl)
    otherwise ⟨hl_38⟩ using hn_a0 hl_36 hl_37
  group_step with case_39_eo__24eo_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_36 x_a0, EoCases.__eo_typeof.case_37 x_a0, EoCases.__eo_typeof.case_38 x_a0, EoCases.__eo_typeof.case_39 x_a0] = [EoCases.__eo_typeof.case_36 x_a0, EoCases.__eo_typeof.case_37 x_a0, EoCases.__eo_typeof.case_38 x_a0] ++ [EoCases.__eo_typeof.case_39 x_a0] ++ [] from rfl)
    otherwise ⟨hl_39⟩ using hn_a0 hl_36 hl_37 hl_38
  group_none hinv4 hG with ⟨hl_36, hl_37, hl_38, hl_39⟩

theorem cases_0_10_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    cases_0_10_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_typeof.case_40 x_a0, EoCases.__eo_typeof.case_41 x_a0, EoCases.__eo_typeof.case_42 x_a0, EoCases.__eo_typeof.case_43 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_40 x_a0 = none ∧ EoCases.__eo_typeof.case_41 x_a0 = none ∧ EoCases.__eo_typeof.case_42 x_a0 = none ∧ EoCases.__eo_typeof.case_43 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_10_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  group_step with case_40_eo__24eo_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_40 x_a0, EoCases.__eo_typeof.case_41 x_a0, EoCases.__eo_typeof.case_42 x_a0, EoCases.__eo_typeof.case_43 x_a0] = [] ++ [EoCases.__eo_typeof.case_40 x_a0] ++ [EoCases.__eo_typeof.case_41 x_a0, EoCases.__eo_typeof.case_42 x_a0, EoCases.__eo_typeof.case_43 x_a0] from rfl)
    otherwise ⟨hl_40⟩ using hn_a0
  group_step with case_41_eo__24eo_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_40 x_a0, EoCases.__eo_typeof.case_41 x_a0, EoCases.__eo_typeof.case_42 x_a0, EoCases.__eo_typeof.case_43 x_a0] = [EoCases.__eo_typeof.case_40 x_a0] ++ [EoCases.__eo_typeof.case_41 x_a0] ++ [EoCases.__eo_typeof.case_42 x_a0, EoCases.__eo_typeof.case_43 x_a0] from rfl)
    otherwise ⟨hl_41⟩ using hn_a0 hl_40
  group_step with case_42_eo__24eo_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_40 x_a0, EoCases.__eo_typeof.case_41 x_a0, EoCases.__eo_typeof.case_42 x_a0, EoCases.__eo_typeof.case_43 x_a0] = [EoCases.__eo_typeof.case_40 x_a0, EoCases.__eo_typeof.case_41 x_a0] ++ [EoCases.__eo_typeof.case_42 x_a0] ++ [EoCases.__eo_typeof.case_43 x_a0] from rfl)
    otherwise ⟨hl_42⟩ using hn_a0 hl_40 hl_41
  group_step with case_43_eo__24eo_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_40 x_a0, EoCases.__eo_typeof.case_41 x_a0, EoCases.__eo_typeof.case_42 x_a0, EoCases.__eo_typeof.case_43 x_a0] = [EoCases.__eo_typeof.case_40 x_a0, EoCases.__eo_typeof.case_41 x_a0, EoCases.__eo_typeof.case_42 x_a0] ++ [EoCases.__eo_typeof.case_43 x_a0] ++ [] from rfl)
    otherwise ⟨hl_43⟩ using hn_a0 hl_40 hl_41 hl_42
  group_none hinv4 hG with ⟨hl_40, hl_41, hl_42, hl_43⟩

theorem cases_0_11_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    cases_0_11_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_typeof.case_44 x_a0, EoCases.__eo_typeof.case_45 x_a0, EoCases.__eo_typeof.case_46 x_a0, EoCases.__eo_typeof.case_47 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_44 x_a0 = none ∧ EoCases.__eo_typeof.case_45 x_a0 = none ∧ EoCases.__eo_typeof.case_46 x_a0 = none ∧ EoCases.__eo_typeof.case_47 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_11_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  group_step with case_44_eo__24eo_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_44 x_a0, EoCases.__eo_typeof.case_45 x_a0, EoCases.__eo_typeof.case_46 x_a0, EoCases.__eo_typeof.case_47 x_a0] = [] ++ [EoCases.__eo_typeof.case_44 x_a0] ++ [EoCases.__eo_typeof.case_45 x_a0, EoCases.__eo_typeof.case_46 x_a0, EoCases.__eo_typeof.case_47 x_a0] from rfl)
    otherwise ⟨hl_44⟩ using hn_a0
  group_step with case_45_eo__24eo_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_44 x_a0, EoCases.__eo_typeof.case_45 x_a0, EoCases.__eo_typeof.case_46 x_a0, EoCases.__eo_typeof.case_47 x_a0] = [EoCases.__eo_typeof.case_44 x_a0] ++ [EoCases.__eo_typeof.case_45 x_a0] ++ [EoCases.__eo_typeof.case_46 x_a0, EoCases.__eo_typeof.case_47 x_a0] from rfl)
    otherwise ⟨hl_45⟩ using hn_a0 hl_44
  group_step with case_46_eo__24eo_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_44 x_a0, EoCases.__eo_typeof.case_45 x_a0, EoCases.__eo_typeof.case_46 x_a0, EoCases.__eo_typeof.case_47 x_a0] = [EoCases.__eo_typeof.case_44 x_a0, EoCases.__eo_typeof.case_45 x_a0] ++ [EoCases.__eo_typeof.case_46 x_a0] ++ [EoCases.__eo_typeof.case_47 x_a0] from rfl)
    otherwise ⟨hl_46⟩ using hn_a0 hl_44 hl_45
  group_step with case_47_eo__24eo_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_44 x_a0, EoCases.__eo_typeof.case_45 x_a0, EoCases.__eo_typeof.case_46 x_a0, EoCases.__eo_typeof.case_47 x_a0] = [EoCases.__eo_typeof.case_44 x_a0, EoCases.__eo_typeof.case_45 x_a0, EoCases.__eo_typeof.case_46 x_a0] ++ [EoCases.__eo_typeof.case_47 x_a0] ++ [] from rfl)
    otherwise ⟨hl_47⟩ using hn_a0 hl_44 hl_45 hl_46
  group_none hinv4 hG with ⟨hl_44, hl_45, hl_46, hl_47⟩

theorem cases_0_12_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    cases_0_12_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_typeof.case_48 x_a0, EoCases.__eo_typeof.case_49 x_a0, EoCases.__eo_typeof.case_50 x_a0, EoCases.__eo_typeof.case_51 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_48 x_a0 = none ∧ EoCases.__eo_typeof.case_49 x_a0 = none ∧ EoCases.__eo_typeof.case_50 x_a0 = none ∧ EoCases.__eo_typeof.case_51 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_12_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  group_step with case_48_eo__24eo_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_48 x_a0, EoCases.__eo_typeof.case_49 x_a0, EoCases.__eo_typeof.case_50 x_a0, EoCases.__eo_typeof.case_51 x_a0] = [] ++ [EoCases.__eo_typeof.case_48 x_a0] ++ [EoCases.__eo_typeof.case_49 x_a0, EoCases.__eo_typeof.case_50 x_a0, EoCases.__eo_typeof.case_51 x_a0] from rfl)
    otherwise ⟨hl_48⟩ using hn_a0
  group_step with case_49_eo__24eo_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_48 x_a0, EoCases.__eo_typeof.case_49 x_a0, EoCases.__eo_typeof.case_50 x_a0, EoCases.__eo_typeof.case_51 x_a0] = [EoCases.__eo_typeof.case_48 x_a0] ++ [EoCases.__eo_typeof.case_49 x_a0] ++ [EoCases.__eo_typeof.case_50 x_a0, EoCases.__eo_typeof.case_51 x_a0] from rfl)
    otherwise ⟨hl_49⟩ using hn_a0 hl_48
  group_step with case_50_eo__24eo_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_48 x_a0, EoCases.__eo_typeof.case_49 x_a0, EoCases.__eo_typeof.case_50 x_a0, EoCases.__eo_typeof.case_51 x_a0] = [EoCases.__eo_typeof.case_48 x_a0, EoCases.__eo_typeof.case_49 x_a0] ++ [EoCases.__eo_typeof.case_50 x_a0] ++ [EoCases.__eo_typeof.case_51 x_a0] from rfl)
    otherwise ⟨hl_50⟩ using hn_a0 hl_48 hl_49
  group_step with case_51_eo__24eo_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_48 x_a0, EoCases.__eo_typeof.case_49 x_a0, EoCases.__eo_typeof.case_50 x_a0, EoCases.__eo_typeof.case_51 x_a0] = [EoCases.__eo_typeof.case_48 x_a0, EoCases.__eo_typeof.case_49 x_a0, EoCases.__eo_typeof.case_50 x_a0] ++ [EoCases.__eo_typeof.case_51 x_a0] ++ [] from rfl)
    otherwise ⟨hl_51⟩ using hn_a0 hl_48 hl_49 hl_50
  group_none hinv4 hG with ⟨hl_48, hl_49, hl_50, hl_51⟩

theorem cases_0_13_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    cases_0_13_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_typeof.case_52 x_a0, EoCases.__eo_typeof.case_53 x_a0, EoCases.__eo_typeof.case_54 x_a0, EoCases.__eo_typeof.case_55 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_52 x_a0 = none ∧ EoCases.__eo_typeof.case_53 x_a0 = none ∧ EoCases.__eo_typeof.case_54 x_a0 = none ∧ EoCases.__eo_typeof.case_55 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_13_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  group_step with case_52_eo__24eo_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_52 x_a0, EoCases.__eo_typeof.case_53 x_a0, EoCases.__eo_typeof.case_54 x_a0, EoCases.__eo_typeof.case_55 x_a0] = [] ++ [EoCases.__eo_typeof.case_52 x_a0] ++ [EoCases.__eo_typeof.case_53 x_a0, EoCases.__eo_typeof.case_54 x_a0, EoCases.__eo_typeof.case_55 x_a0] from rfl)
    otherwise ⟨hl_52⟩ using hn_a0
  group_step with case_53_eo__24eo_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_52 x_a0, EoCases.__eo_typeof.case_53 x_a0, EoCases.__eo_typeof.case_54 x_a0, EoCases.__eo_typeof.case_55 x_a0] = [EoCases.__eo_typeof.case_52 x_a0] ++ [EoCases.__eo_typeof.case_53 x_a0] ++ [EoCases.__eo_typeof.case_54 x_a0, EoCases.__eo_typeof.case_55 x_a0] from rfl)
    otherwise ⟨hl_53⟩ using hn_a0 hl_52
  group_step with case_54_eo__24eo_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_52 x_a0, EoCases.__eo_typeof.case_53 x_a0, EoCases.__eo_typeof.case_54 x_a0, EoCases.__eo_typeof.case_55 x_a0] = [EoCases.__eo_typeof.case_52 x_a0, EoCases.__eo_typeof.case_53 x_a0] ++ [EoCases.__eo_typeof.case_54 x_a0] ++ [EoCases.__eo_typeof.case_55 x_a0] from rfl)
    otherwise ⟨hl_54⟩ using hn_a0 hl_52 hl_53
  group_step with case_55_eo__24eo_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_52 x_a0, EoCases.__eo_typeof.case_53 x_a0, EoCases.__eo_typeof.case_54 x_a0, EoCases.__eo_typeof.case_55 x_a0] = [EoCases.__eo_typeof.case_52 x_a0, EoCases.__eo_typeof.case_53 x_a0, EoCases.__eo_typeof.case_54 x_a0] ++ [EoCases.__eo_typeof.case_55 x_a0] ++ [] from rfl)
    otherwise ⟨hl_55⟩ using hn_a0 hl_52 hl_53 hl_54
  group_none hinv4 hG with ⟨hl_52, hl_53, hl_54, hl_55⟩

theorem cases_0_14_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    cases_0_14_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_typeof.case_56 x_a0, EoCases.__eo_typeof.case_57 x_a0, EoCases.__eo_typeof.case_58 x_a0, EoCases.__eo_typeof.case_59 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_56 x_a0 = none ∧ EoCases.__eo_typeof.case_57 x_a0 = none ∧ EoCases.__eo_typeof.case_58 x_a0 = none ∧ EoCases.__eo_typeof.case_59 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_14_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  group_step with case_56_eo__24eo_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_56 x_a0, EoCases.__eo_typeof.case_57 x_a0, EoCases.__eo_typeof.case_58 x_a0, EoCases.__eo_typeof.case_59 x_a0] = [] ++ [EoCases.__eo_typeof.case_56 x_a0] ++ [EoCases.__eo_typeof.case_57 x_a0, EoCases.__eo_typeof.case_58 x_a0, EoCases.__eo_typeof.case_59 x_a0] from rfl)
    otherwise ⟨hl_56⟩ using hn_a0
  group_step with case_57_eo__24eo_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_56 x_a0, EoCases.__eo_typeof.case_57 x_a0, EoCases.__eo_typeof.case_58 x_a0, EoCases.__eo_typeof.case_59 x_a0] = [EoCases.__eo_typeof.case_56 x_a0] ++ [EoCases.__eo_typeof.case_57 x_a0] ++ [EoCases.__eo_typeof.case_58 x_a0, EoCases.__eo_typeof.case_59 x_a0] from rfl)
    otherwise ⟨hl_57⟩ using hn_a0 hl_56
  group_step with case_58_eo__24eo_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_56 x_a0, EoCases.__eo_typeof.case_57 x_a0, EoCases.__eo_typeof.case_58 x_a0, EoCases.__eo_typeof.case_59 x_a0] = [EoCases.__eo_typeof.case_56 x_a0, EoCases.__eo_typeof.case_57 x_a0] ++ [EoCases.__eo_typeof.case_58 x_a0] ++ [EoCases.__eo_typeof.case_59 x_a0] from rfl)
    otherwise ⟨hl_58⟩ using hn_a0 hl_56 hl_57
  group_step with case_59_eo__24eo_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_56 x_a0, EoCases.__eo_typeof.case_57 x_a0, EoCases.__eo_typeof.case_58 x_a0, EoCases.__eo_typeof.case_59 x_a0] = [EoCases.__eo_typeof.case_56 x_a0, EoCases.__eo_typeof.case_57 x_a0, EoCases.__eo_typeof.case_58 x_a0] ++ [EoCases.__eo_typeof.case_59 x_a0] ++ [] from rfl)
    otherwise ⟨hl_59⟩ using hn_a0 hl_56 hl_57 hl_58
  group_none hinv4 hG with ⟨hl_56, hl_57, hl_58, hl_59⟩

theorem cases_0_15_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    cases_0_15_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_typeof.case_60 x_a0, EoCases.__eo_typeof.case_61 x_a0, EoCases.__eo_typeof.case_62 x_a0, EoCases.__eo_typeof.case_63 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_60 x_a0 = none ∧ EoCases.__eo_typeof.case_61 x_a0 = none ∧ EoCases.__eo_typeof.case_62 x_a0 = none ∧ EoCases.__eo_typeof.case_63 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_15_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  group_step with case_60_eo__24eo_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_60 x_a0, EoCases.__eo_typeof.case_61 x_a0, EoCases.__eo_typeof.case_62 x_a0, EoCases.__eo_typeof.case_63 x_a0] = [] ++ [EoCases.__eo_typeof.case_60 x_a0] ++ [EoCases.__eo_typeof.case_61 x_a0, EoCases.__eo_typeof.case_62 x_a0, EoCases.__eo_typeof.case_63 x_a0] from rfl)
    otherwise ⟨hl_60⟩ using hn_a0
  group_step with case_61_eo__24eo_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_60 x_a0, EoCases.__eo_typeof.case_61 x_a0, EoCases.__eo_typeof.case_62 x_a0, EoCases.__eo_typeof.case_63 x_a0] = [EoCases.__eo_typeof.case_60 x_a0] ++ [EoCases.__eo_typeof.case_61 x_a0] ++ [EoCases.__eo_typeof.case_62 x_a0, EoCases.__eo_typeof.case_63 x_a0] from rfl)
    otherwise ⟨hl_61⟩ using hn_a0 hl_60
  group_step with case_62_eo__24eo_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_60 x_a0, EoCases.__eo_typeof.case_61 x_a0, EoCases.__eo_typeof.case_62 x_a0, EoCases.__eo_typeof.case_63 x_a0] = [EoCases.__eo_typeof.case_60 x_a0, EoCases.__eo_typeof.case_61 x_a0] ++ [EoCases.__eo_typeof.case_62 x_a0] ++ [EoCases.__eo_typeof.case_63 x_a0] from rfl)
    otherwise ⟨hl_62⟩ using hn_a0 hl_60 hl_61
  group_step with case_63_eo__24eo_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_60 x_a0, EoCases.__eo_typeof.case_61 x_a0, EoCases.__eo_typeof.case_62 x_a0, EoCases.__eo_typeof.case_63 x_a0] = [EoCases.__eo_typeof.case_60 x_a0, EoCases.__eo_typeof.case_61 x_a0, EoCases.__eo_typeof.case_62 x_a0] ++ [EoCases.__eo_typeof.case_63 x_a0] ++ [] from rfl)
    otherwise ⟨hl_63⟩ using hn_a0 hl_60 hl_61 hl_62
  group_none hinv4 hG with ⟨hl_60, hl_61, hl_62, hl_63⟩

theorem cases_0_16_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    cases_0_16_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_typeof.case_64 x_a0, EoCases.__eo_typeof.case_65 x_a0, EoCases.__eo_typeof.case_66 x_a0, EoCases.__eo_typeof.case_67 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_64 x_a0 = none ∧ EoCases.__eo_typeof.case_65 x_a0 = none ∧ EoCases.__eo_typeof.case_66 x_a0 = none ∧ EoCases.__eo_typeof.case_67 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_16_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  group_step with case_64_eo__24eo_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_64 x_a0, EoCases.__eo_typeof.case_65 x_a0, EoCases.__eo_typeof.case_66 x_a0, EoCases.__eo_typeof.case_67 x_a0] = [] ++ [EoCases.__eo_typeof.case_64 x_a0] ++ [EoCases.__eo_typeof.case_65 x_a0, EoCases.__eo_typeof.case_66 x_a0, EoCases.__eo_typeof.case_67 x_a0] from rfl)
    otherwise ⟨hl_64⟩ using hn_a0
  group_step with case_65_eo__24eo_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_64 x_a0, EoCases.__eo_typeof.case_65 x_a0, EoCases.__eo_typeof.case_66 x_a0, EoCases.__eo_typeof.case_67 x_a0] = [EoCases.__eo_typeof.case_64 x_a0] ++ [EoCases.__eo_typeof.case_65 x_a0] ++ [EoCases.__eo_typeof.case_66 x_a0, EoCases.__eo_typeof.case_67 x_a0] from rfl)
    otherwise ⟨hl_65⟩ using hn_a0 hl_64
  group_step with case_66_eo__24eo_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_64 x_a0, EoCases.__eo_typeof.case_65 x_a0, EoCases.__eo_typeof.case_66 x_a0, EoCases.__eo_typeof.case_67 x_a0] = [EoCases.__eo_typeof.case_64 x_a0, EoCases.__eo_typeof.case_65 x_a0] ++ [EoCases.__eo_typeof.case_66 x_a0] ++ [EoCases.__eo_typeof.case_67 x_a0] from rfl)
    otherwise ⟨hl_66⟩ using hn_a0 hl_64 hl_65
  group_step with case_67_eo__24eo_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_64 x_a0, EoCases.__eo_typeof.case_65 x_a0, EoCases.__eo_typeof.case_66 x_a0, EoCases.__eo_typeof.case_67 x_a0] = [EoCases.__eo_typeof.case_64 x_a0, EoCases.__eo_typeof.case_65 x_a0, EoCases.__eo_typeof.case_66 x_a0] ++ [EoCases.__eo_typeof.case_67 x_a0] ++ [] from rfl)
    otherwise ⟨hl_67⟩ using hn_a0 hl_64 hl_65 hl_66
  group_none hinv4 hG with ⟨hl_64, hl_65, hl_66, hl_67⟩

theorem cases_0_17_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    cases_0_17_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_typeof.case_68 x_a0, EoCases.__eo_typeof.case_69 x_a0, EoCases.__eo_typeof.case_70 x_a0, EoCases.__eo_typeof.case_71 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_68 x_a0 = none ∧ EoCases.__eo_typeof.case_69 x_a0 = none ∧ EoCases.__eo_typeof.case_70 x_a0 = none ∧ EoCases.__eo_typeof.case_71 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_17_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  group_step with case_68_eo__24eo_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_68 x_a0, EoCases.__eo_typeof.case_69 x_a0, EoCases.__eo_typeof.case_70 x_a0, EoCases.__eo_typeof.case_71 x_a0] = [] ++ [EoCases.__eo_typeof.case_68 x_a0] ++ [EoCases.__eo_typeof.case_69 x_a0, EoCases.__eo_typeof.case_70 x_a0, EoCases.__eo_typeof.case_71 x_a0] from rfl)
    otherwise ⟨hl_68⟩ using hn_a0
  group_step with case_69_eo__24eo_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_68 x_a0, EoCases.__eo_typeof.case_69 x_a0, EoCases.__eo_typeof.case_70 x_a0, EoCases.__eo_typeof.case_71 x_a0] = [EoCases.__eo_typeof.case_68 x_a0] ++ [EoCases.__eo_typeof.case_69 x_a0] ++ [EoCases.__eo_typeof.case_70 x_a0, EoCases.__eo_typeof.case_71 x_a0] from rfl)
    otherwise ⟨hl_69⟩ using hn_a0 hl_68
  group_step with case_70_eo__24eo_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_68 x_a0, EoCases.__eo_typeof.case_69 x_a0, EoCases.__eo_typeof.case_70 x_a0, EoCases.__eo_typeof.case_71 x_a0] = [EoCases.__eo_typeof.case_68 x_a0, EoCases.__eo_typeof.case_69 x_a0] ++ [EoCases.__eo_typeof.case_70 x_a0] ++ [EoCases.__eo_typeof.case_71 x_a0] from rfl)
    otherwise ⟨hl_70⟩ using hn_a0 hl_68 hl_69
  group_step with case_71_eo__24eo_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_68 x_a0, EoCases.__eo_typeof.case_69 x_a0, EoCases.__eo_typeof.case_70 x_a0, EoCases.__eo_typeof.case_71 x_a0] = [EoCases.__eo_typeof.case_68 x_a0, EoCases.__eo_typeof.case_69 x_a0, EoCases.__eo_typeof.case_70 x_a0] ++ [EoCases.__eo_typeof.case_71 x_a0] ++ [] from rfl)
    otherwise ⟨hl_71⟩ using hn_a0 hl_68 hl_69 hl_70
  group_none hinv4 hG with ⟨hl_68, hl_69, hl_70, hl_71⟩

theorem cases_0_18_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    cases_0_18_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_typeof.case_72 x_a0, EoCases.__eo_typeof.case_73 x_a0, EoCases.__eo_typeof.case_74 x_a0, EoCases.__eo_typeof.case_75 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_72 x_a0 = none ∧ EoCases.__eo_typeof.case_73 x_a0 = none ∧ EoCases.__eo_typeof.case_74 x_a0 = none ∧ EoCases.__eo_typeof.case_75 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_18_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  group_step with case_72_eo__24eo_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_72 x_a0, EoCases.__eo_typeof.case_73 x_a0, EoCases.__eo_typeof.case_74 x_a0, EoCases.__eo_typeof.case_75 x_a0] = [] ++ [EoCases.__eo_typeof.case_72 x_a0] ++ [EoCases.__eo_typeof.case_73 x_a0, EoCases.__eo_typeof.case_74 x_a0, EoCases.__eo_typeof.case_75 x_a0] from rfl)
    otherwise ⟨hl_72⟩ using hn_a0
  group_step with case_73_eo__24eo_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_72 x_a0, EoCases.__eo_typeof.case_73 x_a0, EoCases.__eo_typeof.case_74 x_a0, EoCases.__eo_typeof.case_75 x_a0] = [EoCases.__eo_typeof.case_72 x_a0] ++ [EoCases.__eo_typeof.case_73 x_a0] ++ [EoCases.__eo_typeof.case_74 x_a0, EoCases.__eo_typeof.case_75 x_a0] from rfl)
    otherwise ⟨hl_73⟩ using hn_a0 hl_72
  group_step with case_74_eo__24eo_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_72 x_a0, EoCases.__eo_typeof.case_73 x_a0, EoCases.__eo_typeof.case_74 x_a0, EoCases.__eo_typeof.case_75 x_a0] = [EoCases.__eo_typeof.case_72 x_a0, EoCases.__eo_typeof.case_73 x_a0] ++ [EoCases.__eo_typeof.case_74 x_a0] ++ [EoCases.__eo_typeof.case_75 x_a0] from rfl)
    otherwise ⟨hl_74⟩ using hn_a0 hl_72 hl_73
  group_step with case_75_eo__24eo_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_72 x_a0, EoCases.__eo_typeof.case_73 x_a0, EoCases.__eo_typeof.case_74 x_a0, EoCases.__eo_typeof.case_75 x_a0] = [EoCases.__eo_typeof.case_72 x_a0, EoCases.__eo_typeof.case_73 x_a0, EoCases.__eo_typeof.case_74 x_a0] ++ [EoCases.__eo_typeof.case_75 x_a0] ++ [] from rfl)
    otherwise ⟨hl_75⟩ using hn_a0 hl_72 hl_73 hl_74
  group_none hinv4 hG with ⟨hl_72, hl_73, hl_74, hl_75⟩

theorem cases_0_19_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    cases_0_19_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_typeof.case_76 x_a0, EoCases.__eo_typeof.case_77 x_a0, EoCases.__eo_typeof.case_78 x_a0, EoCases.__eo_typeof.case_79 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_76 x_a0 = none ∧ EoCases.__eo_typeof.case_77 x_a0 = none ∧ EoCases.__eo_typeof.case_78 x_a0 = none ∧ EoCases.__eo_typeof.case_79 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_19_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  group_step with case_76_eo__24eo_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_76 x_a0, EoCases.__eo_typeof.case_77 x_a0, EoCases.__eo_typeof.case_78 x_a0, EoCases.__eo_typeof.case_79 x_a0] = [] ++ [EoCases.__eo_typeof.case_76 x_a0] ++ [EoCases.__eo_typeof.case_77 x_a0, EoCases.__eo_typeof.case_78 x_a0, EoCases.__eo_typeof.case_79 x_a0] from rfl)
    otherwise ⟨hl_76⟩ using hn_a0
  group_step with case_77_eo__24eo_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_76 x_a0, EoCases.__eo_typeof.case_77 x_a0, EoCases.__eo_typeof.case_78 x_a0, EoCases.__eo_typeof.case_79 x_a0] = [EoCases.__eo_typeof.case_76 x_a0] ++ [EoCases.__eo_typeof.case_77 x_a0] ++ [EoCases.__eo_typeof.case_78 x_a0, EoCases.__eo_typeof.case_79 x_a0] from rfl)
    otherwise ⟨hl_77⟩ using hn_a0 hl_76
  group_step with case_78_eo__24eo_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_76 x_a0, EoCases.__eo_typeof.case_77 x_a0, EoCases.__eo_typeof.case_78 x_a0, EoCases.__eo_typeof.case_79 x_a0] = [EoCases.__eo_typeof.case_76 x_a0, EoCases.__eo_typeof.case_77 x_a0] ++ [EoCases.__eo_typeof.case_78 x_a0] ++ [EoCases.__eo_typeof.case_79 x_a0] from rfl)
    otherwise ⟨hl_78⟩ using hn_a0 hl_76 hl_77
  group_step with case_79_eo__24eo_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_76 x_a0, EoCases.__eo_typeof.case_77 x_a0, EoCases.__eo_typeof.case_78 x_a0, EoCases.__eo_typeof.case_79 x_a0] = [EoCases.__eo_typeof.case_76 x_a0, EoCases.__eo_typeof.case_77 x_a0, EoCases.__eo_typeof.case_78 x_a0] ++ [EoCases.__eo_typeof.case_79 x_a0] ++ [] from rfl)
    otherwise ⟨hl_79⟩ using hn_a0 hl_76 hl_77 hl_78
  group_none hinv4 hG with ⟨hl_76, hl_77, hl_78, hl_79⟩

theorem cases_0_20_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    cases_0_20_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_typeof.case_80 x_a0, EoCases.__eo_typeof.case_81 x_a0, EoCases.__eo_typeof.case_82 x_a0, EoCases.__eo_typeof.case_83 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_80 x_a0 = none ∧ EoCases.__eo_typeof.case_81 x_a0 = none ∧ EoCases.__eo_typeof.case_82 x_a0 = none ∧ EoCases.__eo_typeof.case_83 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_20_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  group_step with case_80_eo__24eo_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_80 x_a0, EoCases.__eo_typeof.case_81 x_a0, EoCases.__eo_typeof.case_82 x_a0, EoCases.__eo_typeof.case_83 x_a0] = [] ++ [EoCases.__eo_typeof.case_80 x_a0] ++ [EoCases.__eo_typeof.case_81 x_a0, EoCases.__eo_typeof.case_82 x_a0, EoCases.__eo_typeof.case_83 x_a0] from rfl)
    otherwise ⟨hl_80⟩ using hn_a0
  group_step with case_81_eo__24eo_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_80 x_a0, EoCases.__eo_typeof.case_81 x_a0, EoCases.__eo_typeof.case_82 x_a0, EoCases.__eo_typeof.case_83 x_a0] = [EoCases.__eo_typeof.case_80 x_a0] ++ [EoCases.__eo_typeof.case_81 x_a0] ++ [EoCases.__eo_typeof.case_82 x_a0, EoCases.__eo_typeof.case_83 x_a0] from rfl)
    otherwise ⟨hl_81⟩ using hn_a0 hl_80
  group_step with case_82_eo__24eo_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_80 x_a0, EoCases.__eo_typeof.case_81 x_a0, EoCases.__eo_typeof.case_82 x_a0, EoCases.__eo_typeof.case_83 x_a0] = [EoCases.__eo_typeof.case_80 x_a0, EoCases.__eo_typeof.case_81 x_a0] ++ [EoCases.__eo_typeof.case_82 x_a0] ++ [EoCases.__eo_typeof.case_83 x_a0] from rfl)
    otherwise ⟨hl_82⟩ using hn_a0 hl_80 hl_81
  group_step with case_83_eo__24eo_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_80 x_a0, EoCases.__eo_typeof.case_81 x_a0, EoCases.__eo_typeof.case_82 x_a0, EoCases.__eo_typeof.case_83 x_a0] = [EoCases.__eo_typeof.case_80 x_a0, EoCases.__eo_typeof.case_81 x_a0, EoCases.__eo_typeof.case_82 x_a0] ++ [EoCases.__eo_typeof.case_83 x_a0] ++ [] from rfl)
    otherwise ⟨hl_83⟩ using hn_a0 hl_80 hl_81 hl_82
  group_none hinv4 hG with ⟨hl_80, hl_81, hl_82, hl_83⟩

theorem cases_0_21_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    cases_0_21_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_typeof.case_84 x_a0, EoCases.__eo_typeof.case_85 x_a0, EoCases.__eo_typeof.case_86 x_a0, EoCases.__eo_typeof.case_87 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_84 x_a0 = none ∧ EoCases.__eo_typeof.case_85 x_a0 = none ∧ EoCases.__eo_typeof.case_86 x_a0 = none ∧ EoCases.__eo_typeof.case_87 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_21_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  group_step with case_84_eo__24eo_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_84 x_a0, EoCases.__eo_typeof.case_85 x_a0, EoCases.__eo_typeof.case_86 x_a0, EoCases.__eo_typeof.case_87 x_a0] = [] ++ [EoCases.__eo_typeof.case_84 x_a0] ++ [EoCases.__eo_typeof.case_85 x_a0, EoCases.__eo_typeof.case_86 x_a0, EoCases.__eo_typeof.case_87 x_a0] from rfl)
    otherwise ⟨hl_84⟩ using hn_a0
  group_step with case_85_eo__24eo_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_84 x_a0, EoCases.__eo_typeof.case_85 x_a0, EoCases.__eo_typeof.case_86 x_a0, EoCases.__eo_typeof.case_87 x_a0] = [EoCases.__eo_typeof.case_84 x_a0] ++ [EoCases.__eo_typeof.case_85 x_a0] ++ [EoCases.__eo_typeof.case_86 x_a0, EoCases.__eo_typeof.case_87 x_a0] from rfl)
    otherwise ⟨hl_85⟩ using hn_a0 hl_84
  group_step with case_86_eo__24eo_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_84 x_a0, EoCases.__eo_typeof.case_85 x_a0, EoCases.__eo_typeof.case_86 x_a0, EoCases.__eo_typeof.case_87 x_a0] = [EoCases.__eo_typeof.case_84 x_a0, EoCases.__eo_typeof.case_85 x_a0] ++ [EoCases.__eo_typeof.case_86 x_a0] ++ [EoCases.__eo_typeof.case_87 x_a0] from rfl)
    otherwise ⟨hl_86⟩ using hn_a0 hl_84 hl_85
  group_step with case_87_eo__24eo_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_84 x_a0, EoCases.__eo_typeof.case_85 x_a0, EoCases.__eo_typeof.case_86 x_a0, EoCases.__eo_typeof.case_87 x_a0] = [EoCases.__eo_typeof.case_84 x_a0, EoCases.__eo_typeof.case_85 x_a0, EoCases.__eo_typeof.case_86 x_a0] ++ [EoCases.__eo_typeof.case_87 x_a0] ++ [] from rfl)
    otherwise ⟨hl_87⟩ using hn_a0 hl_84 hl_85 hl_86
  group_none hinv4 hG with ⟨hl_84, hl_85, hl_86, hl_87⟩

theorem cases_0_22_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    cases_0_22_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_typeof.case_88 x_a0, EoCases.__eo_typeof.case_89 x_a0, EoCases.__eo_typeof.case_90 x_a0, EoCases.__eo_typeof.case_91 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_88 x_a0 = none ∧ EoCases.__eo_typeof.case_89 x_a0 = none ∧ EoCases.__eo_typeof.case_90 x_a0 = none ∧ EoCases.__eo_typeof.case_91 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_22_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  group_step with case_88_eo__24eo_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_88 x_a0, EoCases.__eo_typeof.case_89 x_a0, EoCases.__eo_typeof.case_90 x_a0, EoCases.__eo_typeof.case_91 x_a0] = [] ++ [EoCases.__eo_typeof.case_88 x_a0] ++ [EoCases.__eo_typeof.case_89 x_a0, EoCases.__eo_typeof.case_90 x_a0, EoCases.__eo_typeof.case_91 x_a0] from rfl)
    otherwise ⟨hl_88⟩ using hn_a0
  group_step with case_89_eo__24eo_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_88 x_a0, EoCases.__eo_typeof.case_89 x_a0, EoCases.__eo_typeof.case_90 x_a0, EoCases.__eo_typeof.case_91 x_a0] = [EoCases.__eo_typeof.case_88 x_a0] ++ [EoCases.__eo_typeof.case_89 x_a0] ++ [EoCases.__eo_typeof.case_90 x_a0, EoCases.__eo_typeof.case_91 x_a0] from rfl)
    otherwise ⟨hl_89⟩ using hn_a0 hl_88
  group_step with case_90_eo__24eo_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_88 x_a0, EoCases.__eo_typeof.case_89 x_a0, EoCases.__eo_typeof.case_90 x_a0, EoCases.__eo_typeof.case_91 x_a0] = [EoCases.__eo_typeof.case_88 x_a0, EoCases.__eo_typeof.case_89 x_a0] ++ [EoCases.__eo_typeof.case_90 x_a0] ++ [EoCases.__eo_typeof.case_91 x_a0] from rfl)
    otherwise ⟨hl_90⟩ using hn_a0 hl_88 hl_89
  group_step with case_91_eo__24eo_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_88 x_a0, EoCases.__eo_typeof.case_89 x_a0, EoCases.__eo_typeof.case_90 x_a0, EoCases.__eo_typeof.case_91 x_a0] = [EoCases.__eo_typeof.case_88 x_a0, EoCases.__eo_typeof.case_89 x_a0, EoCases.__eo_typeof.case_90 x_a0] ++ [EoCases.__eo_typeof.case_91 x_a0] ++ [] from rfl)
    otherwise ⟨hl_91⟩ using hn_a0 hl_88 hl_89 hl_90
  group_none hinv4 hG with ⟨hl_88, hl_89, hl_90, hl_91⟩

theorem cases_0_23_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    cases_0_23_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_typeof.case_92 x_a0, EoCases.__eo_typeof.case_93 x_a0, EoCases.__eo_typeof.case_94 x_a0, EoCases.__eo_typeof.case_95 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_92 x_a0 = none ∧ EoCases.__eo_typeof.case_93 x_a0 = none ∧ EoCases.__eo_typeof.case_94 x_a0 = none ∧ EoCases.__eo_typeof.case_95 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_23_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  group_step with case_92_eo__24eo_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_92 x_a0, EoCases.__eo_typeof.case_93 x_a0, EoCases.__eo_typeof.case_94 x_a0, EoCases.__eo_typeof.case_95 x_a0] = [] ++ [EoCases.__eo_typeof.case_92 x_a0] ++ [EoCases.__eo_typeof.case_93 x_a0, EoCases.__eo_typeof.case_94 x_a0, EoCases.__eo_typeof.case_95 x_a0] from rfl)
    otherwise ⟨hl_92⟩ using hn_a0
  group_step with case_93_eo__24eo_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_92 x_a0, EoCases.__eo_typeof.case_93 x_a0, EoCases.__eo_typeof.case_94 x_a0, EoCases.__eo_typeof.case_95 x_a0] = [EoCases.__eo_typeof.case_92 x_a0] ++ [EoCases.__eo_typeof.case_93 x_a0] ++ [EoCases.__eo_typeof.case_94 x_a0, EoCases.__eo_typeof.case_95 x_a0] from rfl)
    otherwise ⟨hl_93⟩ using hn_a0 hl_92
  group_step with case_94_eo__24eo_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_92 x_a0, EoCases.__eo_typeof.case_93 x_a0, EoCases.__eo_typeof.case_94 x_a0, EoCases.__eo_typeof.case_95 x_a0] = [EoCases.__eo_typeof.case_92 x_a0, EoCases.__eo_typeof.case_93 x_a0] ++ [EoCases.__eo_typeof.case_94 x_a0] ++ [EoCases.__eo_typeof.case_95 x_a0] from rfl)
    otherwise ⟨hl_94⟩ using hn_a0 hl_92 hl_93
  group_step with case_95_eo__24eo_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_92 x_a0, EoCases.__eo_typeof.case_93 x_a0, EoCases.__eo_typeof.case_94 x_a0, EoCases.__eo_typeof.case_95 x_a0] = [EoCases.__eo_typeof.case_92 x_a0, EoCases.__eo_typeof.case_93 x_a0, EoCases.__eo_typeof.case_94 x_a0] ++ [EoCases.__eo_typeof.case_95 x_a0] ++ [] from rfl)
    otherwise ⟨hl_95⟩ using hn_a0 hl_92 hl_93 hl_94
  group_none hinv4 hG with ⟨hl_92, hl_93, hl_94, hl_95⟩

theorem cases_0_24_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    cases_0_24_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_typeof.case_96 x_a0, EoCases.__eo_typeof.case_97 x_a0, EoCases.__eo_typeof.case_98 x_a0, EoCases.__eo_typeof.case_99 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_96 x_a0 = none ∧ EoCases.__eo_typeof.case_97 x_a0 = none ∧ EoCases.__eo_typeof.case_98 x_a0 = none ∧ EoCases.__eo_typeof.case_99 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_24_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  group_step with case_96_eo__24eo_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_96 x_a0, EoCases.__eo_typeof.case_97 x_a0, EoCases.__eo_typeof.case_98 x_a0, EoCases.__eo_typeof.case_99 x_a0] = [] ++ [EoCases.__eo_typeof.case_96 x_a0] ++ [EoCases.__eo_typeof.case_97 x_a0, EoCases.__eo_typeof.case_98 x_a0, EoCases.__eo_typeof.case_99 x_a0] from rfl)
    otherwise ⟨hl_96⟩ using hn_a0
  group_step with case_97_eo__24eo_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_96 x_a0, EoCases.__eo_typeof.case_97 x_a0, EoCases.__eo_typeof.case_98 x_a0, EoCases.__eo_typeof.case_99 x_a0] = [EoCases.__eo_typeof.case_96 x_a0] ++ [EoCases.__eo_typeof.case_97 x_a0] ++ [EoCases.__eo_typeof.case_98 x_a0, EoCases.__eo_typeof.case_99 x_a0] from rfl)
    otherwise ⟨hl_97⟩ using hn_a0 hl_96
  group_step with case_98_eo__24eo_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_96 x_a0, EoCases.__eo_typeof.case_97 x_a0, EoCases.__eo_typeof.case_98 x_a0, EoCases.__eo_typeof.case_99 x_a0] = [EoCases.__eo_typeof.case_96 x_a0, EoCases.__eo_typeof.case_97 x_a0] ++ [EoCases.__eo_typeof.case_98 x_a0] ++ [EoCases.__eo_typeof.case_99 x_a0] from rfl)
    otherwise ⟨hl_98⟩ using hn_a0 hl_96 hl_97
  group_step with case_99_eo__24eo_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_96 x_a0, EoCases.__eo_typeof.case_97 x_a0, EoCases.__eo_typeof.case_98 x_a0, EoCases.__eo_typeof.case_99 x_a0] = [EoCases.__eo_typeof.case_96 x_a0, EoCases.__eo_typeof.case_97 x_a0, EoCases.__eo_typeof.case_98 x_a0] ++ [EoCases.__eo_typeof.case_99 x_a0] ++ [] from rfl)
    otherwise ⟨hl_99⟩ using hn_a0 hl_96 hl_97 hl_98
  group_none hinv4 hG with ⟨hl_96, hl_97, hl_98, hl_99⟩

theorem cases_0_25_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    cases_0_25_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_typeof.case_100 x_a0, EoCases.__eo_typeof.case_101 x_a0, EoCases.__eo_typeof.case_102 x_a0, EoCases.__eo_typeof.case_103 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_100 x_a0 = none ∧ EoCases.__eo_typeof.case_101 x_a0 = none ∧ EoCases.__eo_typeof.case_102 x_a0 = none ∧ EoCases.__eo_typeof.case_103 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_25_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  group_step with case_100_eo__24eo_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_100 x_a0, EoCases.__eo_typeof.case_101 x_a0, EoCases.__eo_typeof.case_102 x_a0, EoCases.__eo_typeof.case_103 x_a0] = [] ++ [EoCases.__eo_typeof.case_100 x_a0] ++ [EoCases.__eo_typeof.case_101 x_a0, EoCases.__eo_typeof.case_102 x_a0, EoCases.__eo_typeof.case_103 x_a0] from rfl)
    otherwise ⟨hl_100⟩ using hn_a0
  group_step with case_101_eo__24eo_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_100 x_a0, EoCases.__eo_typeof.case_101 x_a0, EoCases.__eo_typeof.case_102 x_a0, EoCases.__eo_typeof.case_103 x_a0] = [EoCases.__eo_typeof.case_100 x_a0] ++ [EoCases.__eo_typeof.case_101 x_a0] ++ [EoCases.__eo_typeof.case_102 x_a0, EoCases.__eo_typeof.case_103 x_a0] from rfl)
    otherwise ⟨hl_101⟩ using hn_a0 hl_100
  group_step with case_102_eo__24eo_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_100 x_a0, EoCases.__eo_typeof.case_101 x_a0, EoCases.__eo_typeof.case_102 x_a0, EoCases.__eo_typeof.case_103 x_a0] = [EoCases.__eo_typeof.case_100 x_a0, EoCases.__eo_typeof.case_101 x_a0] ++ [EoCases.__eo_typeof.case_102 x_a0] ++ [EoCases.__eo_typeof.case_103 x_a0] from rfl)
    otherwise ⟨hl_102⟩ using hn_a0 hl_100 hl_101
  group_step with case_103_eo__24eo_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_100 x_a0, EoCases.__eo_typeof.case_101 x_a0, EoCases.__eo_typeof.case_102 x_a0, EoCases.__eo_typeof.case_103 x_a0] = [EoCases.__eo_typeof.case_100 x_a0, EoCases.__eo_typeof.case_101 x_a0, EoCases.__eo_typeof.case_102 x_a0] ++ [EoCases.__eo_typeof.case_103 x_a0] ++ [] from rfl)
    otherwise ⟨hl_103⟩ using hn_a0 hl_100 hl_101 hl_102
  group_none hinv4 hG with ⟨hl_100, hl_101, hl_102, hl_103⟩

theorem cases_0_26_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    cases_0_26_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_typeof.case_104 x_a0, EoCases.__eo_typeof.case_105 x_a0, EoCases.__eo_typeof.case_106 x_a0, EoCases.__eo_typeof.case_107 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_104 x_a0 = none ∧ EoCases.__eo_typeof.case_105 x_a0 = none ∧ EoCases.__eo_typeof.case_106 x_a0 = none ∧ EoCases.__eo_typeof.case_107 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_26_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  group_step with case_104_eo__24eo_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_104 x_a0, EoCases.__eo_typeof.case_105 x_a0, EoCases.__eo_typeof.case_106 x_a0, EoCases.__eo_typeof.case_107 x_a0] = [] ++ [EoCases.__eo_typeof.case_104 x_a0] ++ [EoCases.__eo_typeof.case_105 x_a0, EoCases.__eo_typeof.case_106 x_a0, EoCases.__eo_typeof.case_107 x_a0] from rfl)
    otherwise ⟨hl_104⟩ using hn_a0
  group_step with case_105_eo__24eo_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_104 x_a0, EoCases.__eo_typeof.case_105 x_a0, EoCases.__eo_typeof.case_106 x_a0, EoCases.__eo_typeof.case_107 x_a0] = [EoCases.__eo_typeof.case_104 x_a0] ++ [EoCases.__eo_typeof.case_105 x_a0] ++ [EoCases.__eo_typeof.case_106 x_a0, EoCases.__eo_typeof.case_107 x_a0] from rfl)
    otherwise ⟨hl_105⟩ using hn_a0 hl_104
  group_step with case_106_eo__24eo_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_104 x_a0, EoCases.__eo_typeof.case_105 x_a0, EoCases.__eo_typeof.case_106 x_a0, EoCases.__eo_typeof.case_107 x_a0] = [EoCases.__eo_typeof.case_104 x_a0, EoCases.__eo_typeof.case_105 x_a0] ++ [EoCases.__eo_typeof.case_106 x_a0] ++ [EoCases.__eo_typeof.case_107 x_a0] from rfl)
    otherwise ⟨hl_106⟩ using hn_a0 hl_104 hl_105
  group_step with case_107_eo__24eo_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_104 x_a0, EoCases.__eo_typeof.case_105 x_a0, EoCases.__eo_typeof.case_106 x_a0, EoCases.__eo_typeof.case_107 x_a0] = [EoCases.__eo_typeof.case_104 x_a0, EoCases.__eo_typeof.case_105 x_a0, EoCases.__eo_typeof.case_106 x_a0] ++ [EoCases.__eo_typeof.case_107 x_a0] ++ [] from rfl)
    otherwise ⟨hl_107⟩ using hn_a0 hl_104 hl_105 hl_106
  group_none hinv4 hG with ⟨hl_104, hl_105, hl_106, hl_107⟩

theorem cases_0_27_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    cases_0_27_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_typeof.case_108 x_a0, EoCases.__eo_typeof.case_109 x_a0, EoCases.__eo_typeof.case_110 x_a0, EoCases.__eo_typeof.case_111 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_108 x_a0 = none ∧ EoCases.__eo_typeof.case_109 x_a0 = none ∧ EoCases.__eo_typeof.case_110 x_a0 = none ∧ EoCases.__eo_typeof.case_111 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_27_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  group_step with case_108_eo__24eo_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_108 x_a0, EoCases.__eo_typeof.case_109 x_a0, EoCases.__eo_typeof.case_110 x_a0, EoCases.__eo_typeof.case_111 x_a0] = [] ++ [EoCases.__eo_typeof.case_108 x_a0] ++ [EoCases.__eo_typeof.case_109 x_a0, EoCases.__eo_typeof.case_110 x_a0, EoCases.__eo_typeof.case_111 x_a0] from rfl)
    otherwise ⟨hl_108⟩ using hn_a0
  group_step with case_109_eo__24eo_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_108 x_a0, EoCases.__eo_typeof.case_109 x_a0, EoCases.__eo_typeof.case_110 x_a0, EoCases.__eo_typeof.case_111 x_a0] = [EoCases.__eo_typeof.case_108 x_a0] ++ [EoCases.__eo_typeof.case_109 x_a0] ++ [EoCases.__eo_typeof.case_110 x_a0, EoCases.__eo_typeof.case_111 x_a0] from rfl)
    otherwise ⟨hl_109⟩ using hn_a0 hl_108
  group_step with case_110_eo__24eo_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_108 x_a0, EoCases.__eo_typeof.case_109 x_a0, EoCases.__eo_typeof.case_110 x_a0, EoCases.__eo_typeof.case_111 x_a0] = [EoCases.__eo_typeof.case_108 x_a0, EoCases.__eo_typeof.case_109 x_a0] ++ [EoCases.__eo_typeof.case_110 x_a0] ++ [EoCases.__eo_typeof.case_111 x_a0] from rfl)
    otherwise ⟨hl_110⟩ using hn_a0 hl_108 hl_109
  group_step with case_111_eo__24eo_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_108 x_a0, EoCases.__eo_typeof.case_109 x_a0, EoCases.__eo_typeof.case_110 x_a0, EoCases.__eo_typeof.case_111 x_a0] = [EoCases.__eo_typeof.case_108 x_a0, EoCases.__eo_typeof.case_109 x_a0, EoCases.__eo_typeof.case_110 x_a0] ++ [EoCases.__eo_typeof.case_111 x_a0] ++ [] from rfl)
    otherwise ⟨hl_111⟩ using hn_a0 hl_108 hl_109 hl_110
  group_none hinv4 hG with ⟨hl_108, hl_109, hl_110, hl_111⟩

theorem cases_0_28_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    cases_0_28_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_typeof.case_112 x_a0, EoCases.__eo_typeof.case_113 x_a0, EoCases.__eo_typeof.case_114 x_a0, EoCases.__eo_typeof.case_115 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_112 x_a0 = none ∧ EoCases.__eo_typeof.case_113 x_a0 = none ∧ EoCases.__eo_typeof.case_114 x_a0 = none ∧ EoCases.__eo_typeof.case_115 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_28_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  group_step with case_112_eo__24eo_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_112 x_a0, EoCases.__eo_typeof.case_113 x_a0, EoCases.__eo_typeof.case_114 x_a0, EoCases.__eo_typeof.case_115 x_a0] = [] ++ [EoCases.__eo_typeof.case_112 x_a0] ++ [EoCases.__eo_typeof.case_113 x_a0, EoCases.__eo_typeof.case_114 x_a0, EoCases.__eo_typeof.case_115 x_a0] from rfl)
    otherwise ⟨hl_112⟩ using hn_a0
  group_step with case_113_eo__24eo_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_112 x_a0, EoCases.__eo_typeof.case_113 x_a0, EoCases.__eo_typeof.case_114 x_a0, EoCases.__eo_typeof.case_115 x_a0] = [EoCases.__eo_typeof.case_112 x_a0] ++ [EoCases.__eo_typeof.case_113 x_a0] ++ [EoCases.__eo_typeof.case_114 x_a0, EoCases.__eo_typeof.case_115 x_a0] from rfl)
    otherwise ⟨hl_113⟩ using hn_a0 hl_112
  group_step with case_114_eo__24eo_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_112 x_a0, EoCases.__eo_typeof.case_113 x_a0, EoCases.__eo_typeof.case_114 x_a0, EoCases.__eo_typeof.case_115 x_a0] = [EoCases.__eo_typeof.case_112 x_a0, EoCases.__eo_typeof.case_113 x_a0] ++ [EoCases.__eo_typeof.case_114 x_a0] ++ [EoCases.__eo_typeof.case_115 x_a0] from rfl)
    otherwise ⟨hl_114⟩ using hn_a0 hl_112 hl_113
  group_step with case_115_eo__24eo_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_112 x_a0, EoCases.__eo_typeof.case_113 x_a0, EoCases.__eo_typeof.case_114 x_a0, EoCases.__eo_typeof.case_115 x_a0] = [EoCases.__eo_typeof.case_112 x_a0, EoCases.__eo_typeof.case_113 x_a0, EoCases.__eo_typeof.case_114 x_a0] ++ [EoCases.__eo_typeof.case_115 x_a0] ++ [] from rfl)
    otherwise ⟨hl_115⟩ using hn_a0 hl_112 hl_113 hl_114
  group_none hinv4 hG with ⟨hl_112, hl_113, hl_114, hl_115⟩

theorem cases_0_29_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    cases_0_29_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_typeof.case_116 x_a0, EoCases.__eo_typeof.case_117 x_a0, EoCases.__eo_typeof.case_118 x_a0, EoCases.__eo_typeof.case_119 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_116 x_a0 = none ∧ EoCases.__eo_typeof.case_117 x_a0 = none ∧ EoCases.__eo_typeof.case_118 x_a0 = none ∧ EoCases.__eo_typeof.case_119 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_29_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  group_step with case_116_eo__24eo_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_116 x_a0, EoCases.__eo_typeof.case_117 x_a0, EoCases.__eo_typeof.case_118 x_a0, EoCases.__eo_typeof.case_119 x_a0] = [] ++ [EoCases.__eo_typeof.case_116 x_a0] ++ [EoCases.__eo_typeof.case_117 x_a0, EoCases.__eo_typeof.case_118 x_a0, EoCases.__eo_typeof.case_119 x_a0] from rfl)
    otherwise ⟨hl_116⟩ using hn_a0
  group_step with case_117_eo__24eo_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_116 x_a0, EoCases.__eo_typeof.case_117 x_a0, EoCases.__eo_typeof.case_118 x_a0, EoCases.__eo_typeof.case_119 x_a0] = [EoCases.__eo_typeof.case_116 x_a0] ++ [EoCases.__eo_typeof.case_117 x_a0] ++ [EoCases.__eo_typeof.case_118 x_a0, EoCases.__eo_typeof.case_119 x_a0] from rfl)
    otherwise ⟨hl_117⟩ using hn_a0 hl_116
  group_step with case_118_eo__24eo_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_116 x_a0, EoCases.__eo_typeof.case_117 x_a0, EoCases.__eo_typeof.case_118 x_a0, EoCases.__eo_typeof.case_119 x_a0] = [EoCases.__eo_typeof.case_116 x_a0, EoCases.__eo_typeof.case_117 x_a0] ++ [EoCases.__eo_typeof.case_118 x_a0] ++ [EoCases.__eo_typeof.case_119 x_a0] from rfl)
    otherwise ⟨hl_118⟩ using hn_a0 hl_116 hl_117
  group_step with case_119_eo__24eo_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_116 x_a0, EoCases.__eo_typeof.case_117 x_a0, EoCases.__eo_typeof.case_118 x_a0, EoCases.__eo_typeof.case_119 x_a0] = [EoCases.__eo_typeof.case_116 x_a0, EoCases.__eo_typeof.case_117 x_a0, EoCases.__eo_typeof.case_118 x_a0] ++ [EoCases.__eo_typeof.case_119 x_a0] ++ [] from rfl)
    otherwise ⟨hl_119⟩ using hn_a0 hl_116 hl_117 hl_118
  group_none hinv4 hG with ⟨hl_116, hl_117, hl_118, hl_119⟩

theorem cases_0_30_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    cases_0_30_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_typeof.case_120 x_a0, EoCases.__eo_typeof.case_121 x_a0, EoCases.__eo_typeof.case_122 x_a0, EoCases.__eo_typeof.case_123 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_120 x_a0 = none ∧ EoCases.__eo_typeof.case_121 x_a0 = none ∧ EoCases.__eo_typeof.case_122 x_a0 = none ∧ EoCases.__eo_typeof.case_123 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_30_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  group_step with case_120_eo__24eo_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_120 x_a0, EoCases.__eo_typeof.case_121 x_a0, EoCases.__eo_typeof.case_122 x_a0, EoCases.__eo_typeof.case_123 x_a0] = [] ++ [EoCases.__eo_typeof.case_120 x_a0] ++ [EoCases.__eo_typeof.case_121 x_a0, EoCases.__eo_typeof.case_122 x_a0, EoCases.__eo_typeof.case_123 x_a0] from rfl)
    otherwise ⟨hl_120⟩ using hn_a0
  group_step with case_121_eo__24eo_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_120 x_a0, EoCases.__eo_typeof.case_121 x_a0, EoCases.__eo_typeof.case_122 x_a0, EoCases.__eo_typeof.case_123 x_a0] = [EoCases.__eo_typeof.case_120 x_a0] ++ [EoCases.__eo_typeof.case_121 x_a0] ++ [EoCases.__eo_typeof.case_122 x_a0, EoCases.__eo_typeof.case_123 x_a0] from rfl)
    otherwise ⟨hl_121⟩ using hn_a0 hl_120
  group_step with case_122_eo__24eo_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_120 x_a0, EoCases.__eo_typeof.case_121 x_a0, EoCases.__eo_typeof.case_122 x_a0, EoCases.__eo_typeof.case_123 x_a0] = [EoCases.__eo_typeof.case_120 x_a0, EoCases.__eo_typeof.case_121 x_a0] ++ [EoCases.__eo_typeof.case_122 x_a0] ++ [EoCases.__eo_typeof.case_123 x_a0] from rfl)
    otherwise ⟨hl_122⟩ using hn_a0 hl_120 hl_121
  group_step with case_123_eo__24eo_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_120 x_a0, EoCases.__eo_typeof.case_121 x_a0, EoCases.__eo_typeof.case_122 x_a0, EoCases.__eo_typeof.case_123 x_a0] = [EoCases.__eo_typeof.case_120 x_a0, EoCases.__eo_typeof.case_121 x_a0, EoCases.__eo_typeof.case_122 x_a0] ++ [EoCases.__eo_typeof.case_123 x_a0] ++ [] from rfl)
    otherwise ⟨hl_123⟩ using hn_a0 hl_120 hl_121 hl_122
  group_none hinv4 hG with ⟨hl_120, hl_121, hl_122, hl_123⟩

theorem cases_0_31_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    cases_0_31_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_typeof.case_124 x_a0, EoCases.__eo_typeof.case_125 x_a0, EoCases.__eo_typeof.case_126 x_a0, EoCases.__eo_typeof.case_127 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_124 x_a0 = none ∧ EoCases.__eo_typeof.case_125 x_a0 = none ∧ EoCases.__eo_typeof.case_126 x_a0 = none ∧ EoCases.__eo_typeof.case_127 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_31_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  group_step with case_124_eo__24eo_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_124 x_a0, EoCases.__eo_typeof.case_125 x_a0, EoCases.__eo_typeof.case_126 x_a0, EoCases.__eo_typeof.case_127 x_a0] = [] ++ [EoCases.__eo_typeof.case_124 x_a0] ++ [EoCases.__eo_typeof.case_125 x_a0, EoCases.__eo_typeof.case_126 x_a0, EoCases.__eo_typeof.case_127 x_a0] from rfl)
    otherwise ⟨hl_124⟩ using hn_a0
  group_step with case_125_eo__24eo_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_124 x_a0, EoCases.__eo_typeof.case_125 x_a0, EoCases.__eo_typeof.case_126 x_a0, EoCases.__eo_typeof.case_127 x_a0] = [EoCases.__eo_typeof.case_124 x_a0] ++ [EoCases.__eo_typeof.case_125 x_a0] ++ [EoCases.__eo_typeof.case_126 x_a0, EoCases.__eo_typeof.case_127 x_a0] from rfl)
    otherwise ⟨hl_125⟩ using hn_a0 hl_124
  group_step with case_126_eo__24eo_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_124 x_a0, EoCases.__eo_typeof.case_125 x_a0, EoCases.__eo_typeof.case_126 x_a0, EoCases.__eo_typeof.case_127 x_a0] = [EoCases.__eo_typeof.case_124 x_a0, EoCases.__eo_typeof.case_125 x_a0] ++ [EoCases.__eo_typeof.case_126 x_a0] ++ [EoCases.__eo_typeof.case_127 x_a0] from rfl)
    otherwise ⟨hl_126⟩ using hn_a0 hl_124 hl_125
  group_step with case_127_eo__24eo_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_124 x_a0, EoCases.__eo_typeof.case_125 x_a0, EoCases.__eo_typeof.case_126 x_a0, EoCases.__eo_typeof.case_127 x_a0] = [EoCases.__eo_typeof.case_124 x_a0, EoCases.__eo_typeof.case_125 x_a0, EoCases.__eo_typeof.case_126 x_a0] ++ [EoCases.__eo_typeof.case_127 x_a0] ++ [] from rfl)
    otherwise ⟨hl_127⟩ using hn_a0 hl_124 hl_125 hl_126
  group_none hinv4 hG with ⟨hl_124, hl_125, hl_126, hl_127⟩

theorem cases_0_32_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    cases_0_32_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_typeof.case_128 x_a0, EoCases.__eo_typeof.case_129 x_a0, EoCases.__eo_typeof.case_130 x_a0, EoCases.__eo_typeof.case_131 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_128 x_a0 = none ∧ EoCases.__eo_typeof.case_129 x_a0 = none ∧ EoCases.__eo_typeof.case_130 x_a0 = none ∧ EoCases.__eo_typeof.case_131 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_32_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  group_step with case_128_eo__24eo_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_128 x_a0, EoCases.__eo_typeof.case_129 x_a0, EoCases.__eo_typeof.case_130 x_a0, EoCases.__eo_typeof.case_131 x_a0] = [] ++ [EoCases.__eo_typeof.case_128 x_a0] ++ [EoCases.__eo_typeof.case_129 x_a0, EoCases.__eo_typeof.case_130 x_a0, EoCases.__eo_typeof.case_131 x_a0] from rfl)
    otherwise ⟨hl_128⟩ using hn_a0
  group_step with case_129_eo__24eo_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_128 x_a0, EoCases.__eo_typeof.case_129 x_a0, EoCases.__eo_typeof.case_130 x_a0, EoCases.__eo_typeof.case_131 x_a0] = [EoCases.__eo_typeof.case_128 x_a0] ++ [EoCases.__eo_typeof.case_129 x_a0] ++ [EoCases.__eo_typeof.case_130 x_a0, EoCases.__eo_typeof.case_131 x_a0] from rfl)
    otherwise ⟨hl_129⟩ using hn_a0 hl_128
  group_step with case_130_eo__24eo_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_128 x_a0, EoCases.__eo_typeof.case_129 x_a0, EoCases.__eo_typeof.case_130 x_a0, EoCases.__eo_typeof.case_131 x_a0] = [EoCases.__eo_typeof.case_128 x_a0, EoCases.__eo_typeof.case_129 x_a0] ++ [EoCases.__eo_typeof.case_130 x_a0] ++ [EoCases.__eo_typeof.case_131 x_a0] from rfl)
    otherwise ⟨hl_130⟩ using hn_a0 hl_128 hl_129
  group_step with case_131_eo__24eo_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_128 x_a0, EoCases.__eo_typeof.case_129 x_a0, EoCases.__eo_typeof.case_130 x_a0, EoCases.__eo_typeof.case_131 x_a0] = [EoCases.__eo_typeof.case_128 x_a0, EoCases.__eo_typeof.case_129 x_a0, EoCases.__eo_typeof.case_130 x_a0] ++ [EoCases.__eo_typeof.case_131 x_a0] ++ [] from rfl)
    otherwise ⟨hl_131⟩ using hn_a0 hl_128 hl_129 hl_130
  group_none hinv4 hG with ⟨hl_128, hl_129, hl_130, hl_131⟩

theorem cases_0_33_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    cases_0_33_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_typeof.case_132 x_a0, EoCases.__eo_typeof.case_133 x_a0, EoCases.__eo_typeof.case_134 x_a0, EoCases.__eo_typeof.case_135 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_132 x_a0 = none ∧ EoCases.__eo_typeof.case_133 x_a0 = none ∧ EoCases.__eo_typeof.case_134 x_a0 = none ∧ EoCases.__eo_typeof.case_135 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_33_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  group_step with case_132_eo__24eo_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_132 x_a0, EoCases.__eo_typeof.case_133 x_a0, EoCases.__eo_typeof.case_134 x_a0, EoCases.__eo_typeof.case_135 x_a0] = [] ++ [EoCases.__eo_typeof.case_132 x_a0] ++ [EoCases.__eo_typeof.case_133 x_a0, EoCases.__eo_typeof.case_134 x_a0, EoCases.__eo_typeof.case_135 x_a0] from rfl)
    otherwise ⟨hl_132⟩ using hn_a0
  group_step with case_133_eo__24eo_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_132 x_a0, EoCases.__eo_typeof.case_133 x_a0, EoCases.__eo_typeof.case_134 x_a0, EoCases.__eo_typeof.case_135 x_a0] = [EoCases.__eo_typeof.case_132 x_a0] ++ [EoCases.__eo_typeof.case_133 x_a0] ++ [EoCases.__eo_typeof.case_134 x_a0, EoCases.__eo_typeof.case_135 x_a0] from rfl)
    otherwise ⟨hl_133⟩ using hn_a0 hl_132
  group_step with case_134_eo__24eo_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_132 x_a0, EoCases.__eo_typeof.case_133 x_a0, EoCases.__eo_typeof.case_134 x_a0, EoCases.__eo_typeof.case_135 x_a0] = [EoCases.__eo_typeof.case_132 x_a0, EoCases.__eo_typeof.case_133 x_a0] ++ [EoCases.__eo_typeof.case_134 x_a0] ++ [EoCases.__eo_typeof.case_135 x_a0] from rfl)
    otherwise ⟨hl_134⟩ using hn_a0 hl_132 hl_133
  group_step with case_135_eo__24eo_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_132 x_a0, EoCases.__eo_typeof.case_133 x_a0, EoCases.__eo_typeof.case_134 x_a0, EoCases.__eo_typeof.case_135 x_a0] = [EoCases.__eo_typeof.case_132 x_a0, EoCases.__eo_typeof.case_133 x_a0, EoCases.__eo_typeof.case_134 x_a0] ++ [EoCases.__eo_typeof.case_135 x_a0] ++ [] from rfl)
    otherwise ⟨hl_135⟩ using hn_a0 hl_132 hl_133 hl_134
  group_none hinv4 hG with ⟨hl_132, hl_133, hl_134, hl_135⟩

theorem cases_0_34_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    cases_0_34_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_typeof.case_136 x_a0, EoCases.__eo_typeof.case_137 x_a0, EoCases.__eo_typeof.case_138 x_a0, EoCases.__eo_typeof.case_139 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_136 x_a0 = none ∧ EoCases.__eo_typeof.case_137 x_a0 = none ∧ EoCases.__eo_typeof.case_138 x_a0 = none ∧ EoCases.__eo_typeof.case_139 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_34_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  group_step with case_136_eo__24eo_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_136 x_a0, EoCases.__eo_typeof.case_137 x_a0, EoCases.__eo_typeof.case_138 x_a0, EoCases.__eo_typeof.case_139 x_a0] = [] ++ [EoCases.__eo_typeof.case_136 x_a0] ++ [EoCases.__eo_typeof.case_137 x_a0, EoCases.__eo_typeof.case_138 x_a0, EoCases.__eo_typeof.case_139 x_a0] from rfl)
    otherwise ⟨hl_136⟩ using hn_a0
  group_step with case_137_eo__24eo_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_136 x_a0, EoCases.__eo_typeof.case_137 x_a0, EoCases.__eo_typeof.case_138 x_a0, EoCases.__eo_typeof.case_139 x_a0] = [EoCases.__eo_typeof.case_136 x_a0] ++ [EoCases.__eo_typeof.case_137 x_a0] ++ [EoCases.__eo_typeof.case_138 x_a0, EoCases.__eo_typeof.case_139 x_a0] from rfl)
    otherwise ⟨hl_137⟩ using hn_a0 hl_136
  group_step with case_138_eo__24eo_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_136 x_a0, EoCases.__eo_typeof.case_137 x_a0, EoCases.__eo_typeof.case_138 x_a0, EoCases.__eo_typeof.case_139 x_a0] = [EoCases.__eo_typeof.case_136 x_a0, EoCases.__eo_typeof.case_137 x_a0] ++ [EoCases.__eo_typeof.case_138 x_a0] ++ [EoCases.__eo_typeof.case_139 x_a0] from rfl)
    otherwise ⟨hl_138⟩ using hn_a0 hl_136 hl_137
  group_step with case_139_eo__24eo_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_136 x_a0, EoCases.__eo_typeof.case_137 x_a0, EoCases.__eo_typeof.case_138 x_a0, EoCases.__eo_typeof.case_139 x_a0] = [EoCases.__eo_typeof.case_136 x_a0, EoCases.__eo_typeof.case_137 x_a0, EoCases.__eo_typeof.case_138 x_a0] ++ [EoCases.__eo_typeof.case_139 x_a0] ++ [] from rfl)
    otherwise ⟨hl_139⟩ using hn_a0 hl_136 hl_137 hl_138
  group_none hinv4 hG with ⟨hl_136, hl_137, hl_138, hl_139⟩

theorem cases_0_35_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    cases_0_35_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_typeof.case_140 x_a0, EoCases.__eo_typeof.case_141 x_a0, EoCases.__eo_typeof.case_142 x_a0, EoCases.__eo_typeof.case_143 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_140 x_a0 = none ∧ EoCases.__eo_typeof.case_141 x_a0 = none ∧ EoCases.__eo_typeof.case_142 x_a0 = none ∧ EoCases.__eo_typeof.case_143 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_35_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  group_step with case_140_eo__24eo_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_140 x_a0, EoCases.__eo_typeof.case_141 x_a0, EoCases.__eo_typeof.case_142 x_a0, EoCases.__eo_typeof.case_143 x_a0] = [] ++ [EoCases.__eo_typeof.case_140 x_a0] ++ [EoCases.__eo_typeof.case_141 x_a0, EoCases.__eo_typeof.case_142 x_a0, EoCases.__eo_typeof.case_143 x_a0] from rfl)
    otherwise ⟨hl_140⟩ using hn_a0
  group_step with case_141_eo__24eo_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_140 x_a0, EoCases.__eo_typeof.case_141 x_a0, EoCases.__eo_typeof.case_142 x_a0, EoCases.__eo_typeof.case_143 x_a0] = [EoCases.__eo_typeof.case_140 x_a0] ++ [EoCases.__eo_typeof.case_141 x_a0] ++ [EoCases.__eo_typeof.case_142 x_a0, EoCases.__eo_typeof.case_143 x_a0] from rfl)
    otherwise ⟨hl_141⟩ using hn_a0 hl_140
  group_step with case_142_eo__24eo_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_140 x_a0, EoCases.__eo_typeof.case_141 x_a0, EoCases.__eo_typeof.case_142 x_a0, EoCases.__eo_typeof.case_143 x_a0] = [EoCases.__eo_typeof.case_140 x_a0, EoCases.__eo_typeof.case_141 x_a0] ++ [EoCases.__eo_typeof.case_142 x_a0] ++ [EoCases.__eo_typeof.case_143 x_a0] from rfl)
    otherwise ⟨hl_142⟩ using hn_a0 hl_140 hl_141
  group_step with case_143_eo__24eo_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_140 x_a0, EoCases.__eo_typeof.case_141 x_a0, EoCases.__eo_typeof.case_142 x_a0, EoCases.__eo_typeof.case_143 x_a0] = [EoCases.__eo_typeof.case_140 x_a0, EoCases.__eo_typeof.case_141 x_a0, EoCases.__eo_typeof.case_142 x_a0] ++ [EoCases.__eo_typeof.case_143 x_a0] ++ [] from rfl)
    otherwise ⟨hl_143⟩ using hn_a0 hl_140 hl_141 hl_142
  group_none hinv4 hG with ⟨hl_140, hl_141, hl_142, hl_143⟩

theorem cases_0_36_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    cases_0_36_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_typeof.case_144 x_a0, EoCases.__eo_typeof.case_145 x_a0, EoCases.__eo_typeof.case_146 x_a0, EoCases.__eo_typeof.case_147 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_144 x_a0 = none ∧ EoCases.__eo_typeof.case_145 x_a0 = none ∧ EoCases.__eo_typeof.case_146 x_a0 = none ∧ EoCases.__eo_typeof.case_147 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_36_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  group_step with case_144_eo__24eo_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_144 x_a0, EoCases.__eo_typeof.case_145 x_a0, EoCases.__eo_typeof.case_146 x_a0, EoCases.__eo_typeof.case_147 x_a0] = [] ++ [EoCases.__eo_typeof.case_144 x_a0] ++ [EoCases.__eo_typeof.case_145 x_a0, EoCases.__eo_typeof.case_146 x_a0, EoCases.__eo_typeof.case_147 x_a0] from rfl)
    otherwise ⟨hl_144⟩ using hn_a0
  group_step with case_145_eo__24eo_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_144 x_a0, EoCases.__eo_typeof.case_145 x_a0, EoCases.__eo_typeof.case_146 x_a0, EoCases.__eo_typeof.case_147 x_a0] = [EoCases.__eo_typeof.case_144 x_a0] ++ [EoCases.__eo_typeof.case_145 x_a0] ++ [EoCases.__eo_typeof.case_146 x_a0, EoCases.__eo_typeof.case_147 x_a0] from rfl)
    otherwise ⟨hl_145⟩ using hn_a0 hl_144
  group_step with case_146_eo__24eo_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_144 x_a0, EoCases.__eo_typeof.case_145 x_a0, EoCases.__eo_typeof.case_146 x_a0, EoCases.__eo_typeof.case_147 x_a0] = [EoCases.__eo_typeof.case_144 x_a0, EoCases.__eo_typeof.case_145 x_a0] ++ [EoCases.__eo_typeof.case_146 x_a0] ++ [EoCases.__eo_typeof.case_147 x_a0] from rfl)
    otherwise ⟨hl_146⟩ using hn_a0 hl_144 hl_145
  group_step with case_147_eo__24eo_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_144 x_a0, EoCases.__eo_typeof.case_145 x_a0, EoCases.__eo_typeof.case_146 x_a0, EoCases.__eo_typeof.case_147 x_a0] = [EoCases.__eo_typeof.case_144 x_a0, EoCases.__eo_typeof.case_145 x_a0, EoCases.__eo_typeof.case_146 x_a0] ++ [EoCases.__eo_typeof.case_147 x_a0] ++ [] from rfl)
    otherwise ⟨hl_147⟩ using hn_a0 hl_144 hl_145 hl_146
  group_none hinv4 hG with ⟨hl_144, hl_145, hl_146, hl_147⟩

theorem cases_0_37_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    cases_0_37_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_typeof.case_148 x_a0, EoCases.__eo_typeof.case_149 x_a0, EoCases.__eo_typeof.case_150 x_a0, EoCases.__eo_typeof.case_151 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_148 x_a0 = none ∧ EoCases.__eo_typeof.case_149 x_a0 = none ∧ EoCases.__eo_typeof.case_150 x_a0 = none ∧ EoCases.__eo_typeof.case_151 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_37_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  group_step with case_148_eo__24eo_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_148 x_a0, EoCases.__eo_typeof.case_149 x_a0, EoCases.__eo_typeof.case_150 x_a0, EoCases.__eo_typeof.case_151 x_a0] = [] ++ [EoCases.__eo_typeof.case_148 x_a0] ++ [EoCases.__eo_typeof.case_149 x_a0, EoCases.__eo_typeof.case_150 x_a0, EoCases.__eo_typeof.case_151 x_a0] from rfl)
    otherwise ⟨hl_148⟩ using hn_a0
  group_step with case_149_eo__24eo_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_148 x_a0, EoCases.__eo_typeof.case_149 x_a0, EoCases.__eo_typeof.case_150 x_a0, EoCases.__eo_typeof.case_151 x_a0] = [EoCases.__eo_typeof.case_148 x_a0] ++ [EoCases.__eo_typeof.case_149 x_a0] ++ [EoCases.__eo_typeof.case_150 x_a0, EoCases.__eo_typeof.case_151 x_a0] from rfl)
    otherwise ⟨hl_149⟩ using hn_a0 hl_148
  group_step with case_150_eo__24eo_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_148 x_a0, EoCases.__eo_typeof.case_149 x_a0, EoCases.__eo_typeof.case_150 x_a0, EoCases.__eo_typeof.case_151 x_a0] = [EoCases.__eo_typeof.case_148 x_a0, EoCases.__eo_typeof.case_149 x_a0] ++ [EoCases.__eo_typeof.case_150 x_a0] ++ [EoCases.__eo_typeof.case_151 x_a0] from rfl)
    otherwise ⟨hl_150⟩ using hn_a0 hl_148 hl_149
  group_step with case_151_eo__24eo_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_148 x_a0, EoCases.__eo_typeof.case_149 x_a0, EoCases.__eo_typeof.case_150 x_a0, EoCases.__eo_typeof.case_151 x_a0] = [EoCases.__eo_typeof.case_148 x_a0, EoCases.__eo_typeof.case_149 x_a0, EoCases.__eo_typeof.case_150 x_a0] ++ [EoCases.__eo_typeof.case_151 x_a0] ++ [] from rfl)
    otherwise ⟨hl_151⟩ using hn_a0 hl_148 hl_149 hl_150
  group_none hinv4 hG with ⟨hl_148, hl_149, hl_150, hl_151⟩

theorem cases_0_38_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    cases_0_38_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_typeof.case_152 x_a0, EoCases.__eo_typeof.case_153 x_a0, EoCases.__eo_typeof.case_154 x_a0, EoCases.__eo_typeof.case_155 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_152 x_a0 = none ∧ EoCases.__eo_typeof.case_153 x_a0 = none ∧ EoCases.__eo_typeof.case_154 x_a0 = none ∧ EoCases.__eo_typeof.case_155 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_38_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  group_step with case_152_eo__24eo_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_152 x_a0, EoCases.__eo_typeof.case_153 x_a0, EoCases.__eo_typeof.case_154 x_a0, EoCases.__eo_typeof.case_155 x_a0] = [] ++ [EoCases.__eo_typeof.case_152 x_a0] ++ [EoCases.__eo_typeof.case_153 x_a0, EoCases.__eo_typeof.case_154 x_a0, EoCases.__eo_typeof.case_155 x_a0] from rfl)
    otherwise ⟨hl_152⟩ using hn_a0
  group_step with case_153_eo__24eo_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_152 x_a0, EoCases.__eo_typeof.case_153 x_a0, EoCases.__eo_typeof.case_154 x_a0, EoCases.__eo_typeof.case_155 x_a0] = [EoCases.__eo_typeof.case_152 x_a0] ++ [EoCases.__eo_typeof.case_153 x_a0] ++ [EoCases.__eo_typeof.case_154 x_a0, EoCases.__eo_typeof.case_155 x_a0] from rfl)
    otherwise ⟨hl_153⟩ using hn_a0 hl_152
  group_step with case_154_eo__24eo_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_152 x_a0, EoCases.__eo_typeof.case_153 x_a0, EoCases.__eo_typeof.case_154 x_a0, EoCases.__eo_typeof.case_155 x_a0] = [EoCases.__eo_typeof.case_152 x_a0, EoCases.__eo_typeof.case_153 x_a0] ++ [EoCases.__eo_typeof.case_154 x_a0] ++ [EoCases.__eo_typeof.case_155 x_a0] from rfl)
    otherwise ⟨hl_154⟩ using hn_a0 hl_152 hl_153
  group_step with case_155_eo__24eo_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_152 x_a0, EoCases.__eo_typeof.case_153 x_a0, EoCases.__eo_typeof.case_154 x_a0, EoCases.__eo_typeof.case_155 x_a0] = [EoCases.__eo_typeof.case_152 x_a0, EoCases.__eo_typeof.case_153 x_a0, EoCases.__eo_typeof.case_154 x_a0] ++ [EoCases.__eo_typeof.case_155 x_a0] ++ [] from rfl)
    otherwise ⟨hl_155⟩ using hn_a0 hl_152 hl_153 hl_154
  group_none hinv4 hG with ⟨hl_152, hl_153, hl_154, hl_155⟩

theorem cases_0_39_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    cases_0_39_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_typeof.case_156 x_a0, EoCases.__eo_typeof.case_157 x_a0, EoCases.__eo_typeof.case_158 x_a0, EoCases.__eo_typeof.case_159 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_156 x_a0 = none ∧ EoCases.__eo_typeof.case_157 x_a0 = none ∧ EoCases.__eo_typeof.case_158 x_a0 = none ∧ EoCases.__eo_typeof.case_159 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_39_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  group_step with case_156_eo__24eo_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_156 x_a0, EoCases.__eo_typeof.case_157 x_a0, EoCases.__eo_typeof.case_158 x_a0, EoCases.__eo_typeof.case_159 x_a0] = [] ++ [EoCases.__eo_typeof.case_156 x_a0] ++ [EoCases.__eo_typeof.case_157 x_a0, EoCases.__eo_typeof.case_158 x_a0, EoCases.__eo_typeof.case_159 x_a0] from rfl)
    otherwise ⟨hl_156⟩ using hn_a0
  group_step with case_157_eo__24eo_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_156 x_a0, EoCases.__eo_typeof.case_157 x_a0, EoCases.__eo_typeof.case_158 x_a0, EoCases.__eo_typeof.case_159 x_a0] = [EoCases.__eo_typeof.case_156 x_a0] ++ [EoCases.__eo_typeof.case_157 x_a0] ++ [EoCases.__eo_typeof.case_158 x_a0, EoCases.__eo_typeof.case_159 x_a0] from rfl)
    otherwise ⟨hl_157⟩ using hn_a0 hl_156
  group_step with case_158_eo__24eo_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_156 x_a0, EoCases.__eo_typeof.case_157 x_a0, EoCases.__eo_typeof.case_158 x_a0, EoCases.__eo_typeof.case_159 x_a0] = [EoCases.__eo_typeof.case_156 x_a0, EoCases.__eo_typeof.case_157 x_a0] ++ [EoCases.__eo_typeof.case_158 x_a0] ++ [EoCases.__eo_typeof.case_159 x_a0] from rfl)
    otherwise ⟨hl_158⟩ using hn_a0 hl_156 hl_157
  group_step with case_159_eo__24eo_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_156 x_a0, EoCases.__eo_typeof.case_157 x_a0, EoCases.__eo_typeof.case_158 x_a0, EoCases.__eo_typeof.case_159 x_a0] = [EoCases.__eo_typeof.case_156 x_a0, EoCases.__eo_typeof.case_157 x_a0, EoCases.__eo_typeof.case_158 x_a0] ++ [EoCases.__eo_typeof.case_159 x_a0] ++ [] from rfl)
    otherwise ⟨hl_159⟩ using hn_a0 hl_156 hl_157 hl_158
  group_none hinv4 hG with ⟨hl_156, hl_157, hl_158, hl_159⟩

theorem cases_0_40_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    cases_0_40_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_typeof.case_160 x_a0, EoCases.__eo_typeof.case_161 x_a0, EoCases.__eo_typeof.case_162 x_a0, EoCases.__eo_typeof.case_163 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_160 x_a0 = none ∧ EoCases.__eo_typeof.case_161 x_a0 = none ∧ EoCases.__eo_typeof.case_162 x_a0 = none ∧ EoCases.__eo_typeof.case_163 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_40_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  group_step with case_160_eo__24eo_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_160 x_a0, EoCases.__eo_typeof.case_161 x_a0, EoCases.__eo_typeof.case_162 x_a0, EoCases.__eo_typeof.case_163 x_a0] = [] ++ [EoCases.__eo_typeof.case_160 x_a0] ++ [EoCases.__eo_typeof.case_161 x_a0, EoCases.__eo_typeof.case_162 x_a0, EoCases.__eo_typeof.case_163 x_a0] from rfl)
    otherwise ⟨hl_160⟩ using hn_a0
  group_step with case_161_eo__24eo_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_160 x_a0, EoCases.__eo_typeof.case_161 x_a0, EoCases.__eo_typeof.case_162 x_a0, EoCases.__eo_typeof.case_163 x_a0] = [EoCases.__eo_typeof.case_160 x_a0] ++ [EoCases.__eo_typeof.case_161 x_a0] ++ [EoCases.__eo_typeof.case_162 x_a0, EoCases.__eo_typeof.case_163 x_a0] from rfl)
    otherwise ⟨hl_161⟩ using hn_a0 hl_160
  group_step with case_162_eo__24eo_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_160 x_a0, EoCases.__eo_typeof.case_161 x_a0, EoCases.__eo_typeof.case_162 x_a0, EoCases.__eo_typeof.case_163 x_a0] = [EoCases.__eo_typeof.case_160 x_a0, EoCases.__eo_typeof.case_161 x_a0] ++ [EoCases.__eo_typeof.case_162 x_a0] ++ [EoCases.__eo_typeof.case_163 x_a0] from rfl)
    otherwise ⟨hl_162⟩ using hn_a0 hl_160 hl_161
  group_step with case_163_eo__24eo_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_160 x_a0, EoCases.__eo_typeof.case_161 x_a0, EoCases.__eo_typeof.case_162 x_a0, EoCases.__eo_typeof.case_163 x_a0] = [EoCases.__eo_typeof.case_160 x_a0, EoCases.__eo_typeof.case_161 x_a0, EoCases.__eo_typeof.case_162 x_a0] ++ [EoCases.__eo_typeof.case_163 x_a0] ++ [] from rfl)
    otherwise ⟨hl_163⟩ using hn_a0 hl_160 hl_161 hl_162
  group_none hinv4 hG with ⟨hl_160, hl_161, hl_162, hl_163⟩

theorem cases_0_41_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    cases_0_41_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_typeof.case_164 x_a0, EoCases.__eo_typeof.case_165 x_a0, EoCases.__eo_typeof.case_166 x_a0, EoCases.__eo_typeof.case_167 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_164 x_a0 = none ∧ EoCases.__eo_typeof.case_165 x_a0 = none ∧ EoCases.__eo_typeof.case_166 x_a0 = none ∧ EoCases.__eo_typeof.case_167 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_41_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  group_step with case_164_eo__24eo_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_164 x_a0, EoCases.__eo_typeof.case_165 x_a0, EoCases.__eo_typeof.case_166 x_a0, EoCases.__eo_typeof.case_167 x_a0] = [] ++ [EoCases.__eo_typeof.case_164 x_a0] ++ [EoCases.__eo_typeof.case_165 x_a0, EoCases.__eo_typeof.case_166 x_a0, EoCases.__eo_typeof.case_167 x_a0] from rfl)
    otherwise ⟨hl_164⟩ using hn_a0
  group_step with case_165_eo__24eo_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_164 x_a0, EoCases.__eo_typeof.case_165 x_a0, EoCases.__eo_typeof.case_166 x_a0, EoCases.__eo_typeof.case_167 x_a0] = [EoCases.__eo_typeof.case_164 x_a0] ++ [EoCases.__eo_typeof.case_165 x_a0] ++ [EoCases.__eo_typeof.case_166 x_a0, EoCases.__eo_typeof.case_167 x_a0] from rfl)
    otherwise ⟨hl_165⟩ using hn_a0 hl_164
  group_step with case_166_eo__24eo_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_164 x_a0, EoCases.__eo_typeof.case_165 x_a0, EoCases.__eo_typeof.case_166 x_a0, EoCases.__eo_typeof.case_167 x_a0] = [EoCases.__eo_typeof.case_164 x_a0, EoCases.__eo_typeof.case_165 x_a0] ++ [EoCases.__eo_typeof.case_166 x_a0] ++ [EoCases.__eo_typeof.case_167 x_a0] from rfl)
    otherwise ⟨hl_166⟩ using hn_a0 hl_164 hl_165
  group_step with case_167_eo__24eo_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_164 x_a0, EoCases.__eo_typeof.case_165 x_a0, EoCases.__eo_typeof.case_166 x_a0, EoCases.__eo_typeof.case_167 x_a0] = [EoCases.__eo_typeof.case_164 x_a0, EoCases.__eo_typeof.case_165 x_a0, EoCases.__eo_typeof.case_166 x_a0] ++ [EoCases.__eo_typeof.case_167 x_a0] ++ [] from rfl)
    otherwise ⟨hl_167⟩ using hn_a0 hl_164 hl_165 hl_166
  group_none hinv4 hG with ⟨hl_164, hl_165, hl_166, hl_167⟩

theorem cases_0_42_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    cases_0_42_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_typeof.case_168 x_a0, EoCases.__eo_typeof.case_169 x_a0, EoCases.__eo_typeof.case_170 x_a0, EoCases.__eo_typeof.case_171 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_168 x_a0 = none ∧ EoCases.__eo_typeof.case_169 x_a0 = none ∧ EoCases.__eo_typeof.case_170 x_a0 = none ∧ EoCases.__eo_typeof.case_171 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_42_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  group_step with case_168_eo__24eo_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_168 x_a0, EoCases.__eo_typeof.case_169 x_a0, EoCases.__eo_typeof.case_170 x_a0, EoCases.__eo_typeof.case_171 x_a0] = [] ++ [EoCases.__eo_typeof.case_168 x_a0] ++ [EoCases.__eo_typeof.case_169 x_a0, EoCases.__eo_typeof.case_170 x_a0, EoCases.__eo_typeof.case_171 x_a0] from rfl)
    otherwise ⟨hl_168⟩ using hn_a0
  group_step with case_169_eo__24eo_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_168 x_a0, EoCases.__eo_typeof.case_169 x_a0, EoCases.__eo_typeof.case_170 x_a0, EoCases.__eo_typeof.case_171 x_a0] = [EoCases.__eo_typeof.case_168 x_a0] ++ [EoCases.__eo_typeof.case_169 x_a0] ++ [EoCases.__eo_typeof.case_170 x_a0, EoCases.__eo_typeof.case_171 x_a0] from rfl)
    otherwise ⟨hl_169⟩ using hn_a0 hl_168
  group_step with case_170_eo__24eo_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_168 x_a0, EoCases.__eo_typeof.case_169 x_a0, EoCases.__eo_typeof.case_170 x_a0, EoCases.__eo_typeof.case_171 x_a0] = [EoCases.__eo_typeof.case_168 x_a0, EoCases.__eo_typeof.case_169 x_a0] ++ [EoCases.__eo_typeof.case_170 x_a0] ++ [EoCases.__eo_typeof.case_171 x_a0] from rfl)
    otherwise ⟨hl_170⟩ using hn_a0 hl_168 hl_169
  group_step with case_171_eo__24eo_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_168 x_a0, EoCases.__eo_typeof.case_169 x_a0, EoCases.__eo_typeof.case_170 x_a0, EoCases.__eo_typeof.case_171 x_a0] = [EoCases.__eo_typeof.case_168 x_a0, EoCases.__eo_typeof.case_169 x_a0, EoCases.__eo_typeof.case_170 x_a0] ++ [EoCases.__eo_typeof.case_171 x_a0] ++ [] from rfl)
    otherwise ⟨hl_171⟩ using hn_a0 hl_168 hl_169 hl_170
  group_none hinv4 hG with ⟨hl_168, hl_169, hl_170, hl_171⟩

theorem cases_0_43_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    cases_0_43_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_typeof.case_172 x_a0, EoCases.__eo_typeof.case_173 x_a0, EoCases.__eo_typeof.case_174 x_a0, EoCases.__eo_typeof.case_175 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_172 x_a0 = none ∧ EoCases.__eo_typeof.case_173 x_a0 = none ∧ EoCases.__eo_typeof.case_174 x_a0 = none ∧ EoCases.__eo_typeof.case_175 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_43_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  group_step with case_172_eo__24eo_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_172 x_a0, EoCases.__eo_typeof.case_173 x_a0, EoCases.__eo_typeof.case_174 x_a0, EoCases.__eo_typeof.case_175 x_a0] = [] ++ [EoCases.__eo_typeof.case_172 x_a0] ++ [EoCases.__eo_typeof.case_173 x_a0, EoCases.__eo_typeof.case_174 x_a0, EoCases.__eo_typeof.case_175 x_a0] from rfl)
    otherwise ⟨hl_172⟩ using hn_a0
  group_step with case_173_eo__24eo_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_172 x_a0, EoCases.__eo_typeof.case_173 x_a0, EoCases.__eo_typeof.case_174 x_a0, EoCases.__eo_typeof.case_175 x_a0] = [EoCases.__eo_typeof.case_172 x_a0] ++ [EoCases.__eo_typeof.case_173 x_a0] ++ [EoCases.__eo_typeof.case_174 x_a0, EoCases.__eo_typeof.case_175 x_a0] from rfl)
    otherwise ⟨hl_173⟩ using hn_a0 hl_172
  group_step with case_174_eo__24eo_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_172 x_a0, EoCases.__eo_typeof.case_173 x_a0, EoCases.__eo_typeof.case_174 x_a0, EoCases.__eo_typeof.case_175 x_a0] = [EoCases.__eo_typeof.case_172 x_a0, EoCases.__eo_typeof.case_173 x_a0] ++ [EoCases.__eo_typeof.case_174 x_a0] ++ [EoCases.__eo_typeof.case_175 x_a0] from rfl)
    otherwise ⟨hl_174⟩ using hn_a0 hl_172 hl_173
  group_step with case_175_eo__24eo_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_172 x_a0, EoCases.__eo_typeof.case_173 x_a0, EoCases.__eo_typeof.case_174 x_a0, EoCases.__eo_typeof.case_175 x_a0] = [EoCases.__eo_typeof.case_172 x_a0, EoCases.__eo_typeof.case_173 x_a0, EoCases.__eo_typeof.case_174 x_a0] ++ [EoCases.__eo_typeof.case_175 x_a0] ++ [] from rfl)
    otherwise ⟨hl_175⟩ using hn_a0 hl_172 hl_173 hl_174
  group_none hinv4 hG with ⟨hl_172, hl_173, hl_174, hl_175⟩

theorem cases_0_44_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    cases_0_44_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_typeof.case_176 x_a0, EoCases.__eo_typeof.case_177 x_a0, EoCases.__eo_typeof.case_178 x_a0, EoCases.__eo_typeof.case_179 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_176 x_a0 = none ∧ EoCases.__eo_typeof.case_177 x_a0 = none ∧ EoCases.__eo_typeof.case_178 x_a0 = none ∧ EoCases.__eo_typeof.case_179 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_44_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  group_step with case_176_eo__24eo_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_176 x_a0, EoCases.__eo_typeof.case_177 x_a0, EoCases.__eo_typeof.case_178 x_a0, EoCases.__eo_typeof.case_179 x_a0] = [] ++ [EoCases.__eo_typeof.case_176 x_a0] ++ [EoCases.__eo_typeof.case_177 x_a0, EoCases.__eo_typeof.case_178 x_a0, EoCases.__eo_typeof.case_179 x_a0] from rfl)
    otherwise ⟨hl_176⟩ using hn_a0
  group_step with case_177_eo__24eo_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_176 x_a0, EoCases.__eo_typeof.case_177 x_a0, EoCases.__eo_typeof.case_178 x_a0, EoCases.__eo_typeof.case_179 x_a0] = [EoCases.__eo_typeof.case_176 x_a0] ++ [EoCases.__eo_typeof.case_177 x_a0] ++ [EoCases.__eo_typeof.case_178 x_a0, EoCases.__eo_typeof.case_179 x_a0] from rfl)
    otherwise ⟨hl_177⟩ using hn_a0 hl_176
  group_step with case_178_eo__24eo_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_176 x_a0, EoCases.__eo_typeof.case_177 x_a0, EoCases.__eo_typeof.case_178 x_a0, EoCases.__eo_typeof.case_179 x_a0] = [EoCases.__eo_typeof.case_176 x_a0, EoCases.__eo_typeof.case_177 x_a0] ++ [EoCases.__eo_typeof.case_178 x_a0] ++ [EoCases.__eo_typeof.case_179 x_a0] from rfl)
    otherwise ⟨hl_178⟩ using hn_a0 hl_176 hl_177
  group_step with case_179_eo__24eo_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_176 x_a0, EoCases.__eo_typeof.case_177 x_a0, EoCases.__eo_typeof.case_178 x_a0, EoCases.__eo_typeof.case_179 x_a0] = [EoCases.__eo_typeof.case_176 x_a0, EoCases.__eo_typeof.case_177 x_a0, EoCases.__eo_typeof.case_178 x_a0] ++ [EoCases.__eo_typeof.case_179 x_a0] ++ [] from rfl)
    otherwise ⟨hl_179⟩ using hn_a0 hl_176 hl_177 hl_178
  group_none hinv4 hG with ⟨hl_176, hl_177, hl_178, hl_179⟩

theorem cases_0_45_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    cases_0_45_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_typeof.case_180 x_a0, EoCases.__eo_typeof.case_181 x_a0, EoCases.__eo_typeof.case_182 x_a0, EoCases.__eo_typeof.case_183 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_180 x_a0 = none ∧ EoCases.__eo_typeof.case_181 x_a0 = none ∧ EoCases.__eo_typeof.case_182 x_a0 = none ∧ EoCases.__eo_typeof.case_183 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_45_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  group_step with case_180_eo__24eo_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_180 x_a0, EoCases.__eo_typeof.case_181 x_a0, EoCases.__eo_typeof.case_182 x_a0, EoCases.__eo_typeof.case_183 x_a0] = [] ++ [EoCases.__eo_typeof.case_180 x_a0] ++ [EoCases.__eo_typeof.case_181 x_a0, EoCases.__eo_typeof.case_182 x_a0, EoCases.__eo_typeof.case_183 x_a0] from rfl)
    otherwise ⟨hl_180⟩ using hn_a0
  group_step with case_181_eo__24eo_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_180 x_a0, EoCases.__eo_typeof.case_181 x_a0, EoCases.__eo_typeof.case_182 x_a0, EoCases.__eo_typeof.case_183 x_a0] = [EoCases.__eo_typeof.case_180 x_a0] ++ [EoCases.__eo_typeof.case_181 x_a0] ++ [EoCases.__eo_typeof.case_182 x_a0, EoCases.__eo_typeof.case_183 x_a0] from rfl)
    otherwise ⟨hl_181⟩ using hn_a0 hl_180
  group_step with case_182_eo__24eo_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_180 x_a0, EoCases.__eo_typeof.case_181 x_a0, EoCases.__eo_typeof.case_182 x_a0, EoCases.__eo_typeof.case_183 x_a0] = [EoCases.__eo_typeof.case_180 x_a0, EoCases.__eo_typeof.case_181 x_a0] ++ [EoCases.__eo_typeof.case_182 x_a0] ++ [EoCases.__eo_typeof.case_183 x_a0] from rfl)
    otherwise ⟨hl_182⟩ using hn_a0 hl_180 hl_181
  group_step with case_183_eo__24eo_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_180 x_a0, EoCases.__eo_typeof.case_181 x_a0, EoCases.__eo_typeof.case_182 x_a0, EoCases.__eo_typeof.case_183 x_a0] = [EoCases.__eo_typeof.case_180 x_a0, EoCases.__eo_typeof.case_181 x_a0, EoCases.__eo_typeof.case_182 x_a0] ++ [EoCases.__eo_typeof.case_183 x_a0] ++ [] from rfl)
    otherwise ⟨hl_183⟩ using hn_a0 hl_180 hl_181 hl_182
  group_none hinv4 hG with ⟨hl_180, hl_181, hl_182, hl_183⟩

theorem cases_0_46_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    cases_0_46_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_typeof.case_184 x_a0, EoCases.__eo_typeof.case_185 x_a0, EoCases.__eo_typeof.case_186 x_a0, EoCases.__eo_typeof.case_187 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_184 x_a0 = none ∧ EoCases.__eo_typeof.case_185 x_a0 = none ∧ EoCases.__eo_typeof.case_186 x_a0 = none ∧ EoCases.__eo_typeof.case_187 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_46_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  group_step with case_184_eo__24eo_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_184 x_a0, EoCases.__eo_typeof.case_185 x_a0, EoCases.__eo_typeof.case_186 x_a0, EoCases.__eo_typeof.case_187 x_a0] = [] ++ [EoCases.__eo_typeof.case_184 x_a0] ++ [EoCases.__eo_typeof.case_185 x_a0, EoCases.__eo_typeof.case_186 x_a0, EoCases.__eo_typeof.case_187 x_a0] from rfl)
    otherwise ⟨hl_184⟩ using hn_a0
  group_step with case_185_eo__24eo_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_184 x_a0, EoCases.__eo_typeof.case_185 x_a0, EoCases.__eo_typeof.case_186 x_a0, EoCases.__eo_typeof.case_187 x_a0] = [EoCases.__eo_typeof.case_184 x_a0] ++ [EoCases.__eo_typeof.case_185 x_a0] ++ [EoCases.__eo_typeof.case_186 x_a0, EoCases.__eo_typeof.case_187 x_a0] from rfl)
    otherwise ⟨hl_185⟩ using hn_a0 hl_184
  group_step with case_186_eo__24eo_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_184 x_a0, EoCases.__eo_typeof.case_185 x_a0, EoCases.__eo_typeof.case_186 x_a0, EoCases.__eo_typeof.case_187 x_a0] = [EoCases.__eo_typeof.case_184 x_a0, EoCases.__eo_typeof.case_185 x_a0] ++ [EoCases.__eo_typeof.case_186 x_a0] ++ [EoCases.__eo_typeof.case_187 x_a0] from rfl)
    otherwise ⟨hl_186⟩ using hn_a0 hl_184 hl_185
  group_step with case_187_eo__24eo_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_184 x_a0, EoCases.__eo_typeof.case_185 x_a0, EoCases.__eo_typeof.case_186 x_a0, EoCases.__eo_typeof.case_187 x_a0] = [EoCases.__eo_typeof.case_184 x_a0, EoCases.__eo_typeof.case_185 x_a0, EoCases.__eo_typeof.case_186 x_a0] ++ [EoCases.__eo_typeof.case_187 x_a0] ++ [] from rfl)
    otherwise ⟨hl_187⟩ using hn_a0 hl_184 hl_185 hl_186
  group_none hinv4 hG with ⟨hl_184, hl_185, hl_186, hl_187⟩

theorem cases_0_47_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    cases_0_47_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_typeof.case_188 x_a0, EoCases.__eo_typeof.case_189 x_a0, EoCases.__eo_typeof.case_190 x_a0, EoCases.__eo_typeof.case_191 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_188 x_a0 = none ∧ EoCases.__eo_typeof.case_189 x_a0 = none ∧ EoCases.__eo_typeof.case_190 x_a0 = none ∧ EoCases.__eo_typeof.case_191 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_47_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  group_step with case_188_eo__24eo_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_188 x_a0, EoCases.__eo_typeof.case_189 x_a0, EoCases.__eo_typeof.case_190 x_a0, EoCases.__eo_typeof.case_191 x_a0] = [] ++ [EoCases.__eo_typeof.case_188 x_a0] ++ [EoCases.__eo_typeof.case_189 x_a0, EoCases.__eo_typeof.case_190 x_a0, EoCases.__eo_typeof.case_191 x_a0] from rfl)
    otherwise ⟨hl_188⟩ using hn_a0
  group_step with case_189_eo__24eo_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_188 x_a0, EoCases.__eo_typeof.case_189 x_a0, EoCases.__eo_typeof.case_190 x_a0, EoCases.__eo_typeof.case_191 x_a0] = [EoCases.__eo_typeof.case_188 x_a0] ++ [EoCases.__eo_typeof.case_189 x_a0] ++ [EoCases.__eo_typeof.case_190 x_a0, EoCases.__eo_typeof.case_191 x_a0] from rfl)
    otherwise ⟨hl_189⟩ using hn_a0 hl_188
  group_step with case_190_eo__24eo_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_188 x_a0, EoCases.__eo_typeof.case_189 x_a0, EoCases.__eo_typeof.case_190 x_a0, EoCases.__eo_typeof.case_191 x_a0] = [EoCases.__eo_typeof.case_188 x_a0, EoCases.__eo_typeof.case_189 x_a0] ++ [EoCases.__eo_typeof.case_190 x_a0] ++ [EoCases.__eo_typeof.case_191 x_a0] from rfl)
    otherwise ⟨hl_190⟩ using hn_a0 hl_188 hl_189
  group_step with case_191_eo__24eo_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_188 x_a0, EoCases.__eo_typeof.case_189 x_a0, EoCases.__eo_typeof.case_190 x_a0, EoCases.__eo_typeof.case_191 x_a0] = [EoCases.__eo_typeof.case_188 x_a0, EoCases.__eo_typeof.case_189 x_a0, EoCases.__eo_typeof.case_190 x_a0] ++ [EoCases.__eo_typeof.case_191 x_a0] ++ [] from rfl)
    otherwise ⟨hl_191⟩ using hn_a0 hl_188 hl_189 hl_190
  group_none hinv4 hG with ⟨hl_188, hl_189, hl_190, hl_191⟩

theorem cases_0_48_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    cases_0_48_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_typeof.case_192 x_a0, EoCases.__eo_typeof.case_193 x_a0, EoCases.__eo_typeof.case_194 x_a0, EoCases.__eo_typeof.case_195 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_192 x_a0 = none ∧ EoCases.__eo_typeof.case_193 x_a0 = none ∧ EoCases.__eo_typeof.case_194 x_a0 = none ∧ EoCases.__eo_typeof.case_195 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_48_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  group_step with case_192_eo__24eo_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_192 x_a0, EoCases.__eo_typeof.case_193 x_a0, EoCases.__eo_typeof.case_194 x_a0, EoCases.__eo_typeof.case_195 x_a0] = [] ++ [EoCases.__eo_typeof.case_192 x_a0] ++ [EoCases.__eo_typeof.case_193 x_a0, EoCases.__eo_typeof.case_194 x_a0, EoCases.__eo_typeof.case_195 x_a0] from rfl)
    otherwise ⟨hl_192⟩ using hn_a0
  group_step with case_193_eo__24eo_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_192 x_a0, EoCases.__eo_typeof.case_193 x_a0, EoCases.__eo_typeof.case_194 x_a0, EoCases.__eo_typeof.case_195 x_a0] = [EoCases.__eo_typeof.case_192 x_a0] ++ [EoCases.__eo_typeof.case_193 x_a0] ++ [EoCases.__eo_typeof.case_194 x_a0, EoCases.__eo_typeof.case_195 x_a0] from rfl)
    otherwise ⟨hl_193⟩ using hn_a0 hl_192
  group_step with case_194_eo__24eo_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_192 x_a0, EoCases.__eo_typeof.case_193 x_a0, EoCases.__eo_typeof.case_194 x_a0, EoCases.__eo_typeof.case_195 x_a0] = [EoCases.__eo_typeof.case_192 x_a0, EoCases.__eo_typeof.case_193 x_a0] ++ [EoCases.__eo_typeof.case_194 x_a0] ++ [EoCases.__eo_typeof.case_195 x_a0] from rfl)
    otherwise ⟨hl_194⟩ using hn_a0 hl_192 hl_193
  group_step with case_195_eo__24eo_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_192 x_a0, EoCases.__eo_typeof.case_193 x_a0, EoCases.__eo_typeof.case_194 x_a0, EoCases.__eo_typeof.case_195 x_a0] = [EoCases.__eo_typeof.case_192 x_a0, EoCases.__eo_typeof.case_193 x_a0, EoCases.__eo_typeof.case_194 x_a0] ++ [EoCases.__eo_typeof.case_195 x_a0] ++ [] from rfl)
    otherwise ⟨hl_195⟩ using hn_a0 hl_192 hl_193 hl_194
  group_none hinv4 hG with ⟨hl_192, hl_193, hl_194, hl_195⟩

theorem cases_0_49_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    cases_0_49_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_typeof.case_196 x_a0, EoCases.__eo_typeof.case_197 x_a0, EoCases.__eo_typeof.case_198 x_a0, EoCases.__eo_typeof.case_199 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_196 x_a0 = none ∧ EoCases.__eo_typeof.case_197 x_a0 = none ∧ EoCases.__eo_typeof.case_198 x_a0 = none ∧ EoCases.__eo_typeof.case_199 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_49_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  group_step with case_196_eo__24eo_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_196 x_a0, EoCases.__eo_typeof.case_197 x_a0, EoCases.__eo_typeof.case_198 x_a0, EoCases.__eo_typeof.case_199 x_a0] = [] ++ [EoCases.__eo_typeof.case_196 x_a0] ++ [EoCases.__eo_typeof.case_197 x_a0, EoCases.__eo_typeof.case_198 x_a0, EoCases.__eo_typeof.case_199 x_a0] from rfl)
    otherwise ⟨hl_196⟩ using hn_a0
  group_step with case_197_eo__24eo_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_196 x_a0, EoCases.__eo_typeof.case_197 x_a0, EoCases.__eo_typeof.case_198 x_a0, EoCases.__eo_typeof.case_199 x_a0] = [EoCases.__eo_typeof.case_196 x_a0] ++ [EoCases.__eo_typeof.case_197 x_a0] ++ [EoCases.__eo_typeof.case_198 x_a0, EoCases.__eo_typeof.case_199 x_a0] from rfl)
    otherwise ⟨hl_197⟩ using hn_a0 hl_196
  group_step with case_198_eo__24eo_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_196 x_a0, EoCases.__eo_typeof.case_197 x_a0, EoCases.__eo_typeof.case_198 x_a0, EoCases.__eo_typeof.case_199 x_a0] = [EoCases.__eo_typeof.case_196 x_a0, EoCases.__eo_typeof.case_197 x_a0] ++ [EoCases.__eo_typeof.case_198 x_a0] ++ [EoCases.__eo_typeof.case_199 x_a0] from rfl)
    otherwise ⟨hl_198⟩ using hn_a0 hl_196 hl_197
  group_step with case_199_eo__24eo_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_196 x_a0, EoCases.__eo_typeof.case_197 x_a0, EoCases.__eo_typeof.case_198 x_a0, EoCases.__eo_typeof.case_199 x_a0] = [EoCases.__eo_typeof.case_196 x_a0, EoCases.__eo_typeof.case_197 x_a0, EoCases.__eo_typeof.case_198 x_a0] ++ [EoCases.__eo_typeof.case_199 x_a0] ++ [] from rfl)
    otherwise ⟨hl_199⟩ using hn_a0 hl_196 hl_197 hl_198
  group_none hinv4 hG with ⟨hl_196, hl_197, hl_198, hl_199⟩

theorem cases_0_50_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    cases_0_50_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_typeof.case_200 x_a0, EoCases.__eo_typeof.case_201 x_a0, EoCases.__eo_typeof.case_202 x_a0, EoCases.__eo_typeof.case_203 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_200 x_a0 = none ∧ EoCases.__eo_typeof.case_201 x_a0 = none ∧ EoCases.__eo_typeof.case_202 x_a0 = none ∧ EoCases.__eo_typeof.case_203 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_50_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  group_step with case_200_eo__24eo_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_200 x_a0, EoCases.__eo_typeof.case_201 x_a0, EoCases.__eo_typeof.case_202 x_a0, EoCases.__eo_typeof.case_203 x_a0] = [] ++ [EoCases.__eo_typeof.case_200 x_a0] ++ [EoCases.__eo_typeof.case_201 x_a0, EoCases.__eo_typeof.case_202 x_a0, EoCases.__eo_typeof.case_203 x_a0] from rfl)
    otherwise ⟨hl_200⟩ using hn_a0
  group_step with case_201_eo__24eo_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_200 x_a0, EoCases.__eo_typeof.case_201 x_a0, EoCases.__eo_typeof.case_202 x_a0, EoCases.__eo_typeof.case_203 x_a0] = [EoCases.__eo_typeof.case_200 x_a0] ++ [EoCases.__eo_typeof.case_201 x_a0] ++ [EoCases.__eo_typeof.case_202 x_a0, EoCases.__eo_typeof.case_203 x_a0] from rfl)
    otherwise ⟨hl_201⟩ using hn_a0 hl_200
  group_step with case_202_eo__24eo_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_200 x_a0, EoCases.__eo_typeof.case_201 x_a0, EoCases.__eo_typeof.case_202 x_a0, EoCases.__eo_typeof.case_203 x_a0] = [EoCases.__eo_typeof.case_200 x_a0, EoCases.__eo_typeof.case_201 x_a0] ++ [EoCases.__eo_typeof.case_202 x_a0] ++ [EoCases.__eo_typeof.case_203 x_a0] from rfl)
    otherwise ⟨hl_202⟩ using hn_a0 hl_200 hl_201
  group_step with case_203_eo__24eo_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_200 x_a0, EoCases.__eo_typeof.case_201 x_a0, EoCases.__eo_typeof.case_202 x_a0, EoCases.__eo_typeof.case_203 x_a0] = [EoCases.__eo_typeof.case_200 x_a0, EoCases.__eo_typeof.case_201 x_a0, EoCases.__eo_typeof.case_202 x_a0] ++ [EoCases.__eo_typeof.case_203 x_a0] ++ [] from rfl)
    otherwise ⟨hl_203⟩ using hn_a0 hl_200 hl_201 hl_202
  group_none hinv4 hG with ⟨hl_200, hl_201, hl_202, hl_203⟩

theorem cases_0_51_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    cases_0_51_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_typeof.case_204 x_a0, EoCases.__eo_typeof.case_205 x_a0, EoCases.__eo_typeof.case_206 x_a0, EoCases.__eo_typeof.case_207 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_204 x_a0 = none ∧ EoCases.__eo_typeof.case_205 x_a0 = none ∧ EoCases.__eo_typeof.case_206 x_a0 = none ∧ EoCases.__eo_typeof.case_207 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_51_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  group_step with case_204_eo__24eo_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_204 x_a0, EoCases.__eo_typeof.case_205 x_a0, EoCases.__eo_typeof.case_206 x_a0, EoCases.__eo_typeof.case_207 x_a0] = [] ++ [EoCases.__eo_typeof.case_204 x_a0] ++ [EoCases.__eo_typeof.case_205 x_a0, EoCases.__eo_typeof.case_206 x_a0, EoCases.__eo_typeof.case_207 x_a0] from rfl)
    otherwise ⟨hl_204⟩ using hn_a0
  group_step with case_205_eo__24eo_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_204 x_a0, EoCases.__eo_typeof.case_205 x_a0, EoCases.__eo_typeof.case_206 x_a0, EoCases.__eo_typeof.case_207 x_a0] = [EoCases.__eo_typeof.case_204 x_a0] ++ [EoCases.__eo_typeof.case_205 x_a0] ++ [EoCases.__eo_typeof.case_206 x_a0, EoCases.__eo_typeof.case_207 x_a0] from rfl)
    otherwise ⟨hl_205⟩ using hn_a0 hl_204
  group_step with case_206_eo__24eo_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_204 x_a0, EoCases.__eo_typeof.case_205 x_a0, EoCases.__eo_typeof.case_206 x_a0, EoCases.__eo_typeof.case_207 x_a0] = [EoCases.__eo_typeof.case_204 x_a0, EoCases.__eo_typeof.case_205 x_a0] ++ [EoCases.__eo_typeof.case_206 x_a0] ++ [EoCases.__eo_typeof.case_207 x_a0] from rfl)
    otherwise ⟨hl_206⟩ using hn_a0 hl_204 hl_205
  group_step with case_207_eo__24eo_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_204 x_a0, EoCases.__eo_typeof.case_205 x_a0, EoCases.__eo_typeof.case_206 x_a0, EoCases.__eo_typeof.case_207 x_a0] = [EoCases.__eo_typeof.case_204 x_a0, EoCases.__eo_typeof.case_205 x_a0, EoCases.__eo_typeof.case_206 x_a0] ++ [EoCases.__eo_typeof.case_207 x_a0] ++ [] from rfl)
    otherwise ⟨hl_207⟩ using hn_a0 hl_204 hl_205 hl_206
  group_none hinv4 hG with ⟨hl_204, hl_205, hl_206, hl_207⟩

theorem cases_1_0_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    cases_1_0_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_typeof.case_0 x_a0, EoCases.__eo_typeof.case_1 x_a0, EoCases.__eo_typeof.case_2 x_a0, EoCases.__eo_typeof.case_3 x_a0, EoCases.__eo_typeof.case_4 x_a0, EoCases.__eo_typeof.case_5 x_a0, EoCases.__eo_typeof.case_6 x_a0, EoCases.__eo_typeof.case_7 x_a0, EoCases.__eo_typeof.case_8 x_a0, EoCases.__eo_typeof.case_9 x_a0, EoCases.__eo_typeof.case_10 x_a0, EoCases.__eo_typeof.case_11 x_a0, EoCases.__eo_typeof.case_12 x_a0, EoCases.__eo_typeof.case_13 x_a0, EoCases.__eo_typeof.case_14 x_a0, EoCases.__eo_typeof.case_15 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_0 x_a0 = none ∧ EoCases.__eo_typeof.case_1 x_a0 = none ∧ EoCases.__eo_typeof.case_2 x_a0 = none ∧ EoCases.__eo_typeof.case_3 x_a0 = none ∧ EoCases.__eo_typeof.case_4 x_a0 = none ∧ EoCases.__eo_typeof.case_5 x_a0 = none ∧ EoCases.__eo_typeof.case_6 x_a0 = none ∧ EoCases.__eo_typeof.case_7 x_a0 = none ∧ EoCases.__eo_typeof.case_8 x_a0 = none ∧ EoCases.__eo_typeof.case_9 x_a0 = none ∧ EoCases.__eo_typeof.case_10 x_a0 = none ∧ EoCases.__eo_typeof.case_11 x_a0 = none ∧ EoCases.__eo_typeof.case_12 x_a0 = none ∧ EoCases.__eo_typeof.case_13 x_a0 = none ∧ EoCases.__eo_typeof.case_14 x_a0 = none ∧ EoCases.__eo_typeof.case_15 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_1_0_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  group_step with cases_0_0_eo__24eo_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_0 x_a0, EoCases.__eo_typeof.case_1 x_a0, EoCases.__eo_typeof.case_2 x_a0, EoCases.__eo_typeof.case_3 x_a0, EoCases.__eo_typeof.case_4 x_a0, EoCases.__eo_typeof.case_5 x_a0, EoCases.__eo_typeof.case_6 x_a0, EoCases.__eo_typeof.case_7 x_a0, EoCases.__eo_typeof.case_8 x_a0, EoCases.__eo_typeof.case_9 x_a0, EoCases.__eo_typeof.case_10 x_a0, EoCases.__eo_typeof.case_11 x_a0, EoCases.__eo_typeof.case_12 x_a0, EoCases.__eo_typeof.case_13 x_a0, EoCases.__eo_typeof.case_14 x_a0, EoCases.__eo_typeof.case_15 x_a0] = [] ++ [EoCases.__eo_typeof.case_0 x_a0, EoCases.__eo_typeof.case_1 x_a0, EoCases.__eo_typeof.case_2 x_a0, EoCases.__eo_typeof.case_3 x_a0] ++ [EoCases.__eo_typeof.case_4 x_a0, EoCases.__eo_typeof.case_5 x_a0, EoCases.__eo_typeof.case_6 x_a0, EoCases.__eo_typeof.case_7 x_a0, EoCases.__eo_typeof.case_8 x_a0, EoCases.__eo_typeof.case_9 x_a0, EoCases.__eo_typeof.case_10 x_a0, EoCases.__eo_typeof.case_11 x_a0, EoCases.__eo_typeof.case_12 x_a0, EoCases.__eo_typeof.case_13 x_a0, EoCases.__eo_typeof.case_14 x_a0, EoCases.__eo_typeof.case_15 x_a0] from rfl)
    otherwise ⟨hl_0, hl_1, hl_2, hl_3⟩ using hn_a0
  group_step with cases_0_1_eo__24eo_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_0 x_a0, EoCases.__eo_typeof.case_1 x_a0, EoCases.__eo_typeof.case_2 x_a0, EoCases.__eo_typeof.case_3 x_a0, EoCases.__eo_typeof.case_4 x_a0, EoCases.__eo_typeof.case_5 x_a0, EoCases.__eo_typeof.case_6 x_a0, EoCases.__eo_typeof.case_7 x_a0, EoCases.__eo_typeof.case_8 x_a0, EoCases.__eo_typeof.case_9 x_a0, EoCases.__eo_typeof.case_10 x_a0, EoCases.__eo_typeof.case_11 x_a0, EoCases.__eo_typeof.case_12 x_a0, EoCases.__eo_typeof.case_13 x_a0, EoCases.__eo_typeof.case_14 x_a0, EoCases.__eo_typeof.case_15 x_a0] = [EoCases.__eo_typeof.case_0 x_a0, EoCases.__eo_typeof.case_1 x_a0, EoCases.__eo_typeof.case_2 x_a0, EoCases.__eo_typeof.case_3 x_a0] ++ [EoCases.__eo_typeof.case_4 x_a0, EoCases.__eo_typeof.case_5 x_a0, EoCases.__eo_typeof.case_6 x_a0, EoCases.__eo_typeof.case_7 x_a0] ++ [EoCases.__eo_typeof.case_8 x_a0, EoCases.__eo_typeof.case_9 x_a0, EoCases.__eo_typeof.case_10 x_a0, EoCases.__eo_typeof.case_11 x_a0, EoCases.__eo_typeof.case_12 x_a0, EoCases.__eo_typeof.case_13 x_a0, EoCases.__eo_typeof.case_14 x_a0, EoCases.__eo_typeof.case_15 x_a0] from rfl)
    otherwise ⟨hl_4, hl_5, hl_6, hl_7⟩ using hn_a0 hl_0 hl_1 hl_2 hl_3
  group_step with cases_0_2_eo__24eo_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_0 x_a0, EoCases.__eo_typeof.case_1 x_a0, EoCases.__eo_typeof.case_2 x_a0, EoCases.__eo_typeof.case_3 x_a0, EoCases.__eo_typeof.case_4 x_a0, EoCases.__eo_typeof.case_5 x_a0, EoCases.__eo_typeof.case_6 x_a0, EoCases.__eo_typeof.case_7 x_a0, EoCases.__eo_typeof.case_8 x_a0, EoCases.__eo_typeof.case_9 x_a0, EoCases.__eo_typeof.case_10 x_a0, EoCases.__eo_typeof.case_11 x_a0, EoCases.__eo_typeof.case_12 x_a0, EoCases.__eo_typeof.case_13 x_a0, EoCases.__eo_typeof.case_14 x_a0, EoCases.__eo_typeof.case_15 x_a0] = [EoCases.__eo_typeof.case_0 x_a0, EoCases.__eo_typeof.case_1 x_a0, EoCases.__eo_typeof.case_2 x_a0, EoCases.__eo_typeof.case_3 x_a0, EoCases.__eo_typeof.case_4 x_a0, EoCases.__eo_typeof.case_5 x_a0, EoCases.__eo_typeof.case_6 x_a0, EoCases.__eo_typeof.case_7 x_a0] ++ [EoCases.__eo_typeof.case_8 x_a0, EoCases.__eo_typeof.case_9 x_a0, EoCases.__eo_typeof.case_10 x_a0, EoCases.__eo_typeof.case_11 x_a0] ++ [EoCases.__eo_typeof.case_12 x_a0, EoCases.__eo_typeof.case_13 x_a0, EoCases.__eo_typeof.case_14 x_a0, EoCases.__eo_typeof.case_15 x_a0] from rfl)
    otherwise ⟨hl_8, hl_9, hl_10, hl_11⟩ using hn_a0 hl_0 hl_1 hl_2 hl_3 hl_4 hl_5 hl_6 hl_7
  group_step with cases_0_3_eo__24eo_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_0 x_a0, EoCases.__eo_typeof.case_1 x_a0, EoCases.__eo_typeof.case_2 x_a0, EoCases.__eo_typeof.case_3 x_a0, EoCases.__eo_typeof.case_4 x_a0, EoCases.__eo_typeof.case_5 x_a0, EoCases.__eo_typeof.case_6 x_a0, EoCases.__eo_typeof.case_7 x_a0, EoCases.__eo_typeof.case_8 x_a0, EoCases.__eo_typeof.case_9 x_a0, EoCases.__eo_typeof.case_10 x_a0, EoCases.__eo_typeof.case_11 x_a0, EoCases.__eo_typeof.case_12 x_a0, EoCases.__eo_typeof.case_13 x_a0, EoCases.__eo_typeof.case_14 x_a0, EoCases.__eo_typeof.case_15 x_a0] = [EoCases.__eo_typeof.case_0 x_a0, EoCases.__eo_typeof.case_1 x_a0, EoCases.__eo_typeof.case_2 x_a0, EoCases.__eo_typeof.case_3 x_a0, EoCases.__eo_typeof.case_4 x_a0, EoCases.__eo_typeof.case_5 x_a0, EoCases.__eo_typeof.case_6 x_a0, EoCases.__eo_typeof.case_7 x_a0, EoCases.__eo_typeof.case_8 x_a0, EoCases.__eo_typeof.case_9 x_a0, EoCases.__eo_typeof.case_10 x_a0, EoCases.__eo_typeof.case_11 x_a0] ++ [EoCases.__eo_typeof.case_12 x_a0, EoCases.__eo_typeof.case_13 x_a0, EoCases.__eo_typeof.case_14 x_a0, EoCases.__eo_typeof.case_15 x_a0] ++ [] from rfl)
    otherwise ⟨hl_12, hl_13, hl_14, hl_15⟩ using hn_a0 hl_0 hl_1 hl_2 hl_3 hl_4 hl_5 hl_6 hl_7 hl_8 hl_9 hl_10 hl_11
  group_none hinv4 hG with ⟨hl_0, hl_1, hl_2, hl_3, hl_4, hl_5, hl_6, hl_7, hl_8, hl_9, hl_10, hl_11, hl_12, hl_13, hl_14, hl_15⟩

theorem cases_1_1_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    cases_1_1_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_typeof.case_16 x_a0, EoCases.__eo_typeof.case_17 x_a0, EoCases.__eo_typeof.case_18 x_a0, EoCases.__eo_typeof.case_19 x_a0, EoCases.__eo_typeof.case_20 x_a0, EoCases.__eo_typeof.case_21 x_a0, EoCases.__eo_typeof.case_22 x_a0, EoCases.__eo_typeof.case_23 x_a0, EoCases.__eo_typeof.case_24 x_a0, EoCases.__eo_typeof.case_25 x_a0, EoCases.__eo_typeof.case_26 x_a0, EoCases.__eo_typeof.case_27 x_a0, EoCases.__eo_typeof.case_28 x_a0, EoCases.__eo_typeof.case_29 x_a0, EoCases.__eo_typeof.case_30 x_a0, EoCases.__eo_typeof.case_31 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_16 x_a0 = none ∧ EoCases.__eo_typeof.case_17 x_a0 = none ∧ EoCases.__eo_typeof.case_18 x_a0 = none ∧ EoCases.__eo_typeof.case_19 x_a0 = none ∧ EoCases.__eo_typeof.case_20 x_a0 = none ∧ EoCases.__eo_typeof.case_21 x_a0 = none ∧ EoCases.__eo_typeof.case_22 x_a0 = none ∧ EoCases.__eo_typeof.case_23 x_a0 = none ∧ EoCases.__eo_typeof.case_24 x_a0 = none ∧ EoCases.__eo_typeof.case_25 x_a0 = none ∧ EoCases.__eo_typeof.case_26 x_a0 = none ∧ EoCases.__eo_typeof.case_27 x_a0 = none ∧ EoCases.__eo_typeof.case_28 x_a0 = none ∧ EoCases.__eo_typeof.case_29 x_a0 = none ∧ EoCases.__eo_typeof.case_30 x_a0 = none ∧ EoCases.__eo_typeof.case_31 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_1_1_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  group_step with cases_0_4_eo__24eo_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_16 x_a0, EoCases.__eo_typeof.case_17 x_a0, EoCases.__eo_typeof.case_18 x_a0, EoCases.__eo_typeof.case_19 x_a0, EoCases.__eo_typeof.case_20 x_a0, EoCases.__eo_typeof.case_21 x_a0, EoCases.__eo_typeof.case_22 x_a0, EoCases.__eo_typeof.case_23 x_a0, EoCases.__eo_typeof.case_24 x_a0, EoCases.__eo_typeof.case_25 x_a0, EoCases.__eo_typeof.case_26 x_a0, EoCases.__eo_typeof.case_27 x_a0, EoCases.__eo_typeof.case_28 x_a0, EoCases.__eo_typeof.case_29 x_a0, EoCases.__eo_typeof.case_30 x_a0, EoCases.__eo_typeof.case_31 x_a0] = [] ++ [EoCases.__eo_typeof.case_16 x_a0, EoCases.__eo_typeof.case_17 x_a0, EoCases.__eo_typeof.case_18 x_a0, EoCases.__eo_typeof.case_19 x_a0] ++ [EoCases.__eo_typeof.case_20 x_a0, EoCases.__eo_typeof.case_21 x_a0, EoCases.__eo_typeof.case_22 x_a0, EoCases.__eo_typeof.case_23 x_a0, EoCases.__eo_typeof.case_24 x_a0, EoCases.__eo_typeof.case_25 x_a0, EoCases.__eo_typeof.case_26 x_a0, EoCases.__eo_typeof.case_27 x_a0, EoCases.__eo_typeof.case_28 x_a0, EoCases.__eo_typeof.case_29 x_a0, EoCases.__eo_typeof.case_30 x_a0, EoCases.__eo_typeof.case_31 x_a0] from rfl)
    otherwise ⟨hl_16, hl_17, hl_18, hl_19⟩ using hn_a0
  group_step with cases_0_5_eo__24eo_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_16 x_a0, EoCases.__eo_typeof.case_17 x_a0, EoCases.__eo_typeof.case_18 x_a0, EoCases.__eo_typeof.case_19 x_a0, EoCases.__eo_typeof.case_20 x_a0, EoCases.__eo_typeof.case_21 x_a0, EoCases.__eo_typeof.case_22 x_a0, EoCases.__eo_typeof.case_23 x_a0, EoCases.__eo_typeof.case_24 x_a0, EoCases.__eo_typeof.case_25 x_a0, EoCases.__eo_typeof.case_26 x_a0, EoCases.__eo_typeof.case_27 x_a0, EoCases.__eo_typeof.case_28 x_a0, EoCases.__eo_typeof.case_29 x_a0, EoCases.__eo_typeof.case_30 x_a0, EoCases.__eo_typeof.case_31 x_a0] = [EoCases.__eo_typeof.case_16 x_a0, EoCases.__eo_typeof.case_17 x_a0, EoCases.__eo_typeof.case_18 x_a0, EoCases.__eo_typeof.case_19 x_a0] ++ [EoCases.__eo_typeof.case_20 x_a0, EoCases.__eo_typeof.case_21 x_a0, EoCases.__eo_typeof.case_22 x_a0, EoCases.__eo_typeof.case_23 x_a0] ++ [EoCases.__eo_typeof.case_24 x_a0, EoCases.__eo_typeof.case_25 x_a0, EoCases.__eo_typeof.case_26 x_a0, EoCases.__eo_typeof.case_27 x_a0, EoCases.__eo_typeof.case_28 x_a0, EoCases.__eo_typeof.case_29 x_a0, EoCases.__eo_typeof.case_30 x_a0, EoCases.__eo_typeof.case_31 x_a0] from rfl)
    otherwise ⟨hl_20, hl_21, hl_22, hl_23⟩ using hn_a0 hl_16 hl_17 hl_18 hl_19
  group_step with cases_0_6_eo__24eo_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_16 x_a0, EoCases.__eo_typeof.case_17 x_a0, EoCases.__eo_typeof.case_18 x_a0, EoCases.__eo_typeof.case_19 x_a0, EoCases.__eo_typeof.case_20 x_a0, EoCases.__eo_typeof.case_21 x_a0, EoCases.__eo_typeof.case_22 x_a0, EoCases.__eo_typeof.case_23 x_a0, EoCases.__eo_typeof.case_24 x_a0, EoCases.__eo_typeof.case_25 x_a0, EoCases.__eo_typeof.case_26 x_a0, EoCases.__eo_typeof.case_27 x_a0, EoCases.__eo_typeof.case_28 x_a0, EoCases.__eo_typeof.case_29 x_a0, EoCases.__eo_typeof.case_30 x_a0, EoCases.__eo_typeof.case_31 x_a0] = [EoCases.__eo_typeof.case_16 x_a0, EoCases.__eo_typeof.case_17 x_a0, EoCases.__eo_typeof.case_18 x_a0, EoCases.__eo_typeof.case_19 x_a0, EoCases.__eo_typeof.case_20 x_a0, EoCases.__eo_typeof.case_21 x_a0, EoCases.__eo_typeof.case_22 x_a0, EoCases.__eo_typeof.case_23 x_a0] ++ [EoCases.__eo_typeof.case_24 x_a0, EoCases.__eo_typeof.case_25 x_a0, EoCases.__eo_typeof.case_26 x_a0, EoCases.__eo_typeof.case_27 x_a0] ++ [EoCases.__eo_typeof.case_28 x_a0, EoCases.__eo_typeof.case_29 x_a0, EoCases.__eo_typeof.case_30 x_a0, EoCases.__eo_typeof.case_31 x_a0] from rfl)
    otherwise ⟨hl_24, hl_25, hl_26, hl_27⟩ using hn_a0 hl_16 hl_17 hl_18 hl_19 hl_20 hl_21 hl_22 hl_23
  group_step with cases_0_7_eo__24eo_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_16 x_a0, EoCases.__eo_typeof.case_17 x_a0, EoCases.__eo_typeof.case_18 x_a0, EoCases.__eo_typeof.case_19 x_a0, EoCases.__eo_typeof.case_20 x_a0, EoCases.__eo_typeof.case_21 x_a0, EoCases.__eo_typeof.case_22 x_a0, EoCases.__eo_typeof.case_23 x_a0, EoCases.__eo_typeof.case_24 x_a0, EoCases.__eo_typeof.case_25 x_a0, EoCases.__eo_typeof.case_26 x_a0, EoCases.__eo_typeof.case_27 x_a0, EoCases.__eo_typeof.case_28 x_a0, EoCases.__eo_typeof.case_29 x_a0, EoCases.__eo_typeof.case_30 x_a0, EoCases.__eo_typeof.case_31 x_a0] = [EoCases.__eo_typeof.case_16 x_a0, EoCases.__eo_typeof.case_17 x_a0, EoCases.__eo_typeof.case_18 x_a0, EoCases.__eo_typeof.case_19 x_a0, EoCases.__eo_typeof.case_20 x_a0, EoCases.__eo_typeof.case_21 x_a0, EoCases.__eo_typeof.case_22 x_a0, EoCases.__eo_typeof.case_23 x_a0, EoCases.__eo_typeof.case_24 x_a0, EoCases.__eo_typeof.case_25 x_a0, EoCases.__eo_typeof.case_26 x_a0, EoCases.__eo_typeof.case_27 x_a0] ++ [EoCases.__eo_typeof.case_28 x_a0, EoCases.__eo_typeof.case_29 x_a0, EoCases.__eo_typeof.case_30 x_a0, EoCases.__eo_typeof.case_31 x_a0] ++ [] from rfl)
    otherwise ⟨hl_28, hl_29, hl_30, hl_31⟩ using hn_a0 hl_16 hl_17 hl_18 hl_19 hl_20 hl_21 hl_22 hl_23 hl_24 hl_25 hl_26 hl_27
  group_none hinv4 hG with ⟨hl_16, hl_17, hl_18, hl_19, hl_20, hl_21, hl_22, hl_23, hl_24, hl_25, hl_26, hl_27, hl_28, hl_29, hl_30, hl_31⟩

theorem cases_1_2_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    cases_1_2_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_typeof.case_32 x_a0, EoCases.__eo_typeof.case_33 x_a0, EoCases.__eo_typeof.case_34 x_a0, EoCases.__eo_typeof.case_35 x_a0, EoCases.__eo_typeof.case_36 x_a0, EoCases.__eo_typeof.case_37 x_a0, EoCases.__eo_typeof.case_38 x_a0, EoCases.__eo_typeof.case_39 x_a0, EoCases.__eo_typeof.case_40 x_a0, EoCases.__eo_typeof.case_41 x_a0, EoCases.__eo_typeof.case_42 x_a0, EoCases.__eo_typeof.case_43 x_a0, EoCases.__eo_typeof.case_44 x_a0, EoCases.__eo_typeof.case_45 x_a0, EoCases.__eo_typeof.case_46 x_a0, EoCases.__eo_typeof.case_47 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_32 x_a0 = none ∧ EoCases.__eo_typeof.case_33 x_a0 = none ∧ EoCases.__eo_typeof.case_34 x_a0 = none ∧ EoCases.__eo_typeof.case_35 x_a0 = none ∧ EoCases.__eo_typeof.case_36 x_a0 = none ∧ EoCases.__eo_typeof.case_37 x_a0 = none ∧ EoCases.__eo_typeof.case_38 x_a0 = none ∧ EoCases.__eo_typeof.case_39 x_a0 = none ∧ EoCases.__eo_typeof.case_40 x_a0 = none ∧ EoCases.__eo_typeof.case_41 x_a0 = none ∧ EoCases.__eo_typeof.case_42 x_a0 = none ∧ EoCases.__eo_typeof.case_43 x_a0 = none ∧ EoCases.__eo_typeof.case_44 x_a0 = none ∧ EoCases.__eo_typeof.case_45 x_a0 = none ∧ EoCases.__eo_typeof.case_46 x_a0 = none ∧ EoCases.__eo_typeof.case_47 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_1_2_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  group_step with cases_0_8_eo__24eo_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_32 x_a0, EoCases.__eo_typeof.case_33 x_a0, EoCases.__eo_typeof.case_34 x_a0, EoCases.__eo_typeof.case_35 x_a0, EoCases.__eo_typeof.case_36 x_a0, EoCases.__eo_typeof.case_37 x_a0, EoCases.__eo_typeof.case_38 x_a0, EoCases.__eo_typeof.case_39 x_a0, EoCases.__eo_typeof.case_40 x_a0, EoCases.__eo_typeof.case_41 x_a0, EoCases.__eo_typeof.case_42 x_a0, EoCases.__eo_typeof.case_43 x_a0, EoCases.__eo_typeof.case_44 x_a0, EoCases.__eo_typeof.case_45 x_a0, EoCases.__eo_typeof.case_46 x_a0, EoCases.__eo_typeof.case_47 x_a0] = [] ++ [EoCases.__eo_typeof.case_32 x_a0, EoCases.__eo_typeof.case_33 x_a0, EoCases.__eo_typeof.case_34 x_a0, EoCases.__eo_typeof.case_35 x_a0] ++ [EoCases.__eo_typeof.case_36 x_a0, EoCases.__eo_typeof.case_37 x_a0, EoCases.__eo_typeof.case_38 x_a0, EoCases.__eo_typeof.case_39 x_a0, EoCases.__eo_typeof.case_40 x_a0, EoCases.__eo_typeof.case_41 x_a0, EoCases.__eo_typeof.case_42 x_a0, EoCases.__eo_typeof.case_43 x_a0, EoCases.__eo_typeof.case_44 x_a0, EoCases.__eo_typeof.case_45 x_a0, EoCases.__eo_typeof.case_46 x_a0, EoCases.__eo_typeof.case_47 x_a0] from rfl)
    otherwise ⟨hl_32, hl_33, hl_34, hl_35⟩ using hn_a0
  group_step with cases_0_9_eo__24eo_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_32 x_a0, EoCases.__eo_typeof.case_33 x_a0, EoCases.__eo_typeof.case_34 x_a0, EoCases.__eo_typeof.case_35 x_a0, EoCases.__eo_typeof.case_36 x_a0, EoCases.__eo_typeof.case_37 x_a0, EoCases.__eo_typeof.case_38 x_a0, EoCases.__eo_typeof.case_39 x_a0, EoCases.__eo_typeof.case_40 x_a0, EoCases.__eo_typeof.case_41 x_a0, EoCases.__eo_typeof.case_42 x_a0, EoCases.__eo_typeof.case_43 x_a0, EoCases.__eo_typeof.case_44 x_a0, EoCases.__eo_typeof.case_45 x_a0, EoCases.__eo_typeof.case_46 x_a0, EoCases.__eo_typeof.case_47 x_a0] = [EoCases.__eo_typeof.case_32 x_a0, EoCases.__eo_typeof.case_33 x_a0, EoCases.__eo_typeof.case_34 x_a0, EoCases.__eo_typeof.case_35 x_a0] ++ [EoCases.__eo_typeof.case_36 x_a0, EoCases.__eo_typeof.case_37 x_a0, EoCases.__eo_typeof.case_38 x_a0, EoCases.__eo_typeof.case_39 x_a0] ++ [EoCases.__eo_typeof.case_40 x_a0, EoCases.__eo_typeof.case_41 x_a0, EoCases.__eo_typeof.case_42 x_a0, EoCases.__eo_typeof.case_43 x_a0, EoCases.__eo_typeof.case_44 x_a0, EoCases.__eo_typeof.case_45 x_a0, EoCases.__eo_typeof.case_46 x_a0, EoCases.__eo_typeof.case_47 x_a0] from rfl)
    otherwise ⟨hl_36, hl_37, hl_38, hl_39⟩ using hn_a0 hl_32 hl_33 hl_34 hl_35
  group_step with cases_0_10_eo__24eo_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_32 x_a0, EoCases.__eo_typeof.case_33 x_a0, EoCases.__eo_typeof.case_34 x_a0, EoCases.__eo_typeof.case_35 x_a0, EoCases.__eo_typeof.case_36 x_a0, EoCases.__eo_typeof.case_37 x_a0, EoCases.__eo_typeof.case_38 x_a0, EoCases.__eo_typeof.case_39 x_a0, EoCases.__eo_typeof.case_40 x_a0, EoCases.__eo_typeof.case_41 x_a0, EoCases.__eo_typeof.case_42 x_a0, EoCases.__eo_typeof.case_43 x_a0, EoCases.__eo_typeof.case_44 x_a0, EoCases.__eo_typeof.case_45 x_a0, EoCases.__eo_typeof.case_46 x_a0, EoCases.__eo_typeof.case_47 x_a0] = [EoCases.__eo_typeof.case_32 x_a0, EoCases.__eo_typeof.case_33 x_a0, EoCases.__eo_typeof.case_34 x_a0, EoCases.__eo_typeof.case_35 x_a0, EoCases.__eo_typeof.case_36 x_a0, EoCases.__eo_typeof.case_37 x_a0, EoCases.__eo_typeof.case_38 x_a0, EoCases.__eo_typeof.case_39 x_a0] ++ [EoCases.__eo_typeof.case_40 x_a0, EoCases.__eo_typeof.case_41 x_a0, EoCases.__eo_typeof.case_42 x_a0, EoCases.__eo_typeof.case_43 x_a0] ++ [EoCases.__eo_typeof.case_44 x_a0, EoCases.__eo_typeof.case_45 x_a0, EoCases.__eo_typeof.case_46 x_a0, EoCases.__eo_typeof.case_47 x_a0] from rfl)
    otherwise ⟨hl_40, hl_41, hl_42, hl_43⟩ using hn_a0 hl_32 hl_33 hl_34 hl_35 hl_36 hl_37 hl_38 hl_39
  group_step with cases_0_11_eo__24eo_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_32 x_a0, EoCases.__eo_typeof.case_33 x_a0, EoCases.__eo_typeof.case_34 x_a0, EoCases.__eo_typeof.case_35 x_a0, EoCases.__eo_typeof.case_36 x_a0, EoCases.__eo_typeof.case_37 x_a0, EoCases.__eo_typeof.case_38 x_a0, EoCases.__eo_typeof.case_39 x_a0, EoCases.__eo_typeof.case_40 x_a0, EoCases.__eo_typeof.case_41 x_a0, EoCases.__eo_typeof.case_42 x_a0, EoCases.__eo_typeof.case_43 x_a0, EoCases.__eo_typeof.case_44 x_a0, EoCases.__eo_typeof.case_45 x_a0, EoCases.__eo_typeof.case_46 x_a0, EoCases.__eo_typeof.case_47 x_a0] = [EoCases.__eo_typeof.case_32 x_a0, EoCases.__eo_typeof.case_33 x_a0, EoCases.__eo_typeof.case_34 x_a0, EoCases.__eo_typeof.case_35 x_a0, EoCases.__eo_typeof.case_36 x_a0, EoCases.__eo_typeof.case_37 x_a0, EoCases.__eo_typeof.case_38 x_a0, EoCases.__eo_typeof.case_39 x_a0, EoCases.__eo_typeof.case_40 x_a0, EoCases.__eo_typeof.case_41 x_a0, EoCases.__eo_typeof.case_42 x_a0, EoCases.__eo_typeof.case_43 x_a0] ++ [EoCases.__eo_typeof.case_44 x_a0, EoCases.__eo_typeof.case_45 x_a0, EoCases.__eo_typeof.case_46 x_a0, EoCases.__eo_typeof.case_47 x_a0] ++ [] from rfl)
    otherwise ⟨hl_44, hl_45, hl_46, hl_47⟩ using hn_a0 hl_32 hl_33 hl_34 hl_35 hl_36 hl_37 hl_38 hl_39 hl_40 hl_41 hl_42 hl_43
  group_none hinv4 hG with ⟨hl_32, hl_33, hl_34, hl_35, hl_36, hl_37, hl_38, hl_39, hl_40, hl_41, hl_42, hl_43, hl_44, hl_45, hl_46, hl_47⟩

theorem cases_1_3_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    cases_1_3_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_typeof.case_48 x_a0, EoCases.__eo_typeof.case_49 x_a0, EoCases.__eo_typeof.case_50 x_a0, EoCases.__eo_typeof.case_51 x_a0, EoCases.__eo_typeof.case_52 x_a0, EoCases.__eo_typeof.case_53 x_a0, EoCases.__eo_typeof.case_54 x_a0, EoCases.__eo_typeof.case_55 x_a0, EoCases.__eo_typeof.case_56 x_a0, EoCases.__eo_typeof.case_57 x_a0, EoCases.__eo_typeof.case_58 x_a0, EoCases.__eo_typeof.case_59 x_a0, EoCases.__eo_typeof.case_60 x_a0, EoCases.__eo_typeof.case_61 x_a0, EoCases.__eo_typeof.case_62 x_a0, EoCases.__eo_typeof.case_63 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_48 x_a0 = none ∧ EoCases.__eo_typeof.case_49 x_a0 = none ∧ EoCases.__eo_typeof.case_50 x_a0 = none ∧ EoCases.__eo_typeof.case_51 x_a0 = none ∧ EoCases.__eo_typeof.case_52 x_a0 = none ∧ EoCases.__eo_typeof.case_53 x_a0 = none ∧ EoCases.__eo_typeof.case_54 x_a0 = none ∧ EoCases.__eo_typeof.case_55 x_a0 = none ∧ EoCases.__eo_typeof.case_56 x_a0 = none ∧ EoCases.__eo_typeof.case_57 x_a0 = none ∧ EoCases.__eo_typeof.case_58 x_a0 = none ∧ EoCases.__eo_typeof.case_59 x_a0 = none ∧ EoCases.__eo_typeof.case_60 x_a0 = none ∧ EoCases.__eo_typeof.case_61 x_a0 = none ∧ EoCases.__eo_typeof.case_62 x_a0 = none ∧ EoCases.__eo_typeof.case_63 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_1_3_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  group_step with cases_0_12_eo__24eo_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_48 x_a0, EoCases.__eo_typeof.case_49 x_a0, EoCases.__eo_typeof.case_50 x_a0, EoCases.__eo_typeof.case_51 x_a0, EoCases.__eo_typeof.case_52 x_a0, EoCases.__eo_typeof.case_53 x_a0, EoCases.__eo_typeof.case_54 x_a0, EoCases.__eo_typeof.case_55 x_a0, EoCases.__eo_typeof.case_56 x_a0, EoCases.__eo_typeof.case_57 x_a0, EoCases.__eo_typeof.case_58 x_a0, EoCases.__eo_typeof.case_59 x_a0, EoCases.__eo_typeof.case_60 x_a0, EoCases.__eo_typeof.case_61 x_a0, EoCases.__eo_typeof.case_62 x_a0, EoCases.__eo_typeof.case_63 x_a0] = [] ++ [EoCases.__eo_typeof.case_48 x_a0, EoCases.__eo_typeof.case_49 x_a0, EoCases.__eo_typeof.case_50 x_a0, EoCases.__eo_typeof.case_51 x_a0] ++ [EoCases.__eo_typeof.case_52 x_a0, EoCases.__eo_typeof.case_53 x_a0, EoCases.__eo_typeof.case_54 x_a0, EoCases.__eo_typeof.case_55 x_a0, EoCases.__eo_typeof.case_56 x_a0, EoCases.__eo_typeof.case_57 x_a0, EoCases.__eo_typeof.case_58 x_a0, EoCases.__eo_typeof.case_59 x_a0, EoCases.__eo_typeof.case_60 x_a0, EoCases.__eo_typeof.case_61 x_a0, EoCases.__eo_typeof.case_62 x_a0, EoCases.__eo_typeof.case_63 x_a0] from rfl)
    otherwise ⟨hl_48, hl_49, hl_50, hl_51⟩ using hn_a0
  group_step with cases_0_13_eo__24eo_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_48 x_a0, EoCases.__eo_typeof.case_49 x_a0, EoCases.__eo_typeof.case_50 x_a0, EoCases.__eo_typeof.case_51 x_a0, EoCases.__eo_typeof.case_52 x_a0, EoCases.__eo_typeof.case_53 x_a0, EoCases.__eo_typeof.case_54 x_a0, EoCases.__eo_typeof.case_55 x_a0, EoCases.__eo_typeof.case_56 x_a0, EoCases.__eo_typeof.case_57 x_a0, EoCases.__eo_typeof.case_58 x_a0, EoCases.__eo_typeof.case_59 x_a0, EoCases.__eo_typeof.case_60 x_a0, EoCases.__eo_typeof.case_61 x_a0, EoCases.__eo_typeof.case_62 x_a0, EoCases.__eo_typeof.case_63 x_a0] = [EoCases.__eo_typeof.case_48 x_a0, EoCases.__eo_typeof.case_49 x_a0, EoCases.__eo_typeof.case_50 x_a0, EoCases.__eo_typeof.case_51 x_a0] ++ [EoCases.__eo_typeof.case_52 x_a0, EoCases.__eo_typeof.case_53 x_a0, EoCases.__eo_typeof.case_54 x_a0, EoCases.__eo_typeof.case_55 x_a0] ++ [EoCases.__eo_typeof.case_56 x_a0, EoCases.__eo_typeof.case_57 x_a0, EoCases.__eo_typeof.case_58 x_a0, EoCases.__eo_typeof.case_59 x_a0, EoCases.__eo_typeof.case_60 x_a0, EoCases.__eo_typeof.case_61 x_a0, EoCases.__eo_typeof.case_62 x_a0, EoCases.__eo_typeof.case_63 x_a0] from rfl)
    otherwise ⟨hl_52, hl_53, hl_54, hl_55⟩ using hn_a0 hl_48 hl_49 hl_50 hl_51
  group_step with cases_0_14_eo__24eo_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_48 x_a0, EoCases.__eo_typeof.case_49 x_a0, EoCases.__eo_typeof.case_50 x_a0, EoCases.__eo_typeof.case_51 x_a0, EoCases.__eo_typeof.case_52 x_a0, EoCases.__eo_typeof.case_53 x_a0, EoCases.__eo_typeof.case_54 x_a0, EoCases.__eo_typeof.case_55 x_a0, EoCases.__eo_typeof.case_56 x_a0, EoCases.__eo_typeof.case_57 x_a0, EoCases.__eo_typeof.case_58 x_a0, EoCases.__eo_typeof.case_59 x_a0, EoCases.__eo_typeof.case_60 x_a0, EoCases.__eo_typeof.case_61 x_a0, EoCases.__eo_typeof.case_62 x_a0, EoCases.__eo_typeof.case_63 x_a0] = [EoCases.__eo_typeof.case_48 x_a0, EoCases.__eo_typeof.case_49 x_a0, EoCases.__eo_typeof.case_50 x_a0, EoCases.__eo_typeof.case_51 x_a0, EoCases.__eo_typeof.case_52 x_a0, EoCases.__eo_typeof.case_53 x_a0, EoCases.__eo_typeof.case_54 x_a0, EoCases.__eo_typeof.case_55 x_a0] ++ [EoCases.__eo_typeof.case_56 x_a0, EoCases.__eo_typeof.case_57 x_a0, EoCases.__eo_typeof.case_58 x_a0, EoCases.__eo_typeof.case_59 x_a0] ++ [EoCases.__eo_typeof.case_60 x_a0, EoCases.__eo_typeof.case_61 x_a0, EoCases.__eo_typeof.case_62 x_a0, EoCases.__eo_typeof.case_63 x_a0] from rfl)
    otherwise ⟨hl_56, hl_57, hl_58, hl_59⟩ using hn_a0 hl_48 hl_49 hl_50 hl_51 hl_52 hl_53 hl_54 hl_55
  group_step with cases_0_15_eo__24eo_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_48 x_a0, EoCases.__eo_typeof.case_49 x_a0, EoCases.__eo_typeof.case_50 x_a0, EoCases.__eo_typeof.case_51 x_a0, EoCases.__eo_typeof.case_52 x_a0, EoCases.__eo_typeof.case_53 x_a0, EoCases.__eo_typeof.case_54 x_a0, EoCases.__eo_typeof.case_55 x_a0, EoCases.__eo_typeof.case_56 x_a0, EoCases.__eo_typeof.case_57 x_a0, EoCases.__eo_typeof.case_58 x_a0, EoCases.__eo_typeof.case_59 x_a0, EoCases.__eo_typeof.case_60 x_a0, EoCases.__eo_typeof.case_61 x_a0, EoCases.__eo_typeof.case_62 x_a0, EoCases.__eo_typeof.case_63 x_a0] = [EoCases.__eo_typeof.case_48 x_a0, EoCases.__eo_typeof.case_49 x_a0, EoCases.__eo_typeof.case_50 x_a0, EoCases.__eo_typeof.case_51 x_a0, EoCases.__eo_typeof.case_52 x_a0, EoCases.__eo_typeof.case_53 x_a0, EoCases.__eo_typeof.case_54 x_a0, EoCases.__eo_typeof.case_55 x_a0, EoCases.__eo_typeof.case_56 x_a0, EoCases.__eo_typeof.case_57 x_a0, EoCases.__eo_typeof.case_58 x_a0, EoCases.__eo_typeof.case_59 x_a0] ++ [EoCases.__eo_typeof.case_60 x_a0, EoCases.__eo_typeof.case_61 x_a0, EoCases.__eo_typeof.case_62 x_a0, EoCases.__eo_typeof.case_63 x_a0] ++ [] from rfl)
    otherwise ⟨hl_60, hl_61, hl_62, hl_63⟩ using hn_a0 hl_48 hl_49 hl_50 hl_51 hl_52 hl_53 hl_54 hl_55 hl_56 hl_57 hl_58 hl_59
  group_none hinv4 hG with ⟨hl_48, hl_49, hl_50, hl_51, hl_52, hl_53, hl_54, hl_55, hl_56, hl_57, hl_58, hl_59, hl_60, hl_61, hl_62, hl_63⟩

theorem cases_1_4_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    cases_1_4_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_typeof.case_64 x_a0, EoCases.__eo_typeof.case_65 x_a0, EoCases.__eo_typeof.case_66 x_a0, EoCases.__eo_typeof.case_67 x_a0, EoCases.__eo_typeof.case_68 x_a0, EoCases.__eo_typeof.case_69 x_a0, EoCases.__eo_typeof.case_70 x_a0, EoCases.__eo_typeof.case_71 x_a0, EoCases.__eo_typeof.case_72 x_a0, EoCases.__eo_typeof.case_73 x_a0, EoCases.__eo_typeof.case_74 x_a0, EoCases.__eo_typeof.case_75 x_a0, EoCases.__eo_typeof.case_76 x_a0, EoCases.__eo_typeof.case_77 x_a0, EoCases.__eo_typeof.case_78 x_a0, EoCases.__eo_typeof.case_79 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_64 x_a0 = none ∧ EoCases.__eo_typeof.case_65 x_a0 = none ∧ EoCases.__eo_typeof.case_66 x_a0 = none ∧ EoCases.__eo_typeof.case_67 x_a0 = none ∧ EoCases.__eo_typeof.case_68 x_a0 = none ∧ EoCases.__eo_typeof.case_69 x_a0 = none ∧ EoCases.__eo_typeof.case_70 x_a0 = none ∧ EoCases.__eo_typeof.case_71 x_a0 = none ∧ EoCases.__eo_typeof.case_72 x_a0 = none ∧ EoCases.__eo_typeof.case_73 x_a0 = none ∧ EoCases.__eo_typeof.case_74 x_a0 = none ∧ EoCases.__eo_typeof.case_75 x_a0 = none ∧ EoCases.__eo_typeof.case_76 x_a0 = none ∧ EoCases.__eo_typeof.case_77 x_a0 = none ∧ EoCases.__eo_typeof.case_78 x_a0 = none ∧ EoCases.__eo_typeof.case_79 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_1_4_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  group_step with cases_0_16_eo__24eo_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_64 x_a0, EoCases.__eo_typeof.case_65 x_a0, EoCases.__eo_typeof.case_66 x_a0, EoCases.__eo_typeof.case_67 x_a0, EoCases.__eo_typeof.case_68 x_a0, EoCases.__eo_typeof.case_69 x_a0, EoCases.__eo_typeof.case_70 x_a0, EoCases.__eo_typeof.case_71 x_a0, EoCases.__eo_typeof.case_72 x_a0, EoCases.__eo_typeof.case_73 x_a0, EoCases.__eo_typeof.case_74 x_a0, EoCases.__eo_typeof.case_75 x_a0, EoCases.__eo_typeof.case_76 x_a0, EoCases.__eo_typeof.case_77 x_a0, EoCases.__eo_typeof.case_78 x_a0, EoCases.__eo_typeof.case_79 x_a0] = [] ++ [EoCases.__eo_typeof.case_64 x_a0, EoCases.__eo_typeof.case_65 x_a0, EoCases.__eo_typeof.case_66 x_a0, EoCases.__eo_typeof.case_67 x_a0] ++ [EoCases.__eo_typeof.case_68 x_a0, EoCases.__eo_typeof.case_69 x_a0, EoCases.__eo_typeof.case_70 x_a0, EoCases.__eo_typeof.case_71 x_a0, EoCases.__eo_typeof.case_72 x_a0, EoCases.__eo_typeof.case_73 x_a0, EoCases.__eo_typeof.case_74 x_a0, EoCases.__eo_typeof.case_75 x_a0, EoCases.__eo_typeof.case_76 x_a0, EoCases.__eo_typeof.case_77 x_a0, EoCases.__eo_typeof.case_78 x_a0, EoCases.__eo_typeof.case_79 x_a0] from rfl)
    otherwise ⟨hl_64, hl_65, hl_66, hl_67⟩ using hn_a0
  group_step with cases_0_17_eo__24eo_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_64 x_a0, EoCases.__eo_typeof.case_65 x_a0, EoCases.__eo_typeof.case_66 x_a0, EoCases.__eo_typeof.case_67 x_a0, EoCases.__eo_typeof.case_68 x_a0, EoCases.__eo_typeof.case_69 x_a0, EoCases.__eo_typeof.case_70 x_a0, EoCases.__eo_typeof.case_71 x_a0, EoCases.__eo_typeof.case_72 x_a0, EoCases.__eo_typeof.case_73 x_a0, EoCases.__eo_typeof.case_74 x_a0, EoCases.__eo_typeof.case_75 x_a0, EoCases.__eo_typeof.case_76 x_a0, EoCases.__eo_typeof.case_77 x_a0, EoCases.__eo_typeof.case_78 x_a0, EoCases.__eo_typeof.case_79 x_a0] = [EoCases.__eo_typeof.case_64 x_a0, EoCases.__eo_typeof.case_65 x_a0, EoCases.__eo_typeof.case_66 x_a0, EoCases.__eo_typeof.case_67 x_a0] ++ [EoCases.__eo_typeof.case_68 x_a0, EoCases.__eo_typeof.case_69 x_a0, EoCases.__eo_typeof.case_70 x_a0, EoCases.__eo_typeof.case_71 x_a0] ++ [EoCases.__eo_typeof.case_72 x_a0, EoCases.__eo_typeof.case_73 x_a0, EoCases.__eo_typeof.case_74 x_a0, EoCases.__eo_typeof.case_75 x_a0, EoCases.__eo_typeof.case_76 x_a0, EoCases.__eo_typeof.case_77 x_a0, EoCases.__eo_typeof.case_78 x_a0, EoCases.__eo_typeof.case_79 x_a0] from rfl)
    otherwise ⟨hl_68, hl_69, hl_70, hl_71⟩ using hn_a0 hl_64 hl_65 hl_66 hl_67
  group_step with cases_0_18_eo__24eo_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_64 x_a0, EoCases.__eo_typeof.case_65 x_a0, EoCases.__eo_typeof.case_66 x_a0, EoCases.__eo_typeof.case_67 x_a0, EoCases.__eo_typeof.case_68 x_a0, EoCases.__eo_typeof.case_69 x_a0, EoCases.__eo_typeof.case_70 x_a0, EoCases.__eo_typeof.case_71 x_a0, EoCases.__eo_typeof.case_72 x_a0, EoCases.__eo_typeof.case_73 x_a0, EoCases.__eo_typeof.case_74 x_a0, EoCases.__eo_typeof.case_75 x_a0, EoCases.__eo_typeof.case_76 x_a0, EoCases.__eo_typeof.case_77 x_a0, EoCases.__eo_typeof.case_78 x_a0, EoCases.__eo_typeof.case_79 x_a0] = [EoCases.__eo_typeof.case_64 x_a0, EoCases.__eo_typeof.case_65 x_a0, EoCases.__eo_typeof.case_66 x_a0, EoCases.__eo_typeof.case_67 x_a0, EoCases.__eo_typeof.case_68 x_a0, EoCases.__eo_typeof.case_69 x_a0, EoCases.__eo_typeof.case_70 x_a0, EoCases.__eo_typeof.case_71 x_a0] ++ [EoCases.__eo_typeof.case_72 x_a0, EoCases.__eo_typeof.case_73 x_a0, EoCases.__eo_typeof.case_74 x_a0, EoCases.__eo_typeof.case_75 x_a0] ++ [EoCases.__eo_typeof.case_76 x_a0, EoCases.__eo_typeof.case_77 x_a0, EoCases.__eo_typeof.case_78 x_a0, EoCases.__eo_typeof.case_79 x_a0] from rfl)
    otherwise ⟨hl_72, hl_73, hl_74, hl_75⟩ using hn_a0 hl_64 hl_65 hl_66 hl_67 hl_68 hl_69 hl_70 hl_71
  group_step with cases_0_19_eo__24eo_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_64 x_a0, EoCases.__eo_typeof.case_65 x_a0, EoCases.__eo_typeof.case_66 x_a0, EoCases.__eo_typeof.case_67 x_a0, EoCases.__eo_typeof.case_68 x_a0, EoCases.__eo_typeof.case_69 x_a0, EoCases.__eo_typeof.case_70 x_a0, EoCases.__eo_typeof.case_71 x_a0, EoCases.__eo_typeof.case_72 x_a0, EoCases.__eo_typeof.case_73 x_a0, EoCases.__eo_typeof.case_74 x_a0, EoCases.__eo_typeof.case_75 x_a0, EoCases.__eo_typeof.case_76 x_a0, EoCases.__eo_typeof.case_77 x_a0, EoCases.__eo_typeof.case_78 x_a0, EoCases.__eo_typeof.case_79 x_a0] = [EoCases.__eo_typeof.case_64 x_a0, EoCases.__eo_typeof.case_65 x_a0, EoCases.__eo_typeof.case_66 x_a0, EoCases.__eo_typeof.case_67 x_a0, EoCases.__eo_typeof.case_68 x_a0, EoCases.__eo_typeof.case_69 x_a0, EoCases.__eo_typeof.case_70 x_a0, EoCases.__eo_typeof.case_71 x_a0, EoCases.__eo_typeof.case_72 x_a0, EoCases.__eo_typeof.case_73 x_a0, EoCases.__eo_typeof.case_74 x_a0, EoCases.__eo_typeof.case_75 x_a0] ++ [EoCases.__eo_typeof.case_76 x_a0, EoCases.__eo_typeof.case_77 x_a0, EoCases.__eo_typeof.case_78 x_a0, EoCases.__eo_typeof.case_79 x_a0] ++ [] from rfl)
    otherwise ⟨hl_76, hl_77, hl_78, hl_79⟩ using hn_a0 hl_64 hl_65 hl_66 hl_67 hl_68 hl_69 hl_70 hl_71 hl_72 hl_73 hl_74 hl_75
  group_none hinv4 hG with ⟨hl_64, hl_65, hl_66, hl_67, hl_68, hl_69, hl_70, hl_71, hl_72, hl_73, hl_74, hl_75, hl_76, hl_77, hl_78, hl_79⟩

theorem cases_1_5_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    cases_1_5_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_typeof.case_80 x_a0, EoCases.__eo_typeof.case_81 x_a0, EoCases.__eo_typeof.case_82 x_a0, EoCases.__eo_typeof.case_83 x_a0, EoCases.__eo_typeof.case_84 x_a0, EoCases.__eo_typeof.case_85 x_a0, EoCases.__eo_typeof.case_86 x_a0, EoCases.__eo_typeof.case_87 x_a0, EoCases.__eo_typeof.case_88 x_a0, EoCases.__eo_typeof.case_89 x_a0, EoCases.__eo_typeof.case_90 x_a0, EoCases.__eo_typeof.case_91 x_a0, EoCases.__eo_typeof.case_92 x_a0, EoCases.__eo_typeof.case_93 x_a0, EoCases.__eo_typeof.case_94 x_a0, EoCases.__eo_typeof.case_95 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_80 x_a0 = none ∧ EoCases.__eo_typeof.case_81 x_a0 = none ∧ EoCases.__eo_typeof.case_82 x_a0 = none ∧ EoCases.__eo_typeof.case_83 x_a0 = none ∧ EoCases.__eo_typeof.case_84 x_a0 = none ∧ EoCases.__eo_typeof.case_85 x_a0 = none ∧ EoCases.__eo_typeof.case_86 x_a0 = none ∧ EoCases.__eo_typeof.case_87 x_a0 = none ∧ EoCases.__eo_typeof.case_88 x_a0 = none ∧ EoCases.__eo_typeof.case_89 x_a0 = none ∧ EoCases.__eo_typeof.case_90 x_a0 = none ∧ EoCases.__eo_typeof.case_91 x_a0 = none ∧ EoCases.__eo_typeof.case_92 x_a0 = none ∧ EoCases.__eo_typeof.case_93 x_a0 = none ∧ EoCases.__eo_typeof.case_94 x_a0 = none ∧ EoCases.__eo_typeof.case_95 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_1_5_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  group_step with cases_0_20_eo__24eo_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_80 x_a0, EoCases.__eo_typeof.case_81 x_a0, EoCases.__eo_typeof.case_82 x_a0, EoCases.__eo_typeof.case_83 x_a0, EoCases.__eo_typeof.case_84 x_a0, EoCases.__eo_typeof.case_85 x_a0, EoCases.__eo_typeof.case_86 x_a0, EoCases.__eo_typeof.case_87 x_a0, EoCases.__eo_typeof.case_88 x_a0, EoCases.__eo_typeof.case_89 x_a0, EoCases.__eo_typeof.case_90 x_a0, EoCases.__eo_typeof.case_91 x_a0, EoCases.__eo_typeof.case_92 x_a0, EoCases.__eo_typeof.case_93 x_a0, EoCases.__eo_typeof.case_94 x_a0, EoCases.__eo_typeof.case_95 x_a0] = [] ++ [EoCases.__eo_typeof.case_80 x_a0, EoCases.__eo_typeof.case_81 x_a0, EoCases.__eo_typeof.case_82 x_a0, EoCases.__eo_typeof.case_83 x_a0] ++ [EoCases.__eo_typeof.case_84 x_a0, EoCases.__eo_typeof.case_85 x_a0, EoCases.__eo_typeof.case_86 x_a0, EoCases.__eo_typeof.case_87 x_a0, EoCases.__eo_typeof.case_88 x_a0, EoCases.__eo_typeof.case_89 x_a0, EoCases.__eo_typeof.case_90 x_a0, EoCases.__eo_typeof.case_91 x_a0, EoCases.__eo_typeof.case_92 x_a0, EoCases.__eo_typeof.case_93 x_a0, EoCases.__eo_typeof.case_94 x_a0, EoCases.__eo_typeof.case_95 x_a0] from rfl)
    otherwise ⟨hl_80, hl_81, hl_82, hl_83⟩ using hn_a0
  group_step with cases_0_21_eo__24eo_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_80 x_a0, EoCases.__eo_typeof.case_81 x_a0, EoCases.__eo_typeof.case_82 x_a0, EoCases.__eo_typeof.case_83 x_a0, EoCases.__eo_typeof.case_84 x_a0, EoCases.__eo_typeof.case_85 x_a0, EoCases.__eo_typeof.case_86 x_a0, EoCases.__eo_typeof.case_87 x_a0, EoCases.__eo_typeof.case_88 x_a0, EoCases.__eo_typeof.case_89 x_a0, EoCases.__eo_typeof.case_90 x_a0, EoCases.__eo_typeof.case_91 x_a0, EoCases.__eo_typeof.case_92 x_a0, EoCases.__eo_typeof.case_93 x_a0, EoCases.__eo_typeof.case_94 x_a0, EoCases.__eo_typeof.case_95 x_a0] = [EoCases.__eo_typeof.case_80 x_a0, EoCases.__eo_typeof.case_81 x_a0, EoCases.__eo_typeof.case_82 x_a0, EoCases.__eo_typeof.case_83 x_a0] ++ [EoCases.__eo_typeof.case_84 x_a0, EoCases.__eo_typeof.case_85 x_a0, EoCases.__eo_typeof.case_86 x_a0, EoCases.__eo_typeof.case_87 x_a0] ++ [EoCases.__eo_typeof.case_88 x_a0, EoCases.__eo_typeof.case_89 x_a0, EoCases.__eo_typeof.case_90 x_a0, EoCases.__eo_typeof.case_91 x_a0, EoCases.__eo_typeof.case_92 x_a0, EoCases.__eo_typeof.case_93 x_a0, EoCases.__eo_typeof.case_94 x_a0, EoCases.__eo_typeof.case_95 x_a0] from rfl)
    otherwise ⟨hl_84, hl_85, hl_86, hl_87⟩ using hn_a0 hl_80 hl_81 hl_82 hl_83
  group_step with cases_0_22_eo__24eo_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_80 x_a0, EoCases.__eo_typeof.case_81 x_a0, EoCases.__eo_typeof.case_82 x_a0, EoCases.__eo_typeof.case_83 x_a0, EoCases.__eo_typeof.case_84 x_a0, EoCases.__eo_typeof.case_85 x_a0, EoCases.__eo_typeof.case_86 x_a0, EoCases.__eo_typeof.case_87 x_a0, EoCases.__eo_typeof.case_88 x_a0, EoCases.__eo_typeof.case_89 x_a0, EoCases.__eo_typeof.case_90 x_a0, EoCases.__eo_typeof.case_91 x_a0, EoCases.__eo_typeof.case_92 x_a0, EoCases.__eo_typeof.case_93 x_a0, EoCases.__eo_typeof.case_94 x_a0, EoCases.__eo_typeof.case_95 x_a0] = [EoCases.__eo_typeof.case_80 x_a0, EoCases.__eo_typeof.case_81 x_a0, EoCases.__eo_typeof.case_82 x_a0, EoCases.__eo_typeof.case_83 x_a0, EoCases.__eo_typeof.case_84 x_a0, EoCases.__eo_typeof.case_85 x_a0, EoCases.__eo_typeof.case_86 x_a0, EoCases.__eo_typeof.case_87 x_a0] ++ [EoCases.__eo_typeof.case_88 x_a0, EoCases.__eo_typeof.case_89 x_a0, EoCases.__eo_typeof.case_90 x_a0, EoCases.__eo_typeof.case_91 x_a0] ++ [EoCases.__eo_typeof.case_92 x_a0, EoCases.__eo_typeof.case_93 x_a0, EoCases.__eo_typeof.case_94 x_a0, EoCases.__eo_typeof.case_95 x_a0] from rfl)
    otherwise ⟨hl_88, hl_89, hl_90, hl_91⟩ using hn_a0 hl_80 hl_81 hl_82 hl_83 hl_84 hl_85 hl_86 hl_87
  group_step with cases_0_23_eo__24eo_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_80 x_a0, EoCases.__eo_typeof.case_81 x_a0, EoCases.__eo_typeof.case_82 x_a0, EoCases.__eo_typeof.case_83 x_a0, EoCases.__eo_typeof.case_84 x_a0, EoCases.__eo_typeof.case_85 x_a0, EoCases.__eo_typeof.case_86 x_a0, EoCases.__eo_typeof.case_87 x_a0, EoCases.__eo_typeof.case_88 x_a0, EoCases.__eo_typeof.case_89 x_a0, EoCases.__eo_typeof.case_90 x_a0, EoCases.__eo_typeof.case_91 x_a0, EoCases.__eo_typeof.case_92 x_a0, EoCases.__eo_typeof.case_93 x_a0, EoCases.__eo_typeof.case_94 x_a0, EoCases.__eo_typeof.case_95 x_a0] = [EoCases.__eo_typeof.case_80 x_a0, EoCases.__eo_typeof.case_81 x_a0, EoCases.__eo_typeof.case_82 x_a0, EoCases.__eo_typeof.case_83 x_a0, EoCases.__eo_typeof.case_84 x_a0, EoCases.__eo_typeof.case_85 x_a0, EoCases.__eo_typeof.case_86 x_a0, EoCases.__eo_typeof.case_87 x_a0, EoCases.__eo_typeof.case_88 x_a0, EoCases.__eo_typeof.case_89 x_a0, EoCases.__eo_typeof.case_90 x_a0, EoCases.__eo_typeof.case_91 x_a0] ++ [EoCases.__eo_typeof.case_92 x_a0, EoCases.__eo_typeof.case_93 x_a0, EoCases.__eo_typeof.case_94 x_a0, EoCases.__eo_typeof.case_95 x_a0] ++ [] from rfl)
    otherwise ⟨hl_92, hl_93, hl_94, hl_95⟩ using hn_a0 hl_80 hl_81 hl_82 hl_83 hl_84 hl_85 hl_86 hl_87 hl_88 hl_89 hl_90 hl_91
  group_none hinv4 hG with ⟨hl_80, hl_81, hl_82, hl_83, hl_84, hl_85, hl_86, hl_87, hl_88, hl_89, hl_90, hl_91, hl_92, hl_93, hl_94, hl_95⟩

theorem cases_1_6_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    cases_1_6_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_typeof.case_96 x_a0, EoCases.__eo_typeof.case_97 x_a0, EoCases.__eo_typeof.case_98 x_a0, EoCases.__eo_typeof.case_99 x_a0, EoCases.__eo_typeof.case_100 x_a0, EoCases.__eo_typeof.case_101 x_a0, EoCases.__eo_typeof.case_102 x_a0, EoCases.__eo_typeof.case_103 x_a0, EoCases.__eo_typeof.case_104 x_a0, EoCases.__eo_typeof.case_105 x_a0, EoCases.__eo_typeof.case_106 x_a0, EoCases.__eo_typeof.case_107 x_a0, EoCases.__eo_typeof.case_108 x_a0, EoCases.__eo_typeof.case_109 x_a0, EoCases.__eo_typeof.case_110 x_a0, EoCases.__eo_typeof.case_111 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_96 x_a0 = none ∧ EoCases.__eo_typeof.case_97 x_a0 = none ∧ EoCases.__eo_typeof.case_98 x_a0 = none ∧ EoCases.__eo_typeof.case_99 x_a0 = none ∧ EoCases.__eo_typeof.case_100 x_a0 = none ∧ EoCases.__eo_typeof.case_101 x_a0 = none ∧ EoCases.__eo_typeof.case_102 x_a0 = none ∧ EoCases.__eo_typeof.case_103 x_a0 = none ∧ EoCases.__eo_typeof.case_104 x_a0 = none ∧ EoCases.__eo_typeof.case_105 x_a0 = none ∧ EoCases.__eo_typeof.case_106 x_a0 = none ∧ EoCases.__eo_typeof.case_107 x_a0 = none ∧ EoCases.__eo_typeof.case_108 x_a0 = none ∧ EoCases.__eo_typeof.case_109 x_a0 = none ∧ EoCases.__eo_typeof.case_110 x_a0 = none ∧ EoCases.__eo_typeof.case_111 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_1_6_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  group_step with cases_0_24_eo__24eo_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_96 x_a0, EoCases.__eo_typeof.case_97 x_a0, EoCases.__eo_typeof.case_98 x_a0, EoCases.__eo_typeof.case_99 x_a0, EoCases.__eo_typeof.case_100 x_a0, EoCases.__eo_typeof.case_101 x_a0, EoCases.__eo_typeof.case_102 x_a0, EoCases.__eo_typeof.case_103 x_a0, EoCases.__eo_typeof.case_104 x_a0, EoCases.__eo_typeof.case_105 x_a0, EoCases.__eo_typeof.case_106 x_a0, EoCases.__eo_typeof.case_107 x_a0, EoCases.__eo_typeof.case_108 x_a0, EoCases.__eo_typeof.case_109 x_a0, EoCases.__eo_typeof.case_110 x_a0, EoCases.__eo_typeof.case_111 x_a0] = [] ++ [EoCases.__eo_typeof.case_96 x_a0, EoCases.__eo_typeof.case_97 x_a0, EoCases.__eo_typeof.case_98 x_a0, EoCases.__eo_typeof.case_99 x_a0] ++ [EoCases.__eo_typeof.case_100 x_a0, EoCases.__eo_typeof.case_101 x_a0, EoCases.__eo_typeof.case_102 x_a0, EoCases.__eo_typeof.case_103 x_a0, EoCases.__eo_typeof.case_104 x_a0, EoCases.__eo_typeof.case_105 x_a0, EoCases.__eo_typeof.case_106 x_a0, EoCases.__eo_typeof.case_107 x_a0, EoCases.__eo_typeof.case_108 x_a0, EoCases.__eo_typeof.case_109 x_a0, EoCases.__eo_typeof.case_110 x_a0, EoCases.__eo_typeof.case_111 x_a0] from rfl)
    otherwise ⟨hl_96, hl_97, hl_98, hl_99⟩ using hn_a0
  group_step with cases_0_25_eo__24eo_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_96 x_a0, EoCases.__eo_typeof.case_97 x_a0, EoCases.__eo_typeof.case_98 x_a0, EoCases.__eo_typeof.case_99 x_a0, EoCases.__eo_typeof.case_100 x_a0, EoCases.__eo_typeof.case_101 x_a0, EoCases.__eo_typeof.case_102 x_a0, EoCases.__eo_typeof.case_103 x_a0, EoCases.__eo_typeof.case_104 x_a0, EoCases.__eo_typeof.case_105 x_a0, EoCases.__eo_typeof.case_106 x_a0, EoCases.__eo_typeof.case_107 x_a0, EoCases.__eo_typeof.case_108 x_a0, EoCases.__eo_typeof.case_109 x_a0, EoCases.__eo_typeof.case_110 x_a0, EoCases.__eo_typeof.case_111 x_a0] = [EoCases.__eo_typeof.case_96 x_a0, EoCases.__eo_typeof.case_97 x_a0, EoCases.__eo_typeof.case_98 x_a0, EoCases.__eo_typeof.case_99 x_a0] ++ [EoCases.__eo_typeof.case_100 x_a0, EoCases.__eo_typeof.case_101 x_a0, EoCases.__eo_typeof.case_102 x_a0, EoCases.__eo_typeof.case_103 x_a0] ++ [EoCases.__eo_typeof.case_104 x_a0, EoCases.__eo_typeof.case_105 x_a0, EoCases.__eo_typeof.case_106 x_a0, EoCases.__eo_typeof.case_107 x_a0, EoCases.__eo_typeof.case_108 x_a0, EoCases.__eo_typeof.case_109 x_a0, EoCases.__eo_typeof.case_110 x_a0, EoCases.__eo_typeof.case_111 x_a0] from rfl)
    otherwise ⟨hl_100, hl_101, hl_102, hl_103⟩ using hn_a0 hl_96 hl_97 hl_98 hl_99
  group_step with cases_0_26_eo__24eo_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_96 x_a0, EoCases.__eo_typeof.case_97 x_a0, EoCases.__eo_typeof.case_98 x_a0, EoCases.__eo_typeof.case_99 x_a0, EoCases.__eo_typeof.case_100 x_a0, EoCases.__eo_typeof.case_101 x_a0, EoCases.__eo_typeof.case_102 x_a0, EoCases.__eo_typeof.case_103 x_a0, EoCases.__eo_typeof.case_104 x_a0, EoCases.__eo_typeof.case_105 x_a0, EoCases.__eo_typeof.case_106 x_a0, EoCases.__eo_typeof.case_107 x_a0, EoCases.__eo_typeof.case_108 x_a0, EoCases.__eo_typeof.case_109 x_a0, EoCases.__eo_typeof.case_110 x_a0, EoCases.__eo_typeof.case_111 x_a0] = [EoCases.__eo_typeof.case_96 x_a0, EoCases.__eo_typeof.case_97 x_a0, EoCases.__eo_typeof.case_98 x_a0, EoCases.__eo_typeof.case_99 x_a0, EoCases.__eo_typeof.case_100 x_a0, EoCases.__eo_typeof.case_101 x_a0, EoCases.__eo_typeof.case_102 x_a0, EoCases.__eo_typeof.case_103 x_a0] ++ [EoCases.__eo_typeof.case_104 x_a0, EoCases.__eo_typeof.case_105 x_a0, EoCases.__eo_typeof.case_106 x_a0, EoCases.__eo_typeof.case_107 x_a0] ++ [EoCases.__eo_typeof.case_108 x_a0, EoCases.__eo_typeof.case_109 x_a0, EoCases.__eo_typeof.case_110 x_a0, EoCases.__eo_typeof.case_111 x_a0] from rfl)
    otherwise ⟨hl_104, hl_105, hl_106, hl_107⟩ using hn_a0 hl_96 hl_97 hl_98 hl_99 hl_100 hl_101 hl_102 hl_103
  group_step with cases_0_27_eo__24eo_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_96 x_a0, EoCases.__eo_typeof.case_97 x_a0, EoCases.__eo_typeof.case_98 x_a0, EoCases.__eo_typeof.case_99 x_a0, EoCases.__eo_typeof.case_100 x_a0, EoCases.__eo_typeof.case_101 x_a0, EoCases.__eo_typeof.case_102 x_a0, EoCases.__eo_typeof.case_103 x_a0, EoCases.__eo_typeof.case_104 x_a0, EoCases.__eo_typeof.case_105 x_a0, EoCases.__eo_typeof.case_106 x_a0, EoCases.__eo_typeof.case_107 x_a0, EoCases.__eo_typeof.case_108 x_a0, EoCases.__eo_typeof.case_109 x_a0, EoCases.__eo_typeof.case_110 x_a0, EoCases.__eo_typeof.case_111 x_a0] = [EoCases.__eo_typeof.case_96 x_a0, EoCases.__eo_typeof.case_97 x_a0, EoCases.__eo_typeof.case_98 x_a0, EoCases.__eo_typeof.case_99 x_a0, EoCases.__eo_typeof.case_100 x_a0, EoCases.__eo_typeof.case_101 x_a0, EoCases.__eo_typeof.case_102 x_a0, EoCases.__eo_typeof.case_103 x_a0, EoCases.__eo_typeof.case_104 x_a0, EoCases.__eo_typeof.case_105 x_a0, EoCases.__eo_typeof.case_106 x_a0, EoCases.__eo_typeof.case_107 x_a0] ++ [EoCases.__eo_typeof.case_108 x_a0, EoCases.__eo_typeof.case_109 x_a0, EoCases.__eo_typeof.case_110 x_a0, EoCases.__eo_typeof.case_111 x_a0] ++ [] from rfl)
    otherwise ⟨hl_108, hl_109, hl_110, hl_111⟩ using hn_a0 hl_96 hl_97 hl_98 hl_99 hl_100 hl_101 hl_102 hl_103 hl_104 hl_105 hl_106 hl_107
  group_none hinv4 hG with ⟨hl_96, hl_97, hl_98, hl_99, hl_100, hl_101, hl_102, hl_103, hl_104, hl_105, hl_106, hl_107, hl_108, hl_109, hl_110, hl_111⟩

theorem cases_1_7_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    cases_1_7_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_typeof.case_112 x_a0, EoCases.__eo_typeof.case_113 x_a0, EoCases.__eo_typeof.case_114 x_a0, EoCases.__eo_typeof.case_115 x_a0, EoCases.__eo_typeof.case_116 x_a0, EoCases.__eo_typeof.case_117 x_a0, EoCases.__eo_typeof.case_118 x_a0, EoCases.__eo_typeof.case_119 x_a0, EoCases.__eo_typeof.case_120 x_a0, EoCases.__eo_typeof.case_121 x_a0, EoCases.__eo_typeof.case_122 x_a0, EoCases.__eo_typeof.case_123 x_a0, EoCases.__eo_typeof.case_124 x_a0, EoCases.__eo_typeof.case_125 x_a0, EoCases.__eo_typeof.case_126 x_a0, EoCases.__eo_typeof.case_127 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_112 x_a0 = none ∧ EoCases.__eo_typeof.case_113 x_a0 = none ∧ EoCases.__eo_typeof.case_114 x_a0 = none ∧ EoCases.__eo_typeof.case_115 x_a0 = none ∧ EoCases.__eo_typeof.case_116 x_a0 = none ∧ EoCases.__eo_typeof.case_117 x_a0 = none ∧ EoCases.__eo_typeof.case_118 x_a0 = none ∧ EoCases.__eo_typeof.case_119 x_a0 = none ∧ EoCases.__eo_typeof.case_120 x_a0 = none ∧ EoCases.__eo_typeof.case_121 x_a0 = none ∧ EoCases.__eo_typeof.case_122 x_a0 = none ∧ EoCases.__eo_typeof.case_123 x_a0 = none ∧ EoCases.__eo_typeof.case_124 x_a0 = none ∧ EoCases.__eo_typeof.case_125 x_a0 = none ∧ EoCases.__eo_typeof.case_126 x_a0 = none ∧ EoCases.__eo_typeof.case_127 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_1_7_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  group_step with cases_0_28_eo__24eo_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_112 x_a0, EoCases.__eo_typeof.case_113 x_a0, EoCases.__eo_typeof.case_114 x_a0, EoCases.__eo_typeof.case_115 x_a0, EoCases.__eo_typeof.case_116 x_a0, EoCases.__eo_typeof.case_117 x_a0, EoCases.__eo_typeof.case_118 x_a0, EoCases.__eo_typeof.case_119 x_a0, EoCases.__eo_typeof.case_120 x_a0, EoCases.__eo_typeof.case_121 x_a0, EoCases.__eo_typeof.case_122 x_a0, EoCases.__eo_typeof.case_123 x_a0, EoCases.__eo_typeof.case_124 x_a0, EoCases.__eo_typeof.case_125 x_a0, EoCases.__eo_typeof.case_126 x_a0, EoCases.__eo_typeof.case_127 x_a0] = [] ++ [EoCases.__eo_typeof.case_112 x_a0, EoCases.__eo_typeof.case_113 x_a0, EoCases.__eo_typeof.case_114 x_a0, EoCases.__eo_typeof.case_115 x_a0] ++ [EoCases.__eo_typeof.case_116 x_a0, EoCases.__eo_typeof.case_117 x_a0, EoCases.__eo_typeof.case_118 x_a0, EoCases.__eo_typeof.case_119 x_a0, EoCases.__eo_typeof.case_120 x_a0, EoCases.__eo_typeof.case_121 x_a0, EoCases.__eo_typeof.case_122 x_a0, EoCases.__eo_typeof.case_123 x_a0, EoCases.__eo_typeof.case_124 x_a0, EoCases.__eo_typeof.case_125 x_a0, EoCases.__eo_typeof.case_126 x_a0, EoCases.__eo_typeof.case_127 x_a0] from rfl)
    otherwise ⟨hl_112, hl_113, hl_114, hl_115⟩ using hn_a0
  group_step with cases_0_29_eo__24eo_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_112 x_a0, EoCases.__eo_typeof.case_113 x_a0, EoCases.__eo_typeof.case_114 x_a0, EoCases.__eo_typeof.case_115 x_a0, EoCases.__eo_typeof.case_116 x_a0, EoCases.__eo_typeof.case_117 x_a0, EoCases.__eo_typeof.case_118 x_a0, EoCases.__eo_typeof.case_119 x_a0, EoCases.__eo_typeof.case_120 x_a0, EoCases.__eo_typeof.case_121 x_a0, EoCases.__eo_typeof.case_122 x_a0, EoCases.__eo_typeof.case_123 x_a0, EoCases.__eo_typeof.case_124 x_a0, EoCases.__eo_typeof.case_125 x_a0, EoCases.__eo_typeof.case_126 x_a0, EoCases.__eo_typeof.case_127 x_a0] = [EoCases.__eo_typeof.case_112 x_a0, EoCases.__eo_typeof.case_113 x_a0, EoCases.__eo_typeof.case_114 x_a0, EoCases.__eo_typeof.case_115 x_a0] ++ [EoCases.__eo_typeof.case_116 x_a0, EoCases.__eo_typeof.case_117 x_a0, EoCases.__eo_typeof.case_118 x_a0, EoCases.__eo_typeof.case_119 x_a0] ++ [EoCases.__eo_typeof.case_120 x_a0, EoCases.__eo_typeof.case_121 x_a0, EoCases.__eo_typeof.case_122 x_a0, EoCases.__eo_typeof.case_123 x_a0, EoCases.__eo_typeof.case_124 x_a0, EoCases.__eo_typeof.case_125 x_a0, EoCases.__eo_typeof.case_126 x_a0, EoCases.__eo_typeof.case_127 x_a0] from rfl)
    otherwise ⟨hl_116, hl_117, hl_118, hl_119⟩ using hn_a0 hl_112 hl_113 hl_114 hl_115
  group_step with cases_0_30_eo__24eo_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_112 x_a0, EoCases.__eo_typeof.case_113 x_a0, EoCases.__eo_typeof.case_114 x_a0, EoCases.__eo_typeof.case_115 x_a0, EoCases.__eo_typeof.case_116 x_a0, EoCases.__eo_typeof.case_117 x_a0, EoCases.__eo_typeof.case_118 x_a0, EoCases.__eo_typeof.case_119 x_a0, EoCases.__eo_typeof.case_120 x_a0, EoCases.__eo_typeof.case_121 x_a0, EoCases.__eo_typeof.case_122 x_a0, EoCases.__eo_typeof.case_123 x_a0, EoCases.__eo_typeof.case_124 x_a0, EoCases.__eo_typeof.case_125 x_a0, EoCases.__eo_typeof.case_126 x_a0, EoCases.__eo_typeof.case_127 x_a0] = [EoCases.__eo_typeof.case_112 x_a0, EoCases.__eo_typeof.case_113 x_a0, EoCases.__eo_typeof.case_114 x_a0, EoCases.__eo_typeof.case_115 x_a0, EoCases.__eo_typeof.case_116 x_a0, EoCases.__eo_typeof.case_117 x_a0, EoCases.__eo_typeof.case_118 x_a0, EoCases.__eo_typeof.case_119 x_a0] ++ [EoCases.__eo_typeof.case_120 x_a0, EoCases.__eo_typeof.case_121 x_a0, EoCases.__eo_typeof.case_122 x_a0, EoCases.__eo_typeof.case_123 x_a0] ++ [EoCases.__eo_typeof.case_124 x_a0, EoCases.__eo_typeof.case_125 x_a0, EoCases.__eo_typeof.case_126 x_a0, EoCases.__eo_typeof.case_127 x_a0] from rfl)
    otherwise ⟨hl_120, hl_121, hl_122, hl_123⟩ using hn_a0 hl_112 hl_113 hl_114 hl_115 hl_116 hl_117 hl_118 hl_119
  group_step with cases_0_31_eo__24eo_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_112 x_a0, EoCases.__eo_typeof.case_113 x_a0, EoCases.__eo_typeof.case_114 x_a0, EoCases.__eo_typeof.case_115 x_a0, EoCases.__eo_typeof.case_116 x_a0, EoCases.__eo_typeof.case_117 x_a0, EoCases.__eo_typeof.case_118 x_a0, EoCases.__eo_typeof.case_119 x_a0, EoCases.__eo_typeof.case_120 x_a0, EoCases.__eo_typeof.case_121 x_a0, EoCases.__eo_typeof.case_122 x_a0, EoCases.__eo_typeof.case_123 x_a0, EoCases.__eo_typeof.case_124 x_a0, EoCases.__eo_typeof.case_125 x_a0, EoCases.__eo_typeof.case_126 x_a0, EoCases.__eo_typeof.case_127 x_a0] = [EoCases.__eo_typeof.case_112 x_a0, EoCases.__eo_typeof.case_113 x_a0, EoCases.__eo_typeof.case_114 x_a0, EoCases.__eo_typeof.case_115 x_a0, EoCases.__eo_typeof.case_116 x_a0, EoCases.__eo_typeof.case_117 x_a0, EoCases.__eo_typeof.case_118 x_a0, EoCases.__eo_typeof.case_119 x_a0, EoCases.__eo_typeof.case_120 x_a0, EoCases.__eo_typeof.case_121 x_a0, EoCases.__eo_typeof.case_122 x_a0, EoCases.__eo_typeof.case_123 x_a0] ++ [EoCases.__eo_typeof.case_124 x_a0, EoCases.__eo_typeof.case_125 x_a0, EoCases.__eo_typeof.case_126 x_a0, EoCases.__eo_typeof.case_127 x_a0] ++ [] from rfl)
    otherwise ⟨hl_124, hl_125, hl_126, hl_127⟩ using hn_a0 hl_112 hl_113 hl_114 hl_115 hl_116 hl_117 hl_118 hl_119 hl_120 hl_121 hl_122 hl_123
  group_none hinv4 hG with ⟨hl_112, hl_113, hl_114, hl_115, hl_116, hl_117, hl_118, hl_119, hl_120, hl_121, hl_122, hl_123, hl_124, hl_125, hl_126, hl_127⟩

theorem cases_1_8_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    cases_1_8_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_typeof.case_128 x_a0, EoCases.__eo_typeof.case_129 x_a0, EoCases.__eo_typeof.case_130 x_a0, EoCases.__eo_typeof.case_131 x_a0, EoCases.__eo_typeof.case_132 x_a0, EoCases.__eo_typeof.case_133 x_a0, EoCases.__eo_typeof.case_134 x_a0, EoCases.__eo_typeof.case_135 x_a0, EoCases.__eo_typeof.case_136 x_a0, EoCases.__eo_typeof.case_137 x_a0, EoCases.__eo_typeof.case_138 x_a0, EoCases.__eo_typeof.case_139 x_a0, EoCases.__eo_typeof.case_140 x_a0, EoCases.__eo_typeof.case_141 x_a0, EoCases.__eo_typeof.case_142 x_a0, EoCases.__eo_typeof.case_143 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_128 x_a0 = none ∧ EoCases.__eo_typeof.case_129 x_a0 = none ∧ EoCases.__eo_typeof.case_130 x_a0 = none ∧ EoCases.__eo_typeof.case_131 x_a0 = none ∧ EoCases.__eo_typeof.case_132 x_a0 = none ∧ EoCases.__eo_typeof.case_133 x_a0 = none ∧ EoCases.__eo_typeof.case_134 x_a0 = none ∧ EoCases.__eo_typeof.case_135 x_a0 = none ∧ EoCases.__eo_typeof.case_136 x_a0 = none ∧ EoCases.__eo_typeof.case_137 x_a0 = none ∧ EoCases.__eo_typeof.case_138 x_a0 = none ∧ EoCases.__eo_typeof.case_139 x_a0 = none ∧ EoCases.__eo_typeof.case_140 x_a0 = none ∧ EoCases.__eo_typeof.case_141 x_a0 = none ∧ EoCases.__eo_typeof.case_142 x_a0 = none ∧ EoCases.__eo_typeof.case_143 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_1_8_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  group_step with cases_0_32_eo__24eo_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_128 x_a0, EoCases.__eo_typeof.case_129 x_a0, EoCases.__eo_typeof.case_130 x_a0, EoCases.__eo_typeof.case_131 x_a0, EoCases.__eo_typeof.case_132 x_a0, EoCases.__eo_typeof.case_133 x_a0, EoCases.__eo_typeof.case_134 x_a0, EoCases.__eo_typeof.case_135 x_a0, EoCases.__eo_typeof.case_136 x_a0, EoCases.__eo_typeof.case_137 x_a0, EoCases.__eo_typeof.case_138 x_a0, EoCases.__eo_typeof.case_139 x_a0, EoCases.__eo_typeof.case_140 x_a0, EoCases.__eo_typeof.case_141 x_a0, EoCases.__eo_typeof.case_142 x_a0, EoCases.__eo_typeof.case_143 x_a0] = [] ++ [EoCases.__eo_typeof.case_128 x_a0, EoCases.__eo_typeof.case_129 x_a0, EoCases.__eo_typeof.case_130 x_a0, EoCases.__eo_typeof.case_131 x_a0] ++ [EoCases.__eo_typeof.case_132 x_a0, EoCases.__eo_typeof.case_133 x_a0, EoCases.__eo_typeof.case_134 x_a0, EoCases.__eo_typeof.case_135 x_a0, EoCases.__eo_typeof.case_136 x_a0, EoCases.__eo_typeof.case_137 x_a0, EoCases.__eo_typeof.case_138 x_a0, EoCases.__eo_typeof.case_139 x_a0, EoCases.__eo_typeof.case_140 x_a0, EoCases.__eo_typeof.case_141 x_a0, EoCases.__eo_typeof.case_142 x_a0, EoCases.__eo_typeof.case_143 x_a0] from rfl)
    otherwise ⟨hl_128, hl_129, hl_130, hl_131⟩ using hn_a0
  group_step with cases_0_33_eo__24eo_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_128 x_a0, EoCases.__eo_typeof.case_129 x_a0, EoCases.__eo_typeof.case_130 x_a0, EoCases.__eo_typeof.case_131 x_a0, EoCases.__eo_typeof.case_132 x_a0, EoCases.__eo_typeof.case_133 x_a0, EoCases.__eo_typeof.case_134 x_a0, EoCases.__eo_typeof.case_135 x_a0, EoCases.__eo_typeof.case_136 x_a0, EoCases.__eo_typeof.case_137 x_a0, EoCases.__eo_typeof.case_138 x_a0, EoCases.__eo_typeof.case_139 x_a0, EoCases.__eo_typeof.case_140 x_a0, EoCases.__eo_typeof.case_141 x_a0, EoCases.__eo_typeof.case_142 x_a0, EoCases.__eo_typeof.case_143 x_a0] = [EoCases.__eo_typeof.case_128 x_a0, EoCases.__eo_typeof.case_129 x_a0, EoCases.__eo_typeof.case_130 x_a0, EoCases.__eo_typeof.case_131 x_a0] ++ [EoCases.__eo_typeof.case_132 x_a0, EoCases.__eo_typeof.case_133 x_a0, EoCases.__eo_typeof.case_134 x_a0, EoCases.__eo_typeof.case_135 x_a0] ++ [EoCases.__eo_typeof.case_136 x_a0, EoCases.__eo_typeof.case_137 x_a0, EoCases.__eo_typeof.case_138 x_a0, EoCases.__eo_typeof.case_139 x_a0, EoCases.__eo_typeof.case_140 x_a0, EoCases.__eo_typeof.case_141 x_a0, EoCases.__eo_typeof.case_142 x_a0, EoCases.__eo_typeof.case_143 x_a0] from rfl)
    otherwise ⟨hl_132, hl_133, hl_134, hl_135⟩ using hn_a0 hl_128 hl_129 hl_130 hl_131
  group_step with cases_0_34_eo__24eo_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_128 x_a0, EoCases.__eo_typeof.case_129 x_a0, EoCases.__eo_typeof.case_130 x_a0, EoCases.__eo_typeof.case_131 x_a0, EoCases.__eo_typeof.case_132 x_a0, EoCases.__eo_typeof.case_133 x_a0, EoCases.__eo_typeof.case_134 x_a0, EoCases.__eo_typeof.case_135 x_a0, EoCases.__eo_typeof.case_136 x_a0, EoCases.__eo_typeof.case_137 x_a0, EoCases.__eo_typeof.case_138 x_a0, EoCases.__eo_typeof.case_139 x_a0, EoCases.__eo_typeof.case_140 x_a0, EoCases.__eo_typeof.case_141 x_a0, EoCases.__eo_typeof.case_142 x_a0, EoCases.__eo_typeof.case_143 x_a0] = [EoCases.__eo_typeof.case_128 x_a0, EoCases.__eo_typeof.case_129 x_a0, EoCases.__eo_typeof.case_130 x_a0, EoCases.__eo_typeof.case_131 x_a0, EoCases.__eo_typeof.case_132 x_a0, EoCases.__eo_typeof.case_133 x_a0, EoCases.__eo_typeof.case_134 x_a0, EoCases.__eo_typeof.case_135 x_a0] ++ [EoCases.__eo_typeof.case_136 x_a0, EoCases.__eo_typeof.case_137 x_a0, EoCases.__eo_typeof.case_138 x_a0, EoCases.__eo_typeof.case_139 x_a0] ++ [EoCases.__eo_typeof.case_140 x_a0, EoCases.__eo_typeof.case_141 x_a0, EoCases.__eo_typeof.case_142 x_a0, EoCases.__eo_typeof.case_143 x_a0] from rfl)
    otherwise ⟨hl_136, hl_137, hl_138, hl_139⟩ using hn_a0 hl_128 hl_129 hl_130 hl_131 hl_132 hl_133 hl_134 hl_135
  group_step with cases_0_35_eo__24eo_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_128 x_a0, EoCases.__eo_typeof.case_129 x_a0, EoCases.__eo_typeof.case_130 x_a0, EoCases.__eo_typeof.case_131 x_a0, EoCases.__eo_typeof.case_132 x_a0, EoCases.__eo_typeof.case_133 x_a0, EoCases.__eo_typeof.case_134 x_a0, EoCases.__eo_typeof.case_135 x_a0, EoCases.__eo_typeof.case_136 x_a0, EoCases.__eo_typeof.case_137 x_a0, EoCases.__eo_typeof.case_138 x_a0, EoCases.__eo_typeof.case_139 x_a0, EoCases.__eo_typeof.case_140 x_a0, EoCases.__eo_typeof.case_141 x_a0, EoCases.__eo_typeof.case_142 x_a0, EoCases.__eo_typeof.case_143 x_a0] = [EoCases.__eo_typeof.case_128 x_a0, EoCases.__eo_typeof.case_129 x_a0, EoCases.__eo_typeof.case_130 x_a0, EoCases.__eo_typeof.case_131 x_a0, EoCases.__eo_typeof.case_132 x_a0, EoCases.__eo_typeof.case_133 x_a0, EoCases.__eo_typeof.case_134 x_a0, EoCases.__eo_typeof.case_135 x_a0, EoCases.__eo_typeof.case_136 x_a0, EoCases.__eo_typeof.case_137 x_a0, EoCases.__eo_typeof.case_138 x_a0, EoCases.__eo_typeof.case_139 x_a0] ++ [EoCases.__eo_typeof.case_140 x_a0, EoCases.__eo_typeof.case_141 x_a0, EoCases.__eo_typeof.case_142 x_a0, EoCases.__eo_typeof.case_143 x_a0] ++ [] from rfl)
    otherwise ⟨hl_140, hl_141, hl_142, hl_143⟩ using hn_a0 hl_128 hl_129 hl_130 hl_131 hl_132 hl_133 hl_134 hl_135 hl_136 hl_137 hl_138 hl_139
  group_none hinv4 hG with ⟨hl_128, hl_129, hl_130, hl_131, hl_132, hl_133, hl_134, hl_135, hl_136, hl_137, hl_138, hl_139, hl_140, hl_141, hl_142, hl_143⟩

theorem cases_1_9_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    cases_1_9_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_typeof.case_144 x_a0, EoCases.__eo_typeof.case_145 x_a0, EoCases.__eo_typeof.case_146 x_a0, EoCases.__eo_typeof.case_147 x_a0, EoCases.__eo_typeof.case_148 x_a0, EoCases.__eo_typeof.case_149 x_a0, EoCases.__eo_typeof.case_150 x_a0, EoCases.__eo_typeof.case_151 x_a0, EoCases.__eo_typeof.case_152 x_a0, EoCases.__eo_typeof.case_153 x_a0, EoCases.__eo_typeof.case_154 x_a0, EoCases.__eo_typeof.case_155 x_a0, EoCases.__eo_typeof.case_156 x_a0, EoCases.__eo_typeof.case_157 x_a0, EoCases.__eo_typeof.case_158 x_a0, EoCases.__eo_typeof.case_159 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_144 x_a0 = none ∧ EoCases.__eo_typeof.case_145 x_a0 = none ∧ EoCases.__eo_typeof.case_146 x_a0 = none ∧ EoCases.__eo_typeof.case_147 x_a0 = none ∧ EoCases.__eo_typeof.case_148 x_a0 = none ∧ EoCases.__eo_typeof.case_149 x_a0 = none ∧ EoCases.__eo_typeof.case_150 x_a0 = none ∧ EoCases.__eo_typeof.case_151 x_a0 = none ∧ EoCases.__eo_typeof.case_152 x_a0 = none ∧ EoCases.__eo_typeof.case_153 x_a0 = none ∧ EoCases.__eo_typeof.case_154 x_a0 = none ∧ EoCases.__eo_typeof.case_155 x_a0 = none ∧ EoCases.__eo_typeof.case_156 x_a0 = none ∧ EoCases.__eo_typeof.case_157 x_a0 = none ∧ EoCases.__eo_typeof.case_158 x_a0 = none ∧ EoCases.__eo_typeof.case_159 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_1_9_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  group_step with cases_0_36_eo__24eo_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_144 x_a0, EoCases.__eo_typeof.case_145 x_a0, EoCases.__eo_typeof.case_146 x_a0, EoCases.__eo_typeof.case_147 x_a0, EoCases.__eo_typeof.case_148 x_a0, EoCases.__eo_typeof.case_149 x_a0, EoCases.__eo_typeof.case_150 x_a0, EoCases.__eo_typeof.case_151 x_a0, EoCases.__eo_typeof.case_152 x_a0, EoCases.__eo_typeof.case_153 x_a0, EoCases.__eo_typeof.case_154 x_a0, EoCases.__eo_typeof.case_155 x_a0, EoCases.__eo_typeof.case_156 x_a0, EoCases.__eo_typeof.case_157 x_a0, EoCases.__eo_typeof.case_158 x_a0, EoCases.__eo_typeof.case_159 x_a0] = [] ++ [EoCases.__eo_typeof.case_144 x_a0, EoCases.__eo_typeof.case_145 x_a0, EoCases.__eo_typeof.case_146 x_a0, EoCases.__eo_typeof.case_147 x_a0] ++ [EoCases.__eo_typeof.case_148 x_a0, EoCases.__eo_typeof.case_149 x_a0, EoCases.__eo_typeof.case_150 x_a0, EoCases.__eo_typeof.case_151 x_a0, EoCases.__eo_typeof.case_152 x_a0, EoCases.__eo_typeof.case_153 x_a0, EoCases.__eo_typeof.case_154 x_a0, EoCases.__eo_typeof.case_155 x_a0, EoCases.__eo_typeof.case_156 x_a0, EoCases.__eo_typeof.case_157 x_a0, EoCases.__eo_typeof.case_158 x_a0, EoCases.__eo_typeof.case_159 x_a0] from rfl)
    otherwise ⟨hl_144, hl_145, hl_146, hl_147⟩ using hn_a0
  group_step with cases_0_37_eo__24eo_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_144 x_a0, EoCases.__eo_typeof.case_145 x_a0, EoCases.__eo_typeof.case_146 x_a0, EoCases.__eo_typeof.case_147 x_a0, EoCases.__eo_typeof.case_148 x_a0, EoCases.__eo_typeof.case_149 x_a0, EoCases.__eo_typeof.case_150 x_a0, EoCases.__eo_typeof.case_151 x_a0, EoCases.__eo_typeof.case_152 x_a0, EoCases.__eo_typeof.case_153 x_a0, EoCases.__eo_typeof.case_154 x_a0, EoCases.__eo_typeof.case_155 x_a0, EoCases.__eo_typeof.case_156 x_a0, EoCases.__eo_typeof.case_157 x_a0, EoCases.__eo_typeof.case_158 x_a0, EoCases.__eo_typeof.case_159 x_a0] = [EoCases.__eo_typeof.case_144 x_a0, EoCases.__eo_typeof.case_145 x_a0, EoCases.__eo_typeof.case_146 x_a0, EoCases.__eo_typeof.case_147 x_a0] ++ [EoCases.__eo_typeof.case_148 x_a0, EoCases.__eo_typeof.case_149 x_a0, EoCases.__eo_typeof.case_150 x_a0, EoCases.__eo_typeof.case_151 x_a0] ++ [EoCases.__eo_typeof.case_152 x_a0, EoCases.__eo_typeof.case_153 x_a0, EoCases.__eo_typeof.case_154 x_a0, EoCases.__eo_typeof.case_155 x_a0, EoCases.__eo_typeof.case_156 x_a0, EoCases.__eo_typeof.case_157 x_a0, EoCases.__eo_typeof.case_158 x_a0, EoCases.__eo_typeof.case_159 x_a0] from rfl)
    otherwise ⟨hl_148, hl_149, hl_150, hl_151⟩ using hn_a0 hl_144 hl_145 hl_146 hl_147
  group_step with cases_0_38_eo__24eo_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_144 x_a0, EoCases.__eo_typeof.case_145 x_a0, EoCases.__eo_typeof.case_146 x_a0, EoCases.__eo_typeof.case_147 x_a0, EoCases.__eo_typeof.case_148 x_a0, EoCases.__eo_typeof.case_149 x_a0, EoCases.__eo_typeof.case_150 x_a0, EoCases.__eo_typeof.case_151 x_a0, EoCases.__eo_typeof.case_152 x_a0, EoCases.__eo_typeof.case_153 x_a0, EoCases.__eo_typeof.case_154 x_a0, EoCases.__eo_typeof.case_155 x_a0, EoCases.__eo_typeof.case_156 x_a0, EoCases.__eo_typeof.case_157 x_a0, EoCases.__eo_typeof.case_158 x_a0, EoCases.__eo_typeof.case_159 x_a0] = [EoCases.__eo_typeof.case_144 x_a0, EoCases.__eo_typeof.case_145 x_a0, EoCases.__eo_typeof.case_146 x_a0, EoCases.__eo_typeof.case_147 x_a0, EoCases.__eo_typeof.case_148 x_a0, EoCases.__eo_typeof.case_149 x_a0, EoCases.__eo_typeof.case_150 x_a0, EoCases.__eo_typeof.case_151 x_a0] ++ [EoCases.__eo_typeof.case_152 x_a0, EoCases.__eo_typeof.case_153 x_a0, EoCases.__eo_typeof.case_154 x_a0, EoCases.__eo_typeof.case_155 x_a0] ++ [EoCases.__eo_typeof.case_156 x_a0, EoCases.__eo_typeof.case_157 x_a0, EoCases.__eo_typeof.case_158 x_a0, EoCases.__eo_typeof.case_159 x_a0] from rfl)
    otherwise ⟨hl_152, hl_153, hl_154, hl_155⟩ using hn_a0 hl_144 hl_145 hl_146 hl_147 hl_148 hl_149 hl_150 hl_151
  group_step with cases_0_39_eo__24eo_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_144 x_a0, EoCases.__eo_typeof.case_145 x_a0, EoCases.__eo_typeof.case_146 x_a0, EoCases.__eo_typeof.case_147 x_a0, EoCases.__eo_typeof.case_148 x_a0, EoCases.__eo_typeof.case_149 x_a0, EoCases.__eo_typeof.case_150 x_a0, EoCases.__eo_typeof.case_151 x_a0, EoCases.__eo_typeof.case_152 x_a0, EoCases.__eo_typeof.case_153 x_a0, EoCases.__eo_typeof.case_154 x_a0, EoCases.__eo_typeof.case_155 x_a0, EoCases.__eo_typeof.case_156 x_a0, EoCases.__eo_typeof.case_157 x_a0, EoCases.__eo_typeof.case_158 x_a0, EoCases.__eo_typeof.case_159 x_a0] = [EoCases.__eo_typeof.case_144 x_a0, EoCases.__eo_typeof.case_145 x_a0, EoCases.__eo_typeof.case_146 x_a0, EoCases.__eo_typeof.case_147 x_a0, EoCases.__eo_typeof.case_148 x_a0, EoCases.__eo_typeof.case_149 x_a0, EoCases.__eo_typeof.case_150 x_a0, EoCases.__eo_typeof.case_151 x_a0, EoCases.__eo_typeof.case_152 x_a0, EoCases.__eo_typeof.case_153 x_a0, EoCases.__eo_typeof.case_154 x_a0, EoCases.__eo_typeof.case_155 x_a0] ++ [EoCases.__eo_typeof.case_156 x_a0, EoCases.__eo_typeof.case_157 x_a0, EoCases.__eo_typeof.case_158 x_a0, EoCases.__eo_typeof.case_159 x_a0] ++ [] from rfl)
    otherwise ⟨hl_156, hl_157, hl_158, hl_159⟩ using hn_a0 hl_144 hl_145 hl_146 hl_147 hl_148 hl_149 hl_150 hl_151 hl_152 hl_153 hl_154 hl_155
  group_none hinv4 hG with ⟨hl_144, hl_145, hl_146, hl_147, hl_148, hl_149, hl_150, hl_151, hl_152, hl_153, hl_154, hl_155, hl_156, hl_157, hl_158, hl_159⟩

theorem cases_1_10_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    cases_1_10_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_typeof.case_160 x_a0, EoCases.__eo_typeof.case_161 x_a0, EoCases.__eo_typeof.case_162 x_a0, EoCases.__eo_typeof.case_163 x_a0, EoCases.__eo_typeof.case_164 x_a0, EoCases.__eo_typeof.case_165 x_a0, EoCases.__eo_typeof.case_166 x_a0, EoCases.__eo_typeof.case_167 x_a0, EoCases.__eo_typeof.case_168 x_a0, EoCases.__eo_typeof.case_169 x_a0, EoCases.__eo_typeof.case_170 x_a0, EoCases.__eo_typeof.case_171 x_a0, EoCases.__eo_typeof.case_172 x_a0, EoCases.__eo_typeof.case_173 x_a0, EoCases.__eo_typeof.case_174 x_a0, EoCases.__eo_typeof.case_175 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_160 x_a0 = none ∧ EoCases.__eo_typeof.case_161 x_a0 = none ∧ EoCases.__eo_typeof.case_162 x_a0 = none ∧ EoCases.__eo_typeof.case_163 x_a0 = none ∧ EoCases.__eo_typeof.case_164 x_a0 = none ∧ EoCases.__eo_typeof.case_165 x_a0 = none ∧ EoCases.__eo_typeof.case_166 x_a0 = none ∧ EoCases.__eo_typeof.case_167 x_a0 = none ∧ EoCases.__eo_typeof.case_168 x_a0 = none ∧ EoCases.__eo_typeof.case_169 x_a0 = none ∧ EoCases.__eo_typeof.case_170 x_a0 = none ∧ EoCases.__eo_typeof.case_171 x_a0 = none ∧ EoCases.__eo_typeof.case_172 x_a0 = none ∧ EoCases.__eo_typeof.case_173 x_a0 = none ∧ EoCases.__eo_typeof.case_174 x_a0 = none ∧ EoCases.__eo_typeof.case_175 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_1_10_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  group_step with cases_0_40_eo__24eo_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_160 x_a0, EoCases.__eo_typeof.case_161 x_a0, EoCases.__eo_typeof.case_162 x_a0, EoCases.__eo_typeof.case_163 x_a0, EoCases.__eo_typeof.case_164 x_a0, EoCases.__eo_typeof.case_165 x_a0, EoCases.__eo_typeof.case_166 x_a0, EoCases.__eo_typeof.case_167 x_a0, EoCases.__eo_typeof.case_168 x_a0, EoCases.__eo_typeof.case_169 x_a0, EoCases.__eo_typeof.case_170 x_a0, EoCases.__eo_typeof.case_171 x_a0, EoCases.__eo_typeof.case_172 x_a0, EoCases.__eo_typeof.case_173 x_a0, EoCases.__eo_typeof.case_174 x_a0, EoCases.__eo_typeof.case_175 x_a0] = [] ++ [EoCases.__eo_typeof.case_160 x_a0, EoCases.__eo_typeof.case_161 x_a0, EoCases.__eo_typeof.case_162 x_a0, EoCases.__eo_typeof.case_163 x_a0] ++ [EoCases.__eo_typeof.case_164 x_a0, EoCases.__eo_typeof.case_165 x_a0, EoCases.__eo_typeof.case_166 x_a0, EoCases.__eo_typeof.case_167 x_a0, EoCases.__eo_typeof.case_168 x_a0, EoCases.__eo_typeof.case_169 x_a0, EoCases.__eo_typeof.case_170 x_a0, EoCases.__eo_typeof.case_171 x_a0, EoCases.__eo_typeof.case_172 x_a0, EoCases.__eo_typeof.case_173 x_a0, EoCases.__eo_typeof.case_174 x_a0, EoCases.__eo_typeof.case_175 x_a0] from rfl)
    otherwise ⟨hl_160, hl_161, hl_162, hl_163⟩ using hn_a0
  group_step with cases_0_41_eo__24eo_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_160 x_a0, EoCases.__eo_typeof.case_161 x_a0, EoCases.__eo_typeof.case_162 x_a0, EoCases.__eo_typeof.case_163 x_a0, EoCases.__eo_typeof.case_164 x_a0, EoCases.__eo_typeof.case_165 x_a0, EoCases.__eo_typeof.case_166 x_a0, EoCases.__eo_typeof.case_167 x_a0, EoCases.__eo_typeof.case_168 x_a0, EoCases.__eo_typeof.case_169 x_a0, EoCases.__eo_typeof.case_170 x_a0, EoCases.__eo_typeof.case_171 x_a0, EoCases.__eo_typeof.case_172 x_a0, EoCases.__eo_typeof.case_173 x_a0, EoCases.__eo_typeof.case_174 x_a0, EoCases.__eo_typeof.case_175 x_a0] = [EoCases.__eo_typeof.case_160 x_a0, EoCases.__eo_typeof.case_161 x_a0, EoCases.__eo_typeof.case_162 x_a0, EoCases.__eo_typeof.case_163 x_a0] ++ [EoCases.__eo_typeof.case_164 x_a0, EoCases.__eo_typeof.case_165 x_a0, EoCases.__eo_typeof.case_166 x_a0, EoCases.__eo_typeof.case_167 x_a0] ++ [EoCases.__eo_typeof.case_168 x_a0, EoCases.__eo_typeof.case_169 x_a0, EoCases.__eo_typeof.case_170 x_a0, EoCases.__eo_typeof.case_171 x_a0, EoCases.__eo_typeof.case_172 x_a0, EoCases.__eo_typeof.case_173 x_a0, EoCases.__eo_typeof.case_174 x_a0, EoCases.__eo_typeof.case_175 x_a0] from rfl)
    otherwise ⟨hl_164, hl_165, hl_166, hl_167⟩ using hn_a0 hl_160 hl_161 hl_162 hl_163
  group_step with cases_0_42_eo__24eo_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_160 x_a0, EoCases.__eo_typeof.case_161 x_a0, EoCases.__eo_typeof.case_162 x_a0, EoCases.__eo_typeof.case_163 x_a0, EoCases.__eo_typeof.case_164 x_a0, EoCases.__eo_typeof.case_165 x_a0, EoCases.__eo_typeof.case_166 x_a0, EoCases.__eo_typeof.case_167 x_a0, EoCases.__eo_typeof.case_168 x_a0, EoCases.__eo_typeof.case_169 x_a0, EoCases.__eo_typeof.case_170 x_a0, EoCases.__eo_typeof.case_171 x_a0, EoCases.__eo_typeof.case_172 x_a0, EoCases.__eo_typeof.case_173 x_a0, EoCases.__eo_typeof.case_174 x_a0, EoCases.__eo_typeof.case_175 x_a0] = [EoCases.__eo_typeof.case_160 x_a0, EoCases.__eo_typeof.case_161 x_a0, EoCases.__eo_typeof.case_162 x_a0, EoCases.__eo_typeof.case_163 x_a0, EoCases.__eo_typeof.case_164 x_a0, EoCases.__eo_typeof.case_165 x_a0, EoCases.__eo_typeof.case_166 x_a0, EoCases.__eo_typeof.case_167 x_a0] ++ [EoCases.__eo_typeof.case_168 x_a0, EoCases.__eo_typeof.case_169 x_a0, EoCases.__eo_typeof.case_170 x_a0, EoCases.__eo_typeof.case_171 x_a0] ++ [EoCases.__eo_typeof.case_172 x_a0, EoCases.__eo_typeof.case_173 x_a0, EoCases.__eo_typeof.case_174 x_a0, EoCases.__eo_typeof.case_175 x_a0] from rfl)
    otherwise ⟨hl_168, hl_169, hl_170, hl_171⟩ using hn_a0 hl_160 hl_161 hl_162 hl_163 hl_164 hl_165 hl_166 hl_167
  group_step with cases_0_43_eo__24eo_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_160 x_a0, EoCases.__eo_typeof.case_161 x_a0, EoCases.__eo_typeof.case_162 x_a0, EoCases.__eo_typeof.case_163 x_a0, EoCases.__eo_typeof.case_164 x_a0, EoCases.__eo_typeof.case_165 x_a0, EoCases.__eo_typeof.case_166 x_a0, EoCases.__eo_typeof.case_167 x_a0, EoCases.__eo_typeof.case_168 x_a0, EoCases.__eo_typeof.case_169 x_a0, EoCases.__eo_typeof.case_170 x_a0, EoCases.__eo_typeof.case_171 x_a0, EoCases.__eo_typeof.case_172 x_a0, EoCases.__eo_typeof.case_173 x_a0, EoCases.__eo_typeof.case_174 x_a0, EoCases.__eo_typeof.case_175 x_a0] = [EoCases.__eo_typeof.case_160 x_a0, EoCases.__eo_typeof.case_161 x_a0, EoCases.__eo_typeof.case_162 x_a0, EoCases.__eo_typeof.case_163 x_a0, EoCases.__eo_typeof.case_164 x_a0, EoCases.__eo_typeof.case_165 x_a0, EoCases.__eo_typeof.case_166 x_a0, EoCases.__eo_typeof.case_167 x_a0, EoCases.__eo_typeof.case_168 x_a0, EoCases.__eo_typeof.case_169 x_a0, EoCases.__eo_typeof.case_170 x_a0, EoCases.__eo_typeof.case_171 x_a0] ++ [EoCases.__eo_typeof.case_172 x_a0, EoCases.__eo_typeof.case_173 x_a0, EoCases.__eo_typeof.case_174 x_a0, EoCases.__eo_typeof.case_175 x_a0] ++ [] from rfl)
    otherwise ⟨hl_172, hl_173, hl_174, hl_175⟩ using hn_a0 hl_160 hl_161 hl_162 hl_163 hl_164 hl_165 hl_166 hl_167 hl_168 hl_169 hl_170 hl_171
  group_none hinv4 hG with ⟨hl_160, hl_161, hl_162, hl_163, hl_164, hl_165, hl_166, hl_167, hl_168, hl_169, hl_170, hl_171, hl_172, hl_173, hl_174, hl_175⟩

theorem cases_1_11_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    cases_1_11_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_typeof.case_176 x_a0, EoCases.__eo_typeof.case_177 x_a0, EoCases.__eo_typeof.case_178 x_a0, EoCases.__eo_typeof.case_179 x_a0, EoCases.__eo_typeof.case_180 x_a0, EoCases.__eo_typeof.case_181 x_a0, EoCases.__eo_typeof.case_182 x_a0, EoCases.__eo_typeof.case_183 x_a0, EoCases.__eo_typeof.case_184 x_a0, EoCases.__eo_typeof.case_185 x_a0, EoCases.__eo_typeof.case_186 x_a0, EoCases.__eo_typeof.case_187 x_a0, EoCases.__eo_typeof.case_188 x_a0, EoCases.__eo_typeof.case_189 x_a0, EoCases.__eo_typeof.case_190 x_a0, EoCases.__eo_typeof.case_191 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_176 x_a0 = none ∧ EoCases.__eo_typeof.case_177 x_a0 = none ∧ EoCases.__eo_typeof.case_178 x_a0 = none ∧ EoCases.__eo_typeof.case_179 x_a0 = none ∧ EoCases.__eo_typeof.case_180 x_a0 = none ∧ EoCases.__eo_typeof.case_181 x_a0 = none ∧ EoCases.__eo_typeof.case_182 x_a0 = none ∧ EoCases.__eo_typeof.case_183 x_a0 = none ∧ EoCases.__eo_typeof.case_184 x_a0 = none ∧ EoCases.__eo_typeof.case_185 x_a0 = none ∧ EoCases.__eo_typeof.case_186 x_a0 = none ∧ EoCases.__eo_typeof.case_187 x_a0 = none ∧ EoCases.__eo_typeof.case_188 x_a0 = none ∧ EoCases.__eo_typeof.case_189 x_a0 = none ∧ EoCases.__eo_typeof.case_190 x_a0 = none ∧ EoCases.__eo_typeof.case_191 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_1_11_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  group_step with cases_0_44_eo__24eo_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_176 x_a0, EoCases.__eo_typeof.case_177 x_a0, EoCases.__eo_typeof.case_178 x_a0, EoCases.__eo_typeof.case_179 x_a0, EoCases.__eo_typeof.case_180 x_a0, EoCases.__eo_typeof.case_181 x_a0, EoCases.__eo_typeof.case_182 x_a0, EoCases.__eo_typeof.case_183 x_a0, EoCases.__eo_typeof.case_184 x_a0, EoCases.__eo_typeof.case_185 x_a0, EoCases.__eo_typeof.case_186 x_a0, EoCases.__eo_typeof.case_187 x_a0, EoCases.__eo_typeof.case_188 x_a0, EoCases.__eo_typeof.case_189 x_a0, EoCases.__eo_typeof.case_190 x_a0, EoCases.__eo_typeof.case_191 x_a0] = [] ++ [EoCases.__eo_typeof.case_176 x_a0, EoCases.__eo_typeof.case_177 x_a0, EoCases.__eo_typeof.case_178 x_a0, EoCases.__eo_typeof.case_179 x_a0] ++ [EoCases.__eo_typeof.case_180 x_a0, EoCases.__eo_typeof.case_181 x_a0, EoCases.__eo_typeof.case_182 x_a0, EoCases.__eo_typeof.case_183 x_a0, EoCases.__eo_typeof.case_184 x_a0, EoCases.__eo_typeof.case_185 x_a0, EoCases.__eo_typeof.case_186 x_a0, EoCases.__eo_typeof.case_187 x_a0, EoCases.__eo_typeof.case_188 x_a0, EoCases.__eo_typeof.case_189 x_a0, EoCases.__eo_typeof.case_190 x_a0, EoCases.__eo_typeof.case_191 x_a0] from rfl)
    otherwise ⟨hl_176, hl_177, hl_178, hl_179⟩ using hn_a0
  group_step with cases_0_45_eo__24eo_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_176 x_a0, EoCases.__eo_typeof.case_177 x_a0, EoCases.__eo_typeof.case_178 x_a0, EoCases.__eo_typeof.case_179 x_a0, EoCases.__eo_typeof.case_180 x_a0, EoCases.__eo_typeof.case_181 x_a0, EoCases.__eo_typeof.case_182 x_a0, EoCases.__eo_typeof.case_183 x_a0, EoCases.__eo_typeof.case_184 x_a0, EoCases.__eo_typeof.case_185 x_a0, EoCases.__eo_typeof.case_186 x_a0, EoCases.__eo_typeof.case_187 x_a0, EoCases.__eo_typeof.case_188 x_a0, EoCases.__eo_typeof.case_189 x_a0, EoCases.__eo_typeof.case_190 x_a0, EoCases.__eo_typeof.case_191 x_a0] = [EoCases.__eo_typeof.case_176 x_a0, EoCases.__eo_typeof.case_177 x_a0, EoCases.__eo_typeof.case_178 x_a0, EoCases.__eo_typeof.case_179 x_a0] ++ [EoCases.__eo_typeof.case_180 x_a0, EoCases.__eo_typeof.case_181 x_a0, EoCases.__eo_typeof.case_182 x_a0, EoCases.__eo_typeof.case_183 x_a0] ++ [EoCases.__eo_typeof.case_184 x_a0, EoCases.__eo_typeof.case_185 x_a0, EoCases.__eo_typeof.case_186 x_a0, EoCases.__eo_typeof.case_187 x_a0, EoCases.__eo_typeof.case_188 x_a0, EoCases.__eo_typeof.case_189 x_a0, EoCases.__eo_typeof.case_190 x_a0, EoCases.__eo_typeof.case_191 x_a0] from rfl)
    otherwise ⟨hl_180, hl_181, hl_182, hl_183⟩ using hn_a0 hl_176 hl_177 hl_178 hl_179
  group_step with cases_0_46_eo__24eo_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_176 x_a0, EoCases.__eo_typeof.case_177 x_a0, EoCases.__eo_typeof.case_178 x_a0, EoCases.__eo_typeof.case_179 x_a0, EoCases.__eo_typeof.case_180 x_a0, EoCases.__eo_typeof.case_181 x_a0, EoCases.__eo_typeof.case_182 x_a0, EoCases.__eo_typeof.case_183 x_a0, EoCases.__eo_typeof.case_184 x_a0, EoCases.__eo_typeof.case_185 x_a0, EoCases.__eo_typeof.case_186 x_a0, EoCases.__eo_typeof.case_187 x_a0, EoCases.__eo_typeof.case_188 x_a0, EoCases.__eo_typeof.case_189 x_a0, EoCases.__eo_typeof.case_190 x_a0, EoCases.__eo_typeof.case_191 x_a0] = [EoCases.__eo_typeof.case_176 x_a0, EoCases.__eo_typeof.case_177 x_a0, EoCases.__eo_typeof.case_178 x_a0, EoCases.__eo_typeof.case_179 x_a0, EoCases.__eo_typeof.case_180 x_a0, EoCases.__eo_typeof.case_181 x_a0, EoCases.__eo_typeof.case_182 x_a0, EoCases.__eo_typeof.case_183 x_a0] ++ [EoCases.__eo_typeof.case_184 x_a0, EoCases.__eo_typeof.case_185 x_a0, EoCases.__eo_typeof.case_186 x_a0, EoCases.__eo_typeof.case_187 x_a0] ++ [EoCases.__eo_typeof.case_188 x_a0, EoCases.__eo_typeof.case_189 x_a0, EoCases.__eo_typeof.case_190 x_a0, EoCases.__eo_typeof.case_191 x_a0] from rfl)
    otherwise ⟨hl_184, hl_185, hl_186, hl_187⟩ using hn_a0 hl_176 hl_177 hl_178 hl_179 hl_180 hl_181 hl_182 hl_183
  group_step with cases_0_47_eo__24eo_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_176 x_a0, EoCases.__eo_typeof.case_177 x_a0, EoCases.__eo_typeof.case_178 x_a0, EoCases.__eo_typeof.case_179 x_a0, EoCases.__eo_typeof.case_180 x_a0, EoCases.__eo_typeof.case_181 x_a0, EoCases.__eo_typeof.case_182 x_a0, EoCases.__eo_typeof.case_183 x_a0, EoCases.__eo_typeof.case_184 x_a0, EoCases.__eo_typeof.case_185 x_a0, EoCases.__eo_typeof.case_186 x_a0, EoCases.__eo_typeof.case_187 x_a0, EoCases.__eo_typeof.case_188 x_a0, EoCases.__eo_typeof.case_189 x_a0, EoCases.__eo_typeof.case_190 x_a0, EoCases.__eo_typeof.case_191 x_a0] = [EoCases.__eo_typeof.case_176 x_a0, EoCases.__eo_typeof.case_177 x_a0, EoCases.__eo_typeof.case_178 x_a0, EoCases.__eo_typeof.case_179 x_a0, EoCases.__eo_typeof.case_180 x_a0, EoCases.__eo_typeof.case_181 x_a0, EoCases.__eo_typeof.case_182 x_a0, EoCases.__eo_typeof.case_183 x_a0, EoCases.__eo_typeof.case_184 x_a0, EoCases.__eo_typeof.case_185 x_a0, EoCases.__eo_typeof.case_186 x_a0, EoCases.__eo_typeof.case_187 x_a0] ++ [EoCases.__eo_typeof.case_188 x_a0, EoCases.__eo_typeof.case_189 x_a0, EoCases.__eo_typeof.case_190 x_a0, EoCases.__eo_typeof.case_191 x_a0] ++ [] from rfl)
    otherwise ⟨hl_188, hl_189, hl_190, hl_191⟩ using hn_a0 hl_176 hl_177 hl_178 hl_179 hl_180 hl_181 hl_182 hl_183 hl_184 hl_185 hl_186 hl_187
  group_none hinv4 hG with ⟨hl_176, hl_177, hl_178, hl_179, hl_180, hl_181, hl_182, hl_183, hl_184, hl_185, hl_186, hl_187, hl_188, hl_189, hl_190, hl_191⟩

theorem cases_1_12_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    cases_1_12_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_typeof.case_192 x_a0, EoCases.__eo_typeof.case_193 x_a0, EoCases.__eo_typeof.case_194 x_a0, EoCases.__eo_typeof.case_195 x_a0, EoCases.__eo_typeof.case_196 x_a0, EoCases.__eo_typeof.case_197 x_a0, EoCases.__eo_typeof.case_198 x_a0, EoCases.__eo_typeof.case_199 x_a0, EoCases.__eo_typeof.case_200 x_a0, EoCases.__eo_typeof.case_201 x_a0, EoCases.__eo_typeof.case_202 x_a0, EoCases.__eo_typeof.case_203 x_a0, EoCases.__eo_typeof.case_204 x_a0, EoCases.__eo_typeof.case_205 x_a0, EoCases.__eo_typeof.case_206 x_a0, EoCases.__eo_typeof.case_207 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_192 x_a0 = none ∧ EoCases.__eo_typeof.case_193 x_a0 = none ∧ EoCases.__eo_typeof.case_194 x_a0 = none ∧ EoCases.__eo_typeof.case_195 x_a0 = none ∧ EoCases.__eo_typeof.case_196 x_a0 = none ∧ EoCases.__eo_typeof.case_197 x_a0 = none ∧ EoCases.__eo_typeof.case_198 x_a0 = none ∧ EoCases.__eo_typeof.case_199 x_a0 = none ∧ EoCases.__eo_typeof.case_200 x_a0 = none ∧ EoCases.__eo_typeof.case_201 x_a0 = none ∧ EoCases.__eo_typeof.case_202 x_a0 = none ∧ EoCases.__eo_typeof.case_203 x_a0 = none ∧ EoCases.__eo_typeof.case_204 x_a0 = none ∧ EoCases.__eo_typeof.case_205 x_a0 = none ∧ EoCases.__eo_typeof.case_206 x_a0 = none ∧ EoCases.__eo_typeof.case_207 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_1_12_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  group_step with cases_0_48_eo__24eo_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_192 x_a0, EoCases.__eo_typeof.case_193 x_a0, EoCases.__eo_typeof.case_194 x_a0, EoCases.__eo_typeof.case_195 x_a0, EoCases.__eo_typeof.case_196 x_a0, EoCases.__eo_typeof.case_197 x_a0, EoCases.__eo_typeof.case_198 x_a0, EoCases.__eo_typeof.case_199 x_a0, EoCases.__eo_typeof.case_200 x_a0, EoCases.__eo_typeof.case_201 x_a0, EoCases.__eo_typeof.case_202 x_a0, EoCases.__eo_typeof.case_203 x_a0, EoCases.__eo_typeof.case_204 x_a0, EoCases.__eo_typeof.case_205 x_a0, EoCases.__eo_typeof.case_206 x_a0, EoCases.__eo_typeof.case_207 x_a0] = [] ++ [EoCases.__eo_typeof.case_192 x_a0, EoCases.__eo_typeof.case_193 x_a0, EoCases.__eo_typeof.case_194 x_a0, EoCases.__eo_typeof.case_195 x_a0] ++ [EoCases.__eo_typeof.case_196 x_a0, EoCases.__eo_typeof.case_197 x_a0, EoCases.__eo_typeof.case_198 x_a0, EoCases.__eo_typeof.case_199 x_a0, EoCases.__eo_typeof.case_200 x_a0, EoCases.__eo_typeof.case_201 x_a0, EoCases.__eo_typeof.case_202 x_a0, EoCases.__eo_typeof.case_203 x_a0, EoCases.__eo_typeof.case_204 x_a0, EoCases.__eo_typeof.case_205 x_a0, EoCases.__eo_typeof.case_206 x_a0, EoCases.__eo_typeof.case_207 x_a0] from rfl)
    otherwise ⟨hl_192, hl_193, hl_194, hl_195⟩ using hn_a0
  group_step with cases_0_49_eo__24eo_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_192 x_a0, EoCases.__eo_typeof.case_193 x_a0, EoCases.__eo_typeof.case_194 x_a0, EoCases.__eo_typeof.case_195 x_a0, EoCases.__eo_typeof.case_196 x_a0, EoCases.__eo_typeof.case_197 x_a0, EoCases.__eo_typeof.case_198 x_a0, EoCases.__eo_typeof.case_199 x_a0, EoCases.__eo_typeof.case_200 x_a0, EoCases.__eo_typeof.case_201 x_a0, EoCases.__eo_typeof.case_202 x_a0, EoCases.__eo_typeof.case_203 x_a0, EoCases.__eo_typeof.case_204 x_a0, EoCases.__eo_typeof.case_205 x_a0, EoCases.__eo_typeof.case_206 x_a0, EoCases.__eo_typeof.case_207 x_a0] = [EoCases.__eo_typeof.case_192 x_a0, EoCases.__eo_typeof.case_193 x_a0, EoCases.__eo_typeof.case_194 x_a0, EoCases.__eo_typeof.case_195 x_a0] ++ [EoCases.__eo_typeof.case_196 x_a0, EoCases.__eo_typeof.case_197 x_a0, EoCases.__eo_typeof.case_198 x_a0, EoCases.__eo_typeof.case_199 x_a0] ++ [EoCases.__eo_typeof.case_200 x_a0, EoCases.__eo_typeof.case_201 x_a0, EoCases.__eo_typeof.case_202 x_a0, EoCases.__eo_typeof.case_203 x_a0, EoCases.__eo_typeof.case_204 x_a0, EoCases.__eo_typeof.case_205 x_a0, EoCases.__eo_typeof.case_206 x_a0, EoCases.__eo_typeof.case_207 x_a0] from rfl)
    otherwise ⟨hl_196, hl_197, hl_198, hl_199⟩ using hn_a0 hl_192 hl_193 hl_194 hl_195
  group_step with cases_0_50_eo__24eo_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_192 x_a0, EoCases.__eo_typeof.case_193 x_a0, EoCases.__eo_typeof.case_194 x_a0, EoCases.__eo_typeof.case_195 x_a0, EoCases.__eo_typeof.case_196 x_a0, EoCases.__eo_typeof.case_197 x_a0, EoCases.__eo_typeof.case_198 x_a0, EoCases.__eo_typeof.case_199 x_a0, EoCases.__eo_typeof.case_200 x_a0, EoCases.__eo_typeof.case_201 x_a0, EoCases.__eo_typeof.case_202 x_a0, EoCases.__eo_typeof.case_203 x_a0, EoCases.__eo_typeof.case_204 x_a0, EoCases.__eo_typeof.case_205 x_a0, EoCases.__eo_typeof.case_206 x_a0, EoCases.__eo_typeof.case_207 x_a0] = [EoCases.__eo_typeof.case_192 x_a0, EoCases.__eo_typeof.case_193 x_a0, EoCases.__eo_typeof.case_194 x_a0, EoCases.__eo_typeof.case_195 x_a0, EoCases.__eo_typeof.case_196 x_a0, EoCases.__eo_typeof.case_197 x_a0, EoCases.__eo_typeof.case_198 x_a0, EoCases.__eo_typeof.case_199 x_a0] ++ [EoCases.__eo_typeof.case_200 x_a0, EoCases.__eo_typeof.case_201 x_a0, EoCases.__eo_typeof.case_202 x_a0, EoCases.__eo_typeof.case_203 x_a0] ++ [EoCases.__eo_typeof.case_204 x_a0, EoCases.__eo_typeof.case_205 x_a0, EoCases.__eo_typeof.case_206 x_a0, EoCases.__eo_typeof.case_207 x_a0] from rfl)
    otherwise ⟨hl_200, hl_201, hl_202, hl_203⟩ using hn_a0 hl_192 hl_193 hl_194 hl_195 hl_196 hl_197 hl_198 hl_199
  group_step with cases_0_51_eo__24eo_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_192 x_a0, EoCases.__eo_typeof.case_193 x_a0, EoCases.__eo_typeof.case_194 x_a0, EoCases.__eo_typeof.case_195 x_a0, EoCases.__eo_typeof.case_196 x_a0, EoCases.__eo_typeof.case_197 x_a0, EoCases.__eo_typeof.case_198 x_a0, EoCases.__eo_typeof.case_199 x_a0, EoCases.__eo_typeof.case_200 x_a0, EoCases.__eo_typeof.case_201 x_a0, EoCases.__eo_typeof.case_202 x_a0, EoCases.__eo_typeof.case_203 x_a0, EoCases.__eo_typeof.case_204 x_a0, EoCases.__eo_typeof.case_205 x_a0, EoCases.__eo_typeof.case_206 x_a0, EoCases.__eo_typeof.case_207 x_a0] = [EoCases.__eo_typeof.case_192 x_a0, EoCases.__eo_typeof.case_193 x_a0, EoCases.__eo_typeof.case_194 x_a0, EoCases.__eo_typeof.case_195 x_a0, EoCases.__eo_typeof.case_196 x_a0, EoCases.__eo_typeof.case_197 x_a0, EoCases.__eo_typeof.case_198 x_a0, EoCases.__eo_typeof.case_199 x_a0, EoCases.__eo_typeof.case_200 x_a0, EoCases.__eo_typeof.case_201 x_a0, EoCases.__eo_typeof.case_202 x_a0, EoCases.__eo_typeof.case_203 x_a0] ++ [EoCases.__eo_typeof.case_204 x_a0, EoCases.__eo_typeof.case_205 x_a0, EoCases.__eo_typeof.case_206 x_a0, EoCases.__eo_typeof.case_207 x_a0] ++ [] from rfl)
    otherwise ⟨hl_204, hl_205, hl_206, hl_207⟩ using hn_a0 hl_192 hl_193 hl_194 hl_195 hl_196 hl_197 hl_198 hl_199 hl_200 hl_201 hl_202 hl_203
  group_none hinv4 hG with ⟨hl_192, hl_193, hl_194, hl_195, hl_196, hl_197, hl_198, hl_199, hl_200, hl_201, hl_202, hl_203, hl_204, hl_205, hl_206, hl_207⟩

theorem cases_2_0_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    cases_2_0_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_typeof.case_0 x_a0, EoCases.__eo_typeof.case_1 x_a0, EoCases.__eo_typeof.case_2 x_a0, EoCases.__eo_typeof.case_3 x_a0, EoCases.__eo_typeof.case_4 x_a0, EoCases.__eo_typeof.case_5 x_a0, EoCases.__eo_typeof.case_6 x_a0, EoCases.__eo_typeof.case_7 x_a0, EoCases.__eo_typeof.case_8 x_a0, EoCases.__eo_typeof.case_9 x_a0, EoCases.__eo_typeof.case_10 x_a0, EoCases.__eo_typeof.case_11 x_a0, EoCases.__eo_typeof.case_12 x_a0, EoCases.__eo_typeof.case_13 x_a0, EoCases.__eo_typeof.case_14 x_a0, EoCases.__eo_typeof.case_15 x_a0, EoCases.__eo_typeof.case_16 x_a0, EoCases.__eo_typeof.case_17 x_a0, EoCases.__eo_typeof.case_18 x_a0, EoCases.__eo_typeof.case_19 x_a0, EoCases.__eo_typeof.case_20 x_a0, EoCases.__eo_typeof.case_21 x_a0, EoCases.__eo_typeof.case_22 x_a0, EoCases.__eo_typeof.case_23 x_a0, EoCases.__eo_typeof.case_24 x_a0, EoCases.__eo_typeof.case_25 x_a0, EoCases.__eo_typeof.case_26 x_a0, EoCases.__eo_typeof.case_27 x_a0, EoCases.__eo_typeof.case_28 x_a0, EoCases.__eo_typeof.case_29 x_a0, EoCases.__eo_typeof.case_30 x_a0, EoCases.__eo_typeof.case_31 x_a0, EoCases.__eo_typeof.case_32 x_a0, EoCases.__eo_typeof.case_33 x_a0, EoCases.__eo_typeof.case_34 x_a0, EoCases.__eo_typeof.case_35 x_a0, EoCases.__eo_typeof.case_36 x_a0, EoCases.__eo_typeof.case_37 x_a0, EoCases.__eo_typeof.case_38 x_a0, EoCases.__eo_typeof.case_39 x_a0, EoCases.__eo_typeof.case_40 x_a0, EoCases.__eo_typeof.case_41 x_a0, EoCases.__eo_typeof.case_42 x_a0, EoCases.__eo_typeof.case_43 x_a0, EoCases.__eo_typeof.case_44 x_a0, EoCases.__eo_typeof.case_45 x_a0, EoCases.__eo_typeof.case_46 x_a0, EoCases.__eo_typeof.case_47 x_a0, EoCases.__eo_typeof.case_48 x_a0, EoCases.__eo_typeof.case_49 x_a0, EoCases.__eo_typeof.case_50 x_a0, EoCases.__eo_typeof.case_51 x_a0, EoCases.__eo_typeof.case_52 x_a0, EoCases.__eo_typeof.case_53 x_a0, EoCases.__eo_typeof.case_54 x_a0, EoCases.__eo_typeof.case_55 x_a0, EoCases.__eo_typeof.case_56 x_a0, EoCases.__eo_typeof.case_57 x_a0, EoCases.__eo_typeof.case_58 x_a0, EoCases.__eo_typeof.case_59 x_a0, EoCases.__eo_typeof.case_60 x_a0, EoCases.__eo_typeof.case_61 x_a0, EoCases.__eo_typeof.case_62 x_a0, EoCases.__eo_typeof.case_63 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_0 x_a0 = none ∧ EoCases.__eo_typeof.case_1 x_a0 = none ∧ EoCases.__eo_typeof.case_2 x_a0 = none ∧ EoCases.__eo_typeof.case_3 x_a0 = none ∧ EoCases.__eo_typeof.case_4 x_a0 = none ∧ EoCases.__eo_typeof.case_5 x_a0 = none ∧ EoCases.__eo_typeof.case_6 x_a0 = none ∧ EoCases.__eo_typeof.case_7 x_a0 = none ∧ EoCases.__eo_typeof.case_8 x_a0 = none ∧ EoCases.__eo_typeof.case_9 x_a0 = none ∧ EoCases.__eo_typeof.case_10 x_a0 = none ∧ EoCases.__eo_typeof.case_11 x_a0 = none ∧ EoCases.__eo_typeof.case_12 x_a0 = none ∧ EoCases.__eo_typeof.case_13 x_a0 = none ∧ EoCases.__eo_typeof.case_14 x_a0 = none ∧ EoCases.__eo_typeof.case_15 x_a0 = none ∧ EoCases.__eo_typeof.case_16 x_a0 = none ∧ EoCases.__eo_typeof.case_17 x_a0 = none ∧ EoCases.__eo_typeof.case_18 x_a0 = none ∧ EoCases.__eo_typeof.case_19 x_a0 = none ∧ EoCases.__eo_typeof.case_20 x_a0 = none ∧ EoCases.__eo_typeof.case_21 x_a0 = none ∧ EoCases.__eo_typeof.case_22 x_a0 = none ∧ EoCases.__eo_typeof.case_23 x_a0 = none ∧ EoCases.__eo_typeof.case_24 x_a0 = none ∧ EoCases.__eo_typeof.case_25 x_a0 = none ∧ EoCases.__eo_typeof.case_26 x_a0 = none ∧ EoCases.__eo_typeof.case_27 x_a0 = none ∧ EoCases.__eo_typeof.case_28 x_a0 = none ∧ EoCases.__eo_typeof.case_29 x_a0 = none ∧ EoCases.__eo_typeof.case_30 x_a0 = none ∧ EoCases.__eo_typeof.case_31 x_a0 = none ∧ EoCases.__eo_typeof.case_32 x_a0 = none ∧ EoCases.__eo_typeof.case_33 x_a0 = none ∧ EoCases.__eo_typeof.case_34 x_a0 = none ∧ EoCases.__eo_typeof.case_35 x_a0 = none ∧ EoCases.__eo_typeof.case_36 x_a0 = none ∧ EoCases.__eo_typeof.case_37 x_a0 = none ∧ EoCases.__eo_typeof.case_38 x_a0 = none ∧ EoCases.__eo_typeof.case_39 x_a0 = none ∧ EoCases.__eo_typeof.case_40 x_a0 = none ∧ EoCases.__eo_typeof.case_41 x_a0 = none ∧ EoCases.__eo_typeof.case_42 x_a0 = none ∧ EoCases.__eo_typeof.case_43 x_a0 = none ∧ EoCases.__eo_typeof.case_44 x_a0 = none ∧ EoCases.__eo_typeof.case_45 x_a0 = none ∧ EoCases.__eo_typeof.case_46 x_a0 = none ∧ EoCases.__eo_typeof.case_47 x_a0 = none ∧ EoCases.__eo_typeof.case_48 x_a0 = none ∧ EoCases.__eo_typeof.case_49 x_a0 = none ∧ EoCases.__eo_typeof.case_50 x_a0 = none ∧ EoCases.__eo_typeof.case_51 x_a0 = none ∧ EoCases.__eo_typeof.case_52 x_a0 = none ∧ EoCases.__eo_typeof.case_53 x_a0 = none ∧ EoCases.__eo_typeof.case_54 x_a0 = none ∧ EoCases.__eo_typeof.case_55 x_a0 = none ∧ EoCases.__eo_typeof.case_56 x_a0 = none ∧ EoCases.__eo_typeof.case_57 x_a0 = none ∧ EoCases.__eo_typeof.case_58 x_a0 = none ∧ EoCases.__eo_typeof.case_59 x_a0 = none ∧ EoCases.__eo_typeof.case_60 x_a0 = none ∧ EoCases.__eo_typeof.case_61 x_a0 = none ∧ EoCases.__eo_typeof.case_62 x_a0 = none ∧ EoCases.__eo_typeof.case_63 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_2_0_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  group_step with cases_1_0_eo__24eo_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_0 x_a0, EoCases.__eo_typeof.case_1 x_a0, EoCases.__eo_typeof.case_2 x_a0, EoCases.__eo_typeof.case_3 x_a0, EoCases.__eo_typeof.case_4 x_a0, EoCases.__eo_typeof.case_5 x_a0, EoCases.__eo_typeof.case_6 x_a0, EoCases.__eo_typeof.case_7 x_a0, EoCases.__eo_typeof.case_8 x_a0, EoCases.__eo_typeof.case_9 x_a0, EoCases.__eo_typeof.case_10 x_a0, EoCases.__eo_typeof.case_11 x_a0, EoCases.__eo_typeof.case_12 x_a0, EoCases.__eo_typeof.case_13 x_a0, EoCases.__eo_typeof.case_14 x_a0, EoCases.__eo_typeof.case_15 x_a0, EoCases.__eo_typeof.case_16 x_a0, EoCases.__eo_typeof.case_17 x_a0, EoCases.__eo_typeof.case_18 x_a0, EoCases.__eo_typeof.case_19 x_a0, EoCases.__eo_typeof.case_20 x_a0, EoCases.__eo_typeof.case_21 x_a0, EoCases.__eo_typeof.case_22 x_a0, EoCases.__eo_typeof.case_23 x_a0, EoCases.__eo_typeof.case_24 x_a0, EoCases.__eo_typeof.case_25 x_a0, EoCases.__eo_typeof.case_26 x_a0, EoCases.__eo_typeof.case_27 x_a0, EoCases.__eo_typeof.case_28 x_a0, EoCases.__eo_typeof.case_29 x_a0, EoCases.__eo_typeof.case_30 x_a0, EoCases.__eo_typeof.case_31 x_a0, EoCases.__eo_typeof.case_32 x_a0, EoCases.__eo_typeof.case_33 x_a0, EoCases.__eo_typeof.case_34 x_a0, EoCases.__eo_typeof.case_35 x_a0, EoCases.__eo_typeof.case_36 x_a0, EoCases.__eo_typeof.case_37 x_a0, EoCases.__eo_typeof.case_38 x_a0, EoCases.__eo_typeof.case_39 x_a0, EoCases.__eo_typeof.case_40 x_a0, EoCases.__eo_typeof.case_41 x_a0, EoCases.__eo_typeof.case_42 x_a0, EoCases.__eo_typeof.case_43 x_a0, EoCases.__eo_typeof.case_44 x_a0, EoCases.__eo_typeof.case_45 x_a0, EoCases.__eo_typeof.case_46 x_a0, EoCases.__eo_typeof.case_47 x_a0, EoCases.__eo_typeof.case_48 x_a0, EoCases.__eo_typeof.case_49 x_a0, EoCases.__eo_typeof.case_50 x_a0, EoCases.__eo_typeof.case_51 x_a0, EoCases.__eo_typeof.case_52 x_a0, EoCases.__eo_typeof.case_53 x_a0, EoCases.__eo_typeof.case_54 x_a0, EoCases.__eo_typeof.case_55 x_a0, EoCases.__eo_typeof.case_56 x_a0, EoCases.__eo_typeof.case_57 x_a0, EoCases.__eo_typeof.case_58 x_a0, EoCases.__eo_typeof.case_59 x_a0, EoCases.__eo_typeof.case_60 x_a0, EoCases.__eo_typeof.case_61 x_a0, EoCases.__eo_typeof.case_62 x_a0, EoCases.__eo_typeof.case_63 x_a0] = [] ++ [EoCases.__eo_typeof.case_0 x_a0, EoCases.__eo_typeof.case_1 x_a0, EoCases.__eo_typeof.case_2 x_a0, EoCases.__eo_typeof.case_3 x_a0, EoCases.__eo_typeof.case_4 x_a0, EoCases.__eo_typeof.case_5 x_a0, EoCases.__eo_typeof.case_6 x_a0, EoCases.__eo_typeof.case_7 x_a0, EoCases.__eo_typeof.case_8 x_a0, EoCases.__eo_typeof.case_9 x_a0, EoCases.__eo_typeof.case_10 x_a0, EoCases.__eo_typeof.case_11 x_a0, EoCases.__eo_typeof.case_12 x_a0, EoCases.__eo_typeof.case_13 x_a0, EoCases.__eo_typeof.case_14 x_a0, EoCases.__eo_typeof.case_15 x_a0] ++ [EoCases.__eo_typeof.case_16 x_a0, EoCases.__eo_typeof.case_17 x_a0, EoCases.__eo_typeof.case_18 x_a0, EoCases.__eo_typeof.case_19 x_a0, EoCases.__eo_typeof.case_20 x_a0, EoCases.__eo_typeof.case_21 x_a0, EoCases.__eo_typeof.case_22 x_a0, EoCases.__eo_typeof.case_23 x_a0, EoCases.__eo_typeof.case_24 x_a0, EoCases.__eo_typeof.case_25 x_a0, EoCases.__eo_typeof.case_26 x_a0, EoCases.__eo_typeof.case_27 x_a0, EoCases.__eo_typeof.case_28 x_a0, EoCases.__eo_typeof.case_29 x_a0, EoCases.__eo_typeof.case_30 x_a0, EoCases.__eo_typeof.case_31 x_a0, EoCases.__eo_typeof.case_32 x_a0, EoCases.__eo_typeof.case_33 x_a0, EoCases.__eo_typeof.case_34 x_a0, EoCases.__eo_typeof.case_35 x_a0, EoCases.__eo_typeof.case_36 x_a0, EoCases.__eo_typeof.case_37 x_a0, EoCases.__eo_typeof.case_38 x_a0, EoCases.__eo_typeof.case_39 x_a0, EoCases.__eo_typeof.case_40 x_a0, EoCases.__eo_typeof.case_41 x_a0, EoCases.__eo_typeof.case_42 x_a0, EoCases.__eo_typeof.case_43 x_a0, EoCases.__eo_typeof.case_44 x_a0, EoCases.__eo_typeof.case_45 x_a0, EoCases.__eo_typeof.case_46 x_a0, EoCases.__eo_typeof.case_47 x_a0, EoCases.__eo_typeof.case_48 x_a0, EoCases.__eo_typeof.case_49 x_a0, EoCases.__eo_typeof.case_50 x_a0, EoCases.__eo_typeof.case_51 x_a0, EoCases.__eo_typeof.case_52 x_a0, EoCases.__eo_typeof.case_53 x_a0, EoCases.__eo_typeof.case_54 x_a0, EoCases.__eo_typeof.case_55 x_a0, EoCases.__eo_typeof.case_56 x_a0, EoCases.__eo_typeof.case_57 x_a0, EoCases.__eo_typeof.case_58 x_a0, EoCases.__eo_typeof.case_59 x_a0, EoCases.__eo_typeof.case_60 x_a0, EoCases.__eo_typeof.case_61 x_a0, EoCases.__eo_typeof.case_62 x_a0, EoCases.__eo_typeof.case_63 x_a0] from rfl)
    otherwise ⟨hl_0, hl_1, hl_2, hl_3, hl_4, hl_5, hl_6, hl_7, hl_8, hl_9, hl_10, hl_11, hl_12, hl_13, hl_14, hl_15⟩ using hn_a0
  group_step with cases_1_1_eo__24eo_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_0 x_a0, EoCases.__eo_typeof.case_1 x_a0, EoCases.__eo_typeof.case_2 x_a0, EoCases.__eo_typeof.case_3 x_a0, EoCases.__eo_typeof.case_4 x_a0, EoCases.__eo_typeof.case_5 x_a0, EoCases.__eo_typeof.case_6 x_a0, EoCases.__eo_typeof.case_7 x_a0, EoCases.__eo_typeof.case_8 x_a0, EoCases.__eo_typeof.case_9 x_a0, EoCases.__eo_typeof.case_10 x_a0, EoCases.__eo_typeof.case_11 x_a0, EoCases.__eo_typeof.case_12 x_a0, EoCases.__eo_typeof.case_13 x_a0, EoCases.__eo_typeof.case_14 x_a0, EoCases.__eo_typeof.case_15 x_a0, EoCases.__eo_typeof.case_16 x_a0, EoCases.__eo_typeof.case_17 x_a0, EoCases.__eo_typeof.case_18 x_a0, EoCases.__eo_typeof.case_19 x_a0, EoCases.__eo_typeof.case_20 x_a0, EoCases.__eo_typeof.case_21 x_a0, EoCases.__eo_typeof.case_22 x_a0, EoCases.__eo_typeof.case_23 x_a0, EoCases.__eo_typeof.case_24 x_a0, EoCases.__eo_typeof.case_25 x_a0, EoCases.__eo_typeof.case_26 x_a0, EoCases.__eo_typeof.case_27 x_a0, EoCases.__eo_typeof.case_28 x_a0, EoCases.__eo_typeof.case_29 x_a0, EoCases.__eo_typeof.case_30 x_a0, EoCases.__eo_typeof.case_31 x_a0, EoCases.__eo_typeof.case_32 x_a0, EoCases.__eo_typeof.case_33 x_a0, EoCases.__eo_typeof.case_34 x_a0, EoCases.__eo_typeof.case_35 x_a0, EoCases.__eo_typeof.case_36 x_a0, EoCases.__eo_typeof.case_37 x_a0, EoCases.__eo_typeof.case_38 x_a0, EoCases.__eo_typeof.case_39 x_a0, EoCases.__eo_typeof.case_40 x_a0, EoCases.__eo_typeof.case_41 x_a0, EoCases.__eo_typeof.case_42 x_a0, EoCases.__eo_typeof.case_43 x_a0, EoCases.__eo_typeof.case_44 x_a0, EoCases.__eo_typeof.case_45 x_a0, EoCases.__eo_typeof.case_46 x_a0, EoCases.__eo_typeof.case_47 x_a0, EoCases.__eo_typeof.case_48 x_a0, EoCases.__eo_typeof.case_49 x_a0, EoCases.__eo_typeof.case_50 x_a0, EoCases.__eo_typeof.case_51 x_a0, EoCases.__eo_typeof.case_52 x_a0, EoCases.__eo_typeof.case_53 x_a0, EoCases.__eo_typeof.case_54 x_a0, EoCases.__eo_typeof.case_55 x_a0, EoCases.__eo_typeof.case_56 x_a0, EoCases.__eo_typeof.case_57 x_a0, EoCases.__eo_typeof.case_58 x_a0, EoCases.__eo_typeof.case_59 x_a0, EoCases.__eo_typeof.case_60 x_a0, EoCases.__eo_typeof.case_61 x_a0, EoCases.__eo_typeof.case_62 x_a0, EoCases.__eo_typeof.case_63 x_a0] = [EoCases.__eo_typeof.case_0 x_a0, EoCases.__eo_typeof.case_1 x_a0, EoCases.__eo_typeof.case_2 x_a0, EoCases.__eo_typeof.case_3 x_a0, EoCases.__eo_typeof.case_4 x_a0, EoCases.__eo_typeof.case_5 x_a0, EoCases.__eo_typeof.case_6 x_a0, EoCases.__eo_typeof.case_7 x_a0, EoCases.__eo_typeof.case_8 x_a0, EoCases.__eo_typeof.case_9 x_a0, EoCases.__eo_typeof.case_10 x_a0, EoCases.__eo_typeof.case_11 x_a0, EoCases.__eo_typeof.case_12 x_a0, EoCases.__eo_typeof.case_13 x_a0, EoCases.__eo_typeof.case_14 x_a0, EoCases.__eo_typeof.case_15 x_a0] ++ [EoCases.__eo_typeof.case_16 x_a0, EoCases.__eo_typeof.case_17 x_a0, EoCases.__eo_typeof.case_18 x_a0, EoCases.__eo_typeof.case_19 x_a0, EoCases.__eo_typeof.case_20 x_a0, EoCases.__eo_typeof.case_21 x_a0, EoCases.__eo_typeof.case_22 x_a0, EoCases.__eo_typeof.case_23 x_a0, EoCases.__eo_typeof.case_24 x_a0, EoCases.__eo_typeof.case_25 x_a0, EoCases.__eo_typeof.case_26 x_a0, EoCases.__eo_typeof.case_27 x_a0, EoCases.__eo_typeof.case_28 x_a0, EoCases.__eo_typeof.case_29 x_a0, EoCases.__eo_typeof.case_30 x_a0, EoCases.__eo_typeof.case_31 x_a0] ++ [EoCases.__eo_typeof.case_32 x_a0, EoCases.__eo_typeof.case_33 x_a0, EoCases.__eo_typeof.case_34 x_a0, EoCases.__eo_typeof.case_35 x_a0, EoCases.__eo_typeof.case_36 x_a0, EoCases.__eo_typeof.case_37 x_a0, EoCases.__eo_typeof.case_38 x_a0, EoCases.__eo_typeof.case_39 x_a0, EoCases.__eo_typeof.case_40 x_a0, EoCases.__eo_typeof.case_41 x_a0, EoCases.__eo_typeof.case_42 x_a0, EoCases.__eo_typeof.case_43 x_a0, EoCases.__eo_typeof.case_44 x_a0, EoCases.__eo_typeof.case_45 x_a0, EoCases.__eo_typeof.case_46 x_a0, EoCases.__eo_typeof.case_47 x_a0, EoCases.__eo_typeof.case_48 x_a0, EoCases.__eo_typeof.case_49 x_a0, EoCases.__eo_typeof.case_50 x_a0, EoCases.__eo_typeof.case_51 x_a0, EoCases.__eo_typeof.case_52 x_a0, EoCases.__eo_typeof.case_53 x_a0, EoCases.__eo_typeof.case_54 x_a0, EoCases.__eo_typeof.case_55 x_a0, EoCases.__eo_typeof.case_56 x_a0, EoCases.__eo_typeof.case_57 x_a0, EoCases.__eo_typeof.case_58 x_a0, EoCases.__eo_typeof.case_59 x_a0, EoCases.__eo_typeof.case_60 x_a0, EoCases.__eo_typeof.case_61 x_a0, EoCases.__eo_typeof.case_62 x_a0, EoCases.__eo_typeof.case_63 x_a0] from rfl)
    otherwise ⟨hl_16, hl_17, hl_18, hl_19, hl_20, hl_21, hl_22, hl_23, hl_24, hl_25, hl_26, hl_27, hl_28, hl_29, hl_30, hl_31⟩ using hn_a0 hl_0 hl_1 hl_2 hl_3 hl_4 hl_5 hl_6 hl_7 hl_8 hl_9 hl_10 hl_11 hl_12 hl_13 hl_14 hl_15
  group_step with cases_1_2_eo__24eo_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_0 x_a0, EoCases.__eo_typeof.case_1 x_a0, EoCases.__eo_typeof.case_2 x_a0, EoCases.__eo_typeof.case_3 x_a0, EoCases.__eo_typeof.case_4 x_a0, EoCases.__eo_typeof.case_5 x_a0, EoCases.__eo_typeof.case_6 x_a0, EoCases.__eo_typeof.case_7 x_a0, EoCases.__eo_typeof.case_8 x_a0, EoCases.__eo_typeof.case_9 x_a0, EoCases.__eo_typeof.case_10 x_a0, EoCases.__eo_typeof.case_11 x_a0, EoCases.__eo_typeof.case_12 x_a0, EoCases.__eo_typeof.case_13 x_a0, EoCases.__eo_typeof.case_14 x_a0, EoCases.__eo_typeof.case_15 x_a0, EoCases.__eo_typeof.case_16 x_a0, EoCases.__eo_typeof.case_17 x_a0, EoCases.__eo_typeof.case_18 x_a0, EoCases.__eo_typeof.case_19 x_a0, EoCases.__eo_typeof.case_20 x_a0, EoCases.__eo_typeof.case_21 x_a0, EoCases.__eo_typeof.case_22 x_a0, EoCases.__eo_typeof.case_23 x_a0, EoCases.__eo_typeof.case_24 x_a0, EoCases.__eo_typeof.case_25 x_a0, EoCases.__eo_typeof.case_26 x_a0, EoCases.__eo_typeof.case_27 x_a0, EoCases.__eo_typeof.case_28 x_a0, EoCases.__eo_typeof.case_29 x_a0, EoCases.__eo_typeof.case_30 x_a0, EoCases.__eo_typeof.case_31 x_a0, EoCases.__eo_typeof.case_32 x_a0, EoCases.__eo_typeof.case_33 x_a0, EoCases.__eo_typeof.case_34 x_a0, EoCases.__eo_typeof.case_35 x_a0, EoCases.__eo_typeof.case_36 x_a0, EoCases.__eo_typeof.case_37 x_a0, EoCases.__eo_typeof.case_38 x_a0, EoCases.__eo_typeof.case_39 x_a0, EoCases.__eo_typeof.case_40 x_a0, EoCases.__eo_typeof.case_41 x_a0, EoCases.__eo_typeof.case_42 x_a0, EoCases.__eo_typeof.case_43 x_a0, EoCases.__eo_typeof.case_44 x_a0, EoCases.__eo_typeof.case_45 x_a0, EoCases.__eo_typeof.case_46 x_a0, EoCases.__eo_typeof.case_47 x_a0, EoCases.__eo_typeof.case_48 x_a0, EoCases.__eo_typeof.case_49 x_a0, EoCases.__eo_typeof.case_50 x_a0, EoCases.__eo_typeof.case_51 x_a0, EoCases.__eo_typeof.case_52 x_a0, EoCases.__eo_typeof.case_53 x_a0, EoCases.__eo_typeof.case_54 x_a0, EoCases.__eo_typeof.case_55 x_a0, EoCases.__eo_typeof.case_56 x_a0, EoCases.__eo_typeof.case_57 x_a0, EoCases.__eo_typeof.case_58 x_a0, EoCases.__eo_typeof.case_59 x_a0, EoCases.__eo_typeof.case_60 x_a0, EoCases.__eo_typeof.case_61 x_a0, EoCases.__eo_typeof.case_62 x_a0, EoCases.__eo_typeof.case_63 x_a0] = [EoCases.__eo_typeof.case_0 x_a0, EoCases.__eo_typeof.case_1 x_a0, EoCases.__eo_typeof.case_2 x_a0, EoCases.__eo_typeof.case_3 x_a0, EoCases.__eo_typeof.case_4 x_a0, EoCases.__eo_typeof.case_5 x_a0, EoCases.__eo_typeof.case_6 x_a0, EoCases.__eo_typeof.case_7 x_a0, EoCases.__eo_typeof.case_8 x_a0, EoCases.__eo_typeof.case_9 x_a0, EoCases.__eo_typeof.case_10 x_a0, EoCases.__eo_typeof.case_11 x_a0, EoCases.__eo_typeof.case_12 x_a0, EoCases.__eo_typeof.case_13 x_a0, EoCases.__eo_typeof.case_14 x_a0, EoCases.__eo_typeof.case_15 x_a0, EoCases.__eo_typeof.case_16 x_a0, EoCases.__eo_typeof.case_17 x_a0, EoCases.__eo_typeof.case_18 x_a0, EoCases.__eo_typeof.case_19 x_a0, EoCases.__eo_typeof.case_20 x_a0, EoCases.__eo_typeof.case_21 x_a0, EoCases.__eo_typeof.case_22 x_a0, EoCases.__eo_typeof.case_23 x_a0, EoCases.__eo_typeof.case_24 x_a0, EoCases.__eo_typeof.case_25 x_a0, EoCases.__eo_typeof.case_26 x_a0, EoCases.__eo_typeof.case_27 x_a0, EoCases.__eo_typeof.case_28 x_a0, EoCases.__eo_typeof.case_29 x_a0, EoCases.__eo_typeof.case_30 x_a0, EoCases.__eo_typeof.case_31 x_a0] ++ [EoCases.__eo_typeof.case_32 x_a0, EoCases.__eo_typeof.case_33 x_a0, EoCases.__eo_typeof.case_34 x_a0, EoCases.__eo_typeof.case_35 x_a0, EoCases.__eo_typeof.case_36 x_a0, EoCases.__eo_typeof.case_37 x_a0, EoCases.__eo_typeof.case_38 x_a0, EoCases.__eo_typeof.case_39 x_a0, EoCases.__eo_typeof.case_40 x_a0, EoCases.__eo_typeof.case_41 x_a0, EoCases.__eo_typeof.case_42 x_a0, EoCases.__eo_typeof.case_43 x_a0, EoCases.__eo_typeof.case_44 x_a0, EoCases.__eo_typeof.case_45 x_a0, EoCases.__eo_typeof.case_46 x_a0, EoCases.__eo_typeof.case_47 x_a0] ++ [EoCases.__eo_typeof.case_48 x_a0, EoCases.__eo_typeof.case_49 x_a0, EoCases.__eo_typeof.case_50 x_a0, EoCases.__eo_typeof.case_51 x_a0, EoCases.__eo_typeof.case_52 x_a0, EoCases.__eo_typeof.case_53 x_a0, EoCases.__eo_typeof.case_54 x_a0, EoCases.__eo_typeof.case_55 x_a0, EoCases.__eo_typeof.case_56 x_a0, EoCases.__eo_typeof.case_57 x_a0, EoCases.__eo_typeof.case_58 x_a0, EoCases.__eo_typeof.case_59 x_a0, EoCases.__eo_typeof.case_60 x_a0, EoCases.__eo_typeof.case_61 x_a0, EoCases.__eo_typeof.case_62 x_a0, EoCases.__eo_typeof.case_63 x_a0] from rfl)
    otherwise ⟨hl_32, hl_33, hl_34, hl_35, hl_36, hl_37, hl_38, hl_39, hl_40, hl_41, hl_42, hl_43, hl_44, hl_45, hl_46, hl_47⟩ using hn_a0 hl_0 hl_1 hl_2 hl_3 hl_4 hl_5 hl_6 hl_7 hl_8 hl_9 hl_10 hl_11 hl_12 hl_13 hl_14 hl_15 hl_16 hl_17 hl_18 hl_19 hl_20 hl_21 hl_22 hl_23 hl_24 hl_25 hl_26 hl_27 hl_28 hl_29 hl_30 hl_31
  group_step with cases_1_3_eo__24eo_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_0 x_a0, EoCases.__eo_typeof.case_1 x_a0, EoCases.__eo_typeof.case_2 x_a0, EoCases.__eo_typeof.case_3 x_a0, EoCases.__eo_typeof.case_4 x_a0, EoCases.__eo_typeof.case_5 x_a0, EoCases.__eo_typeof.case_6 x_a0, EoCases.__eo_typeof.case_7 x_a0, EoCases.__eo_typeof.case_8 x_a0, EoCases.__eo_typeof.case_9 x_a0, EoCases.__eo_typeof.case_10 x_a0, EoCases.__eo_typeof.case_11 x_a0, EoCases.__eo_typeof.case_12 x_a0, EoCases.__eo_typeof.case_13 x_a0, EoCases.__eo_typeof.case_14 x_a0, EoCases.__eo_typeof.case_15 x_a0, EoCases.__eo_typeof.case_16 x_a0, EoCases.__eo_typeof.case_17 x_a0, EoCases.__eo_typeof.case_18 x_a0, EoCases.__eo_typeof.case_19 x_a0, EoCases.__eo_typeof.case_20 x_a0, EoCases.__eo_typeof.case_21 x_a0, EoCases.__eo_typeof.case_22 x_a0, EoCases.__eo_typeof.case_23 x_a0, EoCases.__eo_typeof.case_24 x_a0, EoCases.__eo_typeof.case_25 x_a0, EoCases.__eo_typeof.case_26 x_a0, EoCases.__eo_typeof.case_27 x_a0, EoCases.__eo_typeof.case_28 x_a0, EoCases.__eo_typeof.case_29 x_a0, EoCases.__eo_typeof.case_30 x_a0, EoCases.__eo_typeof.case_31 x_a0, EoCases.__eo_typeof.case_32 x_a0, EoCases.__eo_typeof.case_33 x_a0, EoCases.__eo_typeof.case_34 x_a0, EoCases.__eo_typeof.case_35 x_a0, EoCases.__eo_typeof.case_36 x_a0, EoCases.__eo_typeof.case_37 x_a0, EoCases.__eo_typeof.case_38 x_a0, EoCases.__eo_typeof.case_39 x_a0, EoCases.__eo_typeof.case_40 x_a0, EoCases.__eo_typeof.case_41 x_a0, EoCases.__eo_typeof.case_42 x_a0, EoCases.__eo_typeof.case_43 x_a0, EoCases.__eo_typeof.case_44 x_a0, EoCases.__eo_typeof.case_45 x_a0, EoCases.__eo_typeof.case_46 x_a0, EoCases.__eo_typeof.case_47 x_a0, EoCases.__eo_typeof.case_48 x_a0, EoCases.__eo_typeof.case_49 x_a0, EoCases.__eo_typeof.case_50 x_a0, EoCases.__eo_typeof.case_51 x_a0, EoCases.__eo_typeof.case_52 x_a0, EoCases.__eo_typeof.case_53 x_a0, EoCases.__eo_typeof.case_54 x_a0, EoCases.__eo_typeof.case_55 x_a0, EoCases.__eo_typeof.case_56 x_a0, EoCases.__eo_typeof.case_57 x_a0, EoCases.__eo_typeof.case_58 x_a0, EoCases.__eo_typeof.case_59 x_a0, EoCases.__eo_typeof.case_60 x_a0, EoCases.__eo_typeof.case_61 x_a0, EoCases.__eo_typeof.case_62 x_a0, EoCases.__eo_typeof.case_63 x_a0] = [EoCases.__eo_typeof.case_0 x_a0, EoCases.__eo_typeof.case_1 x_a0, EoCases.__eo_typeof.case_2 x_a0, EoCases.__eo_typeof.case_3 x_a0, EoCases.__eo_typeof.case_4 x_a0, EoCases.__eo_typeof.case_5 x_a0, EoCases.__eo_typeof.case_6 x_a0, EoCases.__eo_typeof.case_7 x_a0, EoCases.__eo_typeof.case_8 x_a0, EoCases.__eo_typeof.case_9 x_a0, EoCases.__eo_typeof.case_10 x_a0, EoCases.__eo_typeof.case_11 x_a0, EoCases.__eo_typeof.case_12 x_a0, EoCases.__eo_typeof.case_13 x_a0, EoCases.__eo_typeof.case_14 x_a0, EoCases.__eo_typeof.case_15 x_a0, EoCases.__eo_typeof.case_16 x_a0, EoCases.__eo_typeof.case_17 x_a0, EoCases.__eo_typeof.case_18 x_a0, EoCases.__eo_typeof.case_19 x_a0, EoCases.__eo_typeof.case_20 x_a0, EoCases.__eo_typeof.case_21 x_a0, EoCases.__eo_typeof.case_22 x_a0, EoCases.__eo_typeof.case_23 x_a0, EoCases.__eo_typeof.case_24 x_a0, EoCases.__eo_typeof.case_25 x_a0, EoCases.__eo_typeof.case_26 x_a0, EoCases.__eo_typeof.case_27 x_a0, EoCases.__eo_typeof.case_28 x_a0, EoCases.__eo_typeof.case_29 x_a0, EoCases.__eo_typeof.case_30 x_a0, EoCases.__eo_typeof.case_31 x_a0, EoCases.__eo_typeof.case_32 x_a0, EoCases.__eo_typeof.case_33 x_a0, EoCases.__eo_typeof.case_34 x_a0, EoCases.__eo_typeof.case_35 x_a0, EoCases.__eo_typeof.case_36 x_a0, EoCases.__eo_typeof.case_37 x_a0, EoCases.__eo_typeof.case_38 x_a0, EoCases.__eo_typeof.case_39 x_a0, EoCases.__eo_typeof.case_40 x_a0, EoCases.__eo_typeof.case_41 x_a0, EoCases.__eo_typeof.case_42 x_a0, EoCases.__eo_typeof.case_43 x_a0, EoCases.__eo_typeof.case_44 x_a0, EoCases.__eo_typeof.case_45 x_a0, EoCases.__eo_typeof.case_46 x_a0, EoCases.__eo_typeof.case_47 x_a0] ++ [EoCases.__eo_typeof.case_48 x_a0, EoCases.__eo_typeof.case_49 x_a0, EoCases.__eo_typeof.case_50 x_a0, EoCases.__eo_typeof.case_51 x_a0, EoCases.__eo_typeof.case_52 x_a0, EoCases.__eo_typeof.case_53 x_a0, EoCases.__eo_typeof.case_54 x_a0, EoCases.__eo_typeof.case_55 x_a0, EoCases.__eo_typeof.case_56 x_a0, EoCases.__eo_typeof.case_57 x_a0, EoCases.__eo_typeof.case_58 x_a0, EoCases.__eo_typeof.case_59 x_a0, EoCases.__eo_typeof.case_60 x_a0, EoCases.__eo_typeof.case_61 x_a0, EoCases.__eo_typeof.case_62 x_a0, EoCases.__eo_typeof.case_63 x_a0] ++ [] from rfl)
    otherwise ⟨hl_48, hl_49, hl_50, hl_51, hl_52, hl_53, hl_54, hl_55, hl_56, hl_57, hl_58, hl_59, hl_60, hl_61, hl_62, hl_63⟩ using hn_a0 hl_0 hl_1 hl_2 hl_3 hl_4 hl_5 hl_6 hl_7 hl_8 hl_9 hl_10 hl_11 hl_12 hl_13 hl_14 hl_15 hl_16 hl_17 hl_18 hl_19 hl_20 hl_21 hl_22 hl_23 hl_24 hl_25 hl_26 hl_27 hl_28 hl_29 hl_30 hl_31 hl_32 hl_33 hl_34 hl_35 hl_36 hl_37 hl_38 hl_39 hl_40 hl_41 hl_42 hl_43 hl_44 hl_45 hl_46 hl_47
  group_none hinv4 hG with ⟨hl_0, hl_1, hl_2, hl_3, hl_4, hl_5, hl_6, hl_7, hl_8, hl_9, hl_10, hl_11, hl_12, hl_13, hl_14, hl_15, hl_16, hl_17, hl_18, hl_19, hl_20, hl_21, hl_22, hl_23, hl_24, hl_25, hl_26, hl_27, hl_28, hl_29, hl_30, hl_31, hl_32, hl_33, hl_34, hl_35, hl_36, hl_37, hl_38, hl_39, hl_40, hl_41, hl_42, hl_43, hl_44, hl_45, hl_46, hl_47, hl_48, hl_49, hl_50, hl_51, hl_52, hl_53, hl_54, hl_55, hl_56, hl_57, hl_58, hl_59, hl_60, hl_61, hl_62, hl_63⟩

theorem cases_2_1_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    cases_2_1_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_typeof.case_64 x_a0, EoCases.__eo_typeof.case_65 x_a0, EoCases.__eo_typeof.case_66 x_a0, EoCases.__eo_typeof.case_67 x_a0, EoCases.__eo_typeof.case_68 x_a0, EoCases.__eo_typeof.case_69 x_a0, EoCases.__eo_typeof.case_70 x_a0, EoCases.__eo_typeof.case_71 x_a0, EoCases.__eo_typeof.case_72 x_a0, EoCases.__eo_typeof.case_73 x_a0, EoCases.__eo_typeof.case_74 x_a0, EoCases.__eo_typeof.case_75 x_a0, EoCases.__eo_typeof.case_76 x_a0, EoCases.__eo_typeof.case_77 x_a0, EoCases.__eo_typeof.case_78 x_a0, EoCases.__eo_typeof.case_79 x_a0, EoCases.__eo_typeof.case_80 x_a0, EoCases.__eo_typeof.case_81 x_a0, EoCases.__eo_typeof.case_82 x_a0, EoCases.__eo_typeof.case_83 x_a0, EoCases.__eo_typeof.case_84 x_a0, EoCases.__eo_typeof.case_85 x_a0, EoCases.__eo_typeof.case_86 x_a0, EoCases.__eo_typeof.case_87 x_a0, EoCases.__eo_typeof.case_88 x_a0, EoCases.__eo_typeof.case_89 x_a0, EoCases.__eo_typeof.case_90 x_a0, EoCases.__eo_typeof.case_91 x_a0, EoCases.__eo_typeof.case_92 x_a0, EoCases.__eo_typeof.case_93 x_a0, EoCases.__eo_typeof.case_94 x_a0, EoCases.__eo_typeof.case_95 x_a0, EoCases.__eo_typeof.case_96 x_a0, EoCases.__eo_typeof.case_97 x_a0, EoCases.__eo_typeof.case_98 x_a0, EoCases.__eo_typeof.case_99 x_a0, EoCases.__eo_typeof.case_100 x_a0, EoCases.__eo_typeof.case_101 x_a0, EoCases.__eo_typeof.case_102 x_a0, EoCases.__eo_typeof.case_103 x_a0, EoCases.__eo_typeof.case_104 x_a0, EoCases.__eo_typeof.case_105 x_a0, EoCases.__eo_typeof.case_106 x_a0, EoCases.__eo_typeof.case_107 x_a0, EoCases.__eo_typeof.case_108 x_a0, EoCases.__eo_typeof.case_109 x_a0, EoCases.__eo_typeof.case_110 x_a0, EoCases.__eo_typeof.case_111 x_a0, EoCases.__eo_typeof.case_112 x_a0, EoCases.__eo_typeof.case_113 x_a0, EoCases.__eo_typeof.case_114 x_a0, EoCases.__eo_typeof.case_115 x_a0, EoCases.__eo_typeof.case_116 x_a0, EoCases.__eo_typeof.case_117 x_a0, EoCases.__eo_typeof.case_118 x_a0, EoCases.__eo_typeof.case_119 x_a0, EoCases.__eo_typeof.case_120 x_a0, EoCases.__eo_typeof.case_121 x_a0, EoCases.__eo_typeof.case_122 x_a0, EoCases.__eo_typeof.case_123 x_a0, EoCases.__eo_typeof.case_124 x_a0, EoCases.__eo_typeof.case_125 x_a0, EoCases.__eo_typeof.case_126 x_a0, EoCases.__eo_typeof.case_127 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_64 x_a0 = none ∧ EoCases.__eo_typeof.case_65 x_a0 = none ∧ EoCases.__eo_typeof.case_66 x_a0 = none ∧ EoCases.__eo_typeof.case_67 x_a0 = none ∧ EoCases.__eo_typeof.case_68 x_a0 = none ∧ EoCases.__eo_typeof.case_69 x_a0 = none ∧ EoCases.__eo_typeof.case_70 x_a0 = none ∧ EoCases.__eo_typeof.case_71 x_a0 = none ∧ EoCases.__eo_typeof.case_72 x_a0 = none ∧ EoCases.__eo_typeof.case_73 x_a0 = none ∧ EoCases.__eo_typeof.case_74 x_a0 = none ∧ EoCases.__eo_typeof.case_75 x_a0 = none ∧ EoCases.__eo_typeof.case_76 x_a0 = none ∧ EoCases.__eo_typeof.case_77 x_a0 = none ∧ EoCases.__eo_typeof.case_78 x_a0 = none ∧ EoCases.__eo_typeof.case_79 x_a0 = none ∧ EoCases.__eo_typeof.case_80 x_a0 = none ∧ EoCases.__eo_typeof.case_81 x_a0 = none ∧ EoCases.__eo_typeof.case_82 x_a0 = none ∧ EoCases.__eo_typeof.case_83 x_a0 = none ∧ EoCases.__eo_typeof.case_84 x_a0 = none ∧ EoCases.__eo_typeof.case_85 x_a0 = none ∧ EoCases.__eo_typeof.case_86 x_a0 = none ∧ EoCases.__eo_typeof.case_87 x_a0 = none ∧ EoCases.__eo_typeof.case_88 x_a0 = none ∧ EoCases.__eo_typeof.case_89 x_a0 = none ∧ EoCases.__eo_typeof.case_90 x_a0 = none ∧ EoCases.__eo_typeof.case_91 x_a0 = none ∧ EoCases.__eo_typeof.case_92 x_a0 = none ∧ EoCases.__eo_typeof.case_93 x_a0 = none ∧ EoCases.__eo_typeof.case_94 x_a0 = none ∧ EoCases.__eo_typeof.case_95 x_a0 = none ∧ EoCases.__eo_typeof.case_96 x_a0 = none ∧ EoCases.__eo_typeof.case_97 x_a0 = none ∧ EoCases.__eo_typeof.case_98 x_a0 = none ∧ EoCases.__eo_typeof.case_99 x_a0 = none ∧ EoCases.__eo_typeof.case_100 x_a0 = none ∧ EoCases.__eo_typeof.case_101 x_a0 = none ∧ EoCases.__eo_typeof.case_102 x_a0 = none ∧ EoCases.__eo_typeof.case_103 x_a0 = none ∧ EoCases.__eo_typeof.case_104 x_a0 = none ∧ EoCases.__eo_typeof.case_105 x_a0 = none ∧ EoCases.__eo_typeof.case_106 x_a0 = none ∧ EoCases.__eo_typeof.case_107 x_a0 = none ∧ EoCases.__eo_typeof.case_108 x_a0 = none ∧ EoCases.__eo_typeof.case_109 x_a0 = none ∧ EoCases.__eo_typeof.case_110 x_a0 = none ∧ EoCases.__eo_typeof.case_111 x_a0 = none ∧ EoCases.__eo_typeof.case_112 x_a0 = none ∧ EoCases.__eo_typeof.case_113 x_a0 = none ∧ EoCases.__eo_typeof.case_114 x_a0 = none ∧ EoCases.__eo_typeof.case_115 x_a0 = none ∧ EoCases.__eo_typeof.case_116 x_a0 = none ∧ EoCases.__eo_typeof.case_117 x_a0 = none ∧ EoCases.__eo_typeof.case_118 x_a0 = none ∧ EoCases.__eo_typeof.case_119 x_a0 = none ∧ EoCases.__eo_typeof.case_120 x_a0 = none ∧ EoCases.__eo_typeof.case_121 x_a0 = none ∧ EoCases.__eo_typeof.case_122 x_a0 = none ∧ EoCases.__eo_typeof.case_123 x_a0 = none ∧ EoCases.__eo_typeof.case_124 x_a0 = none ∧ EoCases.__eo_typeof.case_125 x_a0 = none ∧ EoCases.__eo_typeof.case_126 x_a0 = none ∧ EoCases.__eo_typeof.case_127 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_2_1_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  group_step with cases_1_4_eo__24eo_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_64 x_a0, EoCases.__eo_typeof.case_65 x_a0, EoCases.__eo_typeof.case_66 x_a0, EoCases.__eo_typeof.case_67 x_a0, EoCases.__eo_typeof.case_68 x_a0, EoCases.__eo_typeof.case_69 x_a0, EoCases.__eo_typeof.case_70 x_a0, EoCases.__eo_typeof.case_71 x_a0, EoCases.__eo_typeof.case_72 x_a0, EoCases.__eo_typeof.case_73 x_a0, EoCases.__eo_typeof.case_74 x_a0, EoCases.__eo_typeof.case_75 x_a0, EoCases.__eo_typeof.case_76 x_a0, EoCases.__eo_typeof.case_77 x_a0, EoCases.__eo_typeof.case_78 x_a0, EoCases.__eo_typeof.case_79 x_a0, EoCases.__eo_typeof.case_80 x_a0, EoCases.__eo_typeof.case_81 x_a0, EoCases.__eo_typeof.case_82 x_a0, EoCases.__eo_typeof.case_83 x_a0, EoCases.__eo_typeof.case_84 x_a0, EoCases.__eo_typeof.case_85 x_a0, EoCases.__eo_typeof.case_86 x_a0, EoCases.__eo_typeof.case_87 x_a0, EoCases.__eo_typeof.case_88 x_a0, EoCases.__eo_typeof.case_89 x_a0, EoCases.__eo_typeof.case_90 x_a0, EoCases.__eo_typeof.case_91 x_a0, EoCases.__eo_typeof.case_92 x_a0, EoCases.__eo_typeof.case_93 x_a0, EoCases.__eo_typeof.case_94 x_a0, EoCases.__eo_typeof.case_95 x_a0, EoCases.__eo_typeof.case_96 x_a0, EoCases.__eo_typeof.case_97 x_a0, EoCases.__eo_typeof.case_98 x_a0, EoCases.__eo_typeof.case_99 x_a0, EoCases.__eo_typeof.case_100 x_a0, EoCases.__eo_typeof.case_101 x_a0, EoCases.__eo_typeof.case_102 x_a0, EoCases.__eo_typeof.case_103 x_a0, EoCases.__eo_typeof.case_104 x_a0, EoCases.__eo_typeof.case_105 x_a0, EoCases.__eo_typeof.case_106 x_a0, EoCases.__eo_typeof.case_107 x_a0, EoCases.__eo_typeof.case_108 x_a0, EoCases.__eo_typeof.case_109 x_a0, EoCases.__eo_typeof.case_110 x_a0, EoCases.__eo_typeof.case_111 x_a0, EoCases.__eo_typeof.case_112 x_a0, EoCases.__eo_typeof.case_113 x_a0, EoCases.__eo_typeof.case_114 x_a0, EoCases.__eo_typeof.case_115 x_a0, EoCases.__eo_typeof.case_116 x_a0, EoCases.__eo_typeof.case_117 x_a0, EoCases.__eo_typeof.case_118 x_a0, EoCases.__eo_typeof.case_119 x_a0, EoCases.__eo_typeof.case_120 x_a0, EoCases.__eo_typeof.case_121 x_a0, EoCases.__eo_typeof.case_122 x_a0, EoCases.__eo_typeof.case_123 x_a0, EoCases.__eo_typeof.case_124 x_a0, EoCases.__eo_typeof.case_125 x_a0, EoCases.__eo_typeof.case_126 x_a0, EoCases.__eo_typeof.case_127 x_a0] = [] ++ [EoCases.__eo_typeof.case_64 x_a0, EoCases.__eo_typeof.case_65 x_a0, EoCases.__eo_typeof.case_66 x_a0, EoCases.__eo_typeof.case_67 x_a0, EoCases.__eo_typeof.case_68 x_a0, EoCases.__eo_typeof.case_69 x_a0, EoCases.__eo_typeof.case_70 x_a0, EoCases.__eo_typeof.case_71 x_a0, EoCases.__eo_typeof.case_72 x_a0, EoCases.__eo_typeof.case_73 x_a0, EoCases.__eo_typeof.case_74 x_a0, EoCases.__eo_typeof.case_75 x_a0, EoCases.__eo_typeof.case_76 x_a0, EoCases.__eo_typeof.case_77 x_a0, EoCases.__eo_typeof.case_78 x_a0, EoCases.__eo_typeof.case_79 x_a0] ++ [EoCases.__eo_typeof.case_80 x_a0, EoCases.__eo_typeof.case_81 x_a0, EoCases.__eo_typeof.case_82 x_a0, EoCases.__eo_typeof.case_83 x_a0, EoCases.__eo_typeof.case_84 x_a0, EoCases.__eo_typeof.case_85 x_a0, EoCases.__eo_typeof.case_86 x_a0, EoCases.__eo_typeof.case_87 x_a0, EoCases.__eo_typeof.case_88 x_a0, EoCases.__eo_typeof.case_89 x_a0, EoCases.__eo_typeof.case_90 x_a0, EoCases.__eo_typeof.case_91 x_a0, EoCases.__eo_typeof.case_92 x_a0, EoCases.__eo_typeof.case_93 x_a0, EoCases.__eo_typeof.case_94 x_a0, EoCases.__eo_typeof.case_95 x_a0, EoCases.__eo_typeof.case_96 x_a0, EoCases.__eo_typeof.case_97 x_a0, EoCases.__eo_typeof.case_98 x_a0, EoCases.__eo_typeof.case_99 x_a0, EoCases.__eo_typeof.case_100 x_a0, EoCases.__eo_typeof.case_101 x_a0, EoCases.__eo_typeof.case_102 x_a0, EoCases.__eo_typeof.case_103 x_a0, EoCases.__eo_typeof.case_104 x_a0, EoCases.__eo_typeof.case_105 x_a0, EoCases.__eo_typeof.case_106 x_a0, EoCases.__eo_typeof.case_107 x_a0, EoCases.__eo_typeof.case_108 x_a0, EoCases.__eo_typeof.case_109 x_a0, EoCases.__eo_typeof.case_110 x_a0, EoCases.__eo_typeof.case_111 x_a0, EoCases.__eo_typeof.case_112 x_a0, EoCases.__eo_typeof.case_113 x_a0, EoCases.__eo_typeof.case_114 x_a0, EoCases.__eo_typeof.case_115 x_a0, EoCases.__eo_typeof.case_116 x_a0, EoCases.__eo_typeof.case_117 x_a0, EoCases.__eo_typeof.case_118 x_a0, EoCases.__eo_typeof.case_119 x_a0, EoCases.__eo_typeof.case_120 x_a0, EoCases.__eo_typeof.case_121 x_a0, EoCases.__eo_typeof.case_122 x_a0, EoCases.__eo_typeof.case_123 x_a0, EoCases.__eo_typeof.case_124 x_a0, EoCases.__eo_typeof.case_125 x_a0, EoCases.__eo_typeof.case_126 x_a0, EoCases.__eo_typeof.case_127 x_a0] from rfl)
    otherwise ⟨hl_64, hl_65, hl_66, hl_67, hl_68, hl_69, hl_70, hl_71, hl_72, hl_73, hl_74, hl_75, hl_76, hl_77, hl_78, hl_79⟩ using hn_a0
  group_step with cases_1_5_eo__24eo_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_64 x_a0, EoCases.__eo_typeof.case_65 x_a0, EoCases.__eo_typeof.case_66 x_a0, EoCases.__eo_typeof.case_67 x_a0, EoCases.__eo_typeof.case_68 x_a0, EoCases.__eo_typeof.case_69 x_a0, EoCases.__eo_typeof.case_70 x_a0, EoCases.__eo_typeof.case_71 x_a0, EoCases.__eo_typeof.case_72 x_a0, EoCases.__eo_typeof.case_73 x_a0, EoCases.__eo_typeof.case_74 x_a0, EoCases.__eo_typeof.case_75 x_a0, EoCases.__eo_typeof.case_76 x_a0, EoCases.__eo_typeof.case_77 x_a0, EoCases.__eo_typeof.case_78 x_a0, EoCases.__eo_typeof.case_79 x_a0, EoCases.__eo_typeof.case_80 x_a0, EoCases.__eo_typeof.case_81 x_a0, EoCases.__eo_typeof.case_82 x_a0, EoCases.__eo_typeof.case_83 x_a0, EoCases.__eo_typeof.case_84 x_a0, EoCases.__eo_typeof.case_85 x_a0, EoCases.__eo_typeof.case_86 x_a0, EoCases.__eo_typeof.case_87 x_a0, EoCases.__eo_typeof.case_88 x_a0, EoCases.__eo_typeof.case_89 x_a0, EoCases.__eo_typeof.case_90 x_a0, EoCases.__eo_typeof.case_91 x_a0, EoCases.__eo_typeof.case_92 x_a0, EoCases.__eo_typeof.case_93 x_a0, EoCases.__eo_typeof.case_94 x_a0, EoCases.__eo_typeof.case_95 x_a0, EoCases.__eo_typeof.case_96 x_a0, EoCases.__eo_typeof.case_97 x_a0, EoCases.__eo_typeof.case_98 x_a0, EoCases.__eo_typeof.case_99 x_a0, EoCases.__eo_typeof.case_100 x_a0, EoCases.__eo_typeof.case_101 x_a0, EoCases.__eo_typeof.case_102 x_a0, EoCases.__eo_typeof.case_103 x_a0, EoCases.__eo_typeof.case_104 x_a0, EoCases.__eo_typeof.case_105 x_a0, EoCases.__eo_typeof.case_106 x_a0, EoCases.__eo_typeof.case_107 x_a0, EoCases.__eo_typeof.case_108 x_a0, EoCases.__eo_typeof.case_109 x_a0, EoCases.__eo_typeof.case_110 x_a0, EoCases.__eo_typeof.case_111 x_a0, EoCases.__eo_typeof.case_112 x_a0, EoCases.__eo_typeof.case_113 x_a0, EoCases.__eo_typeof.case_114 x_a0, EoCases.__eo_typeof.case_115 x_a0, EoCases.__eo_typeof.case_116 x_a0, EoCases.__eo_typeof.case_117 x_a0, EoCases.__eo_typeof.case_118 x_a0, EoCases.__eo_typeof.case_119 x_a0, EoCases.__eo_typeof.case_120 x_a0, EoCases.__eo_typeof.case_121 x_a0, EoCases.__eo_typeof.case_122 x_a0, EoCases.__eo_typeof.case_123 x_a0, EoCases.__eo_typeof.case_124 x_a0, EoCases.__eo_typeof.case_125 x_a0, EoCases.__eo_typeof.case_126 x_a0, EoCases.__eo_typeof.case_127 x_a0] = [EoCases.__eo_typeof.case_64 x_a0, EoCases.__eo_typeof.case_65 x_a0, EoCases.__eo_typeof.case_66 x_a0, EoCases.__eo_typeof.case_67 x_a0, EoCases.__eo_typeof.case_68 x_a0, EoCases.__eo_typeof.case_69 x_a0, EoCases.__eo_typeof.case_70 x_a0, EoCases.__eo_typeof.case_71 x_a0, EoCases.__eo_typeof.case_72 x_a0, EoCases.__eo_typeof.case_73 x_a0, EoCases.__eo_typeof.case_74 x_a0, EoCases.__eo_typeof.case_75 x_a0, EoCases.__eo_typeof.case_76 x_a0, EoCases.__eo_typeof.case_77 x_a0, EoCases.__eo_typeof.case_78 x_a0, EoCases.__eo_typeof.case_79 x_a0] ++ [EoCases.__eo_typeof.case_80 x_a0, EoCases.__eo_typeof.case_81 x_a0, EoCases.__eo_typeof.case_82 x_a0, EoCases.__eo_typeof.case_83 x_a0, EoCases.__eo_typeof.case_84 x_a0, EoCases.__eo_typeof.case_85 x_a0, EoCases.__eo_typeof.case_86 x_a0, EoCases.__eo_typeof.case_87 x_a0, EoCases.__eo_typeof.case_88 x_a0, EoCases.__eo_typeof.case_89 x_a0, EoCases.__eo_typeof.case_90 x_a0, EoCases.__eo_typeof.case_91 x_a0, EoCases.__eo_typeof.case_92 x_a0, EoCases.__eo_typeof.case_93 x_a0, EoCases.__eo_typeof.case_94 x_a0, EoCases.__eo_typeof.case_95 x_a0] ++ [EoCases.__eo_typeof.case_96 x_a0, EoCases.__eo_typeof.case_97 x_a0, EoCases.__eo_typeof.case_98 x_a0, EoCases.__eo_typeof.case_99 x_a0, EoCases.__eo_typeof.case_100 x_a0, EoCases.__eo_typeof.case_101 x_a0, EoCases.__eo_typeof.case_102 x_a0, EoCases.__eo_typeof.case_103 x_a0, EoCases.__eo_typeof.case_104 x_a0, EoCases.__eo_typeof.case_105 x_a0, EoCases.__eo_typeof.case_106 x_a0, EoCases.__eo_typeof.case_107 x_a0, EoCases.__eo_typeof.case_108 x_a0, EoCases.__eo_typeof.case_109 x_a0, EoCases.__eo_typeof.case_110 x_a0, EoCases.__eo_typeof.case_111 x_a0, EoCases.__eo_typeof.case_112 x_a0, EoCases.__eo_typeof.case_113 x_a0, EoCases.__eo_typeof.case_114 x_a0, EoCases.__eo_typeof.case_115 x_a0, EoCases.__eo_typeof.case_116 x_a0, EoCases.__eo_typeof.case_117 x_a0, EoCases.__eo_typeof.case_118 x_a0, EoCases.__eo_typeof.case_119 x_a0, EoCases.__eo_typeof.case_120 x_a0, EoCases.__eo_typeof.case_121 x_a0, EoCases.__eo_typeof.case_122 x_a0, EoCases.__eo_typeof.case_123 x_a0, EoCases.__eo_typeof.case_124 x_a0, EoCases.__eo_typeof.case_125 x_a0, EoCases.__eo_typeof.case_126 x_a0, EoCases.__eo_typeof.case_127 x_a0] from rfl)
    otherwise ⟨hl_80, hl_81, hl_82, hl_83, hl_84, hl_85, hl_86, hl_87, hl_88, hl_89, hl_90, hl_91, hl_92, hl_93, hl_94, hl_95⟩ using hn_a0 hl_64 hl_65 hl_66 hl_67 hl_68 hl_69 hl_70 hl_71 hl_72 hl_73 hl_74 hl_75 hl_76 hl_77 hl_78 hl_79
  group_step with cases_1_6_eo__24eo_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_64 x_a0, EoCases.__eo_typeof.case_65 x_a0, EoCases.__eo_typeof.case_66 x_a0, EoCases.__eo_typeof.case_67 x_a0, EoCases.__eo_typeof.case_68 x_a0, EoCases.__eo_typeof.case_69 x_a0, EoCases.__eo_typeof.case_70 x_a0, EoCases.__eo_typeof.case_71 x_a0, EoCases.__eo_typeof.case_72 x_a0, EoCases.__eo_typeof.case_73 x_a0, EoCases.__eo_typeof.case_74 x_a0, EoCases.__eo_typeof.case_75 x_a0, EoCases.__eo_typeof.case_76 x_a0, EoCases.__eo_typeof.case_77 x_a0, EoCases.__eo_typeof.case_78 x_a0, EoCases.__eo_typeof.case_79 x_a0, EoCases.__eo_typeof.case_80 x_a0, EoCases.__eo_typeof.case_81 x_a0, EoCases.__eo_typeof.case_82 x_a0, EoCases.__eo_typeof.case_83 x_a0, EoCases.__eo_typeof.case_84 x_a0, EoCases.__eo_typeof.case_85 x_a0, EoCases.__eo_typeof.case_86 x_a0, EoCases.__eo_typeof.case_87 x_a0, EoCases.__eo_typeof.case_88 x_a0, EoCases.__eo_typeof.case_89 x_a0, EoCases.__eo_typeof.case_90 x_a0, EoCases.__eo_typeof.case_91 x_a0, EoCases.__eo_typeof.case_92 x_a0, EoCases.__eo_typeof.case_93 x_a0, EoCases.__eo_typeof.case_94 x_a0, EoCases.__eo_typeof.case_95 x_a0, EoCases.__eo_typeof.case_96 x_a0, EoCases.__eo_typeof.case_97 x_a0, EoCases.__eo_typeof.case_98 x_a0, EoCases.__eo_typeof.case_99 x_a0, EoCases.__eo_typeof.case_100 x_a0, EoCases.__eo_typeof.case_101 x_a0, EoCases.__eo_typeof.case_102 x_a0, EoCases.__eo_typeof.case_103 x_a0, EoCases.__eo_typeof.case_104 x_a0, EoCases.__eo_typeof.case_105 x_a0, EoCases.__eo_typeof.case_106 x_a0, EoCases.__eo_typeof.case_107 x_a0, EoCases.__eo_typeof.case_108 x_a0, EoCases.__eo_typeof.case_109 x_a0, EoCases.__eo_typeof.case_110 x_a0, EoCases.__eo_typeof.case_111 x_a0, EoCases.__eo_typeof.case_112 x_a0, EoCases.__eo_typeof.case_113 x_a0, EoCases.__eo_typeof.case_114 x_a0, EoCases.__eo_typeof.case_115 x_a0, EoCases.__eo_typeof.case_116 x_a0, EoCases.__eo_typeof.case_117 x_a0, EoCases.__eo_typeof.case_118 x_a0, EoCases.__eo_typeof.case_119 x_a0, EoCases.__eo_typeof.case_120 x_a0, EoCases.__eo_typeof.case_121 x_a0, EoCases.__eo_typeof.case_122 x_a0, EoCases.__eo_typeof.case_123 x_a0, EoCases.__eo_typeof.case_124 x_a0, EoCases.__eo_typeof.case_125 x_a0, EoCases.__eo_typeof.case_126 x_a0, EoCases.__eo_typeof.case_127 x_a0] = [EoCases.__eo_typeof.case_64 x_a0, EoCases.__eo_typeof.case_65 x_a0, EoCases.__eo_typeof.case_66 x_a0, EoCases.__eo_typeof.case_67 x_a0, EoCases.__eo_typeof.case_68 x_a0, EoCases.__eo_typeof.case_69 x_a0, EoCases.__eo_typeof.case_70 x_a0, EoCases.__eo_typeof.case_71 x_a0, EoCases.__eo_typeof.case_72 x_a0, EoCases.__eo_typeof.case_73 x_a0, EoCases.__eo_typeof.case_74 x_a0, EoCases.__eo_typeof.case_75 x_a0, EoCases.__eo_typeof.case_76 x_a0, EoCases.__eo_typeof.case_77 x_a0, EoCases.__eo_typeof.case_78 x_a0, EoCases.__eo_typeof.case_79 x_a0, EoCases.__eo_typeof.case_80 x_a0, EoCases.__eo_typeof.case_81 x_a0, EoCases.__eo_typeof.case_82 x_a0, EoCases.__eo_typeof.case_83 x_a0, EoCases.__eo_typeof.case_84 x_a0, EoCases.__eo_typeof.case_85 x_a0, EoCases.__eo_typeof.case_86 x_a0, EoCases.__eo_typeof.case_87 x_a0, EoCases.__eo_typeof.case_88 x_a0, EoCases.__eo_typeof.case_89 x_a0, EoCases.__eo_typeof.case_90 x_a0, EoCases.__eo_typeof.case_91 x_a0, EoCases.__eo_typeof.case_92 x_a0, EoCases.__eo_typeof.case_93 x_a0, EoCases.__eo_typeof.case_94 x_a0, EoCases.__eo_typeof.case_95 x_a0] ++ [EoCases.__eo_typeof.case_96 x_a0, EoCases.__eo_typeof.case_97 x_a0, EoCases.__eo_typeof.case_98 x_a0, EoCases.__eo_typeof.case_99 x_a0, EoCases.__eo_typeof.case_100 x_a0, EoCases.__eo_typeof.case_101 x_a0, EoCases.__eo_typeof.case_102 x_a0, EoCases.__eo_typeof.case_103 x_a0, EoCases.__eo_typeof.case_104 x_a0, EoCases.__eo_typeof.case_105 x_a0, EoCases.__eo_typeof.case_106 x_a0, EoCases.__eo_typeof.case_107 x_a0, EoCases.__eo_typeof.case_108 x_a0, EoCases.__eo_typeof.case_109 x_a0, EoCases.__eo_typeof.case_110 x_a0, EoCases.__eo_typeof.case_111 x_a0] ++ [EoCases.__eo_typeof.case_112 x_a0, EoCases.__eo_typeof.case_113 x_a0, EoCases.__eo_typeof.case_114 x_a0, EoCases.__eo_typeof.case_115 x_a0, EoCases.__eo_typeof.case_116 x_a0, EoCases.__eo_typeof.case_117 x_a0, EoCases.__eo_typeof.case_118 x_a0, EoCases.__eo_typeof.case_119 x_a0, EoCases.__eo_typeof.case_120 x_a0, EoCases.__eo_typeof.case_121 x_a0, EoCases.__eo_typeof.case_122 x_a0, EoCases.__eo_typeof.case_123 x_a0, EoCases.__eo_typeof.case_124 x_a0, EoCases.__eo_typeof.case_125 x_a0, EoCases.__eo_typeof.case_126 x_a0, EoCases.__eo_typeof.case_127 x_a0] from rfl)
    otherwise ⟨hl_96, hl_97, hl_98, hl_99, hl_100, hl_101, hl_102, hl_103, hl_104, hl_105, hl_106, hl_107, hl_108, hl_109, hl_110, hl_111⟩ using hn_a0 hl_64 hl_65 hl_66 hl_67 hl_68 hl_69 hl_70 hl_71 hl_72 hl_73 hl_74 hl_75 hl_76 hl_77 hl_78 hl_79 hl_80 hl_81 hl_82 hl_83 hl_84 hl_85 hl_86 hl_87 hl_88 hl_89 hl_90 hl_91 hl_92 hl_93 hl_94 hl_95
  group_step with cases_1_7_eo__24eo_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_64 x_a0, EoCases.__eo_typeof.case_65 x_a0, EoCases.__eo_typeof.case_66 x_a0, EoCases.__eo_typeof.case_67 x_a0, EoCases.__eo_typeof.case_68 x_a0, EoCases.__eo_typeof.case_69 x_a0, EoCases.__eo_typeof.case_70 x_a0, EoCases.__eo_typeof.case_71 x_a0, EoCases.__eo_typeof.case_72 x_a0, EoCases.__eo_typeof.case_73 x_a0, EoCases.__eo_typeof.case_74 x_a0, EoCases.__eo_typeof.case_75 x_a0, EoCases.__eo_typeof.case_76 x_a0, EoCases.__eo_typeof.case_77 x_a0, EoCases.__eo_typeof.case_78 x_a0, EoCases.__eo_typeof.case_79 x_a0, EoCases.__eo_typeof.case_80 x_a0, EoCases.__eo_typeof.case_81 x_a0, EoCases.__eo_typeof.case_82 x_a0, EoCases.__eo_typeof.case_83 x_a0, EoCases.__eo_typeof.case_84 x_a0, EoCases.__eo_typeof.case_85 x_a0, EoCases.__eo_typeof.case_86 x_a0, EoCases.__eo_typeof.case_87 x_a0, EoCases.__eo_typeof.case_88 x_a0, EoCases.__eo_typeof.case_89 x_a0, EoCases.__eo_typeof.case_90 x_a0, EoCases.__eo_typeof.case_91 x_a0, EoCases.__eo_typeof.case_92 x_a0, EoCases.__eo_typeof.case_93 x_a0, EoCases.__eo_typeof.case_94 x_a0, EoCases.__eo_typeof.case_95 x_a0, EoCases.__eo_typeof.case_96 x_a0, EoCases.__eo_typeof.case_97 x_a0, EoCases.__eo_typeof.case_98 x_a0, EoCases.__eo_typeof.case_99 x_a0, EoCases.__eo_typeof.case_100 x_a0, EoCases.__eo_typeof.case_101 x_a0, EoCases.__eo_typeof.case_102 x_a0, EoCases.__eo_typeof.case_103 x_a0, EoCases.__eo_typeof.case_104 x_a0, EoCases.__eo_typeof.case_105 x_a0, EoCases.__eo_typeof.case_106 x_a0, EoCases.__eo_typeof.case_107 x_a0, EoCases.__eo_typeof.case_108 x_a0, EoCases.__eo_typeof.case_109 x_a0, EoCases.__eo_typeof.case_110 x_a0, EoCases.__eo_typeof.case_111 x_a0, EoCases.__eo_typeof.case_112 x_a0, EoCases.__eo_typeof.case_113 x_a0, EoCases.__eo_typeof.case_114 x_a0, EoCases.__eo_typeof.case_115 x_a0, EoCases.__eo_typeof.case_116 x_a0, EoCases.__eo_typeof.case_117 x_a0, EoCases.__eo_typeof.case_118 x_a0, EoCases.__eo_typeof.case_119 x_a0, EoCases.__eo_typeof.case_120 x_a0, EoCases.__eo_typeof.case_121 x_a0, EoCases.__eo_typeof.case_122 x_a0, EoCases.__eo_typeof.case_123 x_a0, EoCases.__eo_typeof.case_124 x_a0, EoCases.__eo_typeof.case_125 x_a0, EoCases.__eo_typeof.case_126 x_a0, EoCases.__eo_typeof.case_127 x_a0] = [EoCases.__eo_typeof.case_64 x_a0, EoCases.__eo_typeof.case_65 x_a0, EoCases.__eo_typeof.case_66 x_a0, EoCases.__eo_typeof.case_67 x_a0, EoCases.__eo_typeof.case_68 x_a0, EoCases.__eo_typeof.case_69 x_a0, EoCases.__eo_typeof.case_70 x_a0, EoCases.__eo_typeof.case_71 x_a0, EoCases.__eo_typeof.case_72 x_a0, EoCases.__eo_typeof.case_73 x_a0, EoCases.__eo_typeof.case_74 x_a0, EoCases.__eo_typeof.case_75 x_a0, EoCases.__eo_typeof.case_76 x_a0, EoCases.__eo_typeof.case_77 x_a0, EoCases.__eo_typeof.case_78 x_a0, EoCases.__eo_typeof.case_79 x_a0, EoCases.__eo_typeof.case_80 x_a0, EoCases.__eo_typeof.case_81 x_a0, EoCases.__eo_typeof.case_82 x_a0, EoCases.__eo_typeof.case_83 x_a0, EoCases.__eo_typeof.case_84 x_a0, EoCases.__eo_typeof.case_85 x_a0, EoCases.__eo_typeof.case_86 x_a0, EoCases.__eo_typeof.case_87 x_a0, EoCases.__eo_typeof.case_88 x_a0, EoCases.__eo_typeof.case_89 x_a0, EoCases.__eo_typeof.case_90 x_a0, EoCases.__eo_typeof.case_91 x_a0, EoCases.__eo_typeof.case_92 x_a0, EoCases.__eo_typeof.case_93 x_a0, EoCases.__eo_typeof.case_94 x_a0, EoCases.__eo_typeof.case_95 x_a0, EoCases.__eo_typeof.case_96 x_a0, EoCases.__eo_typeof.case_97 x_a0, EoCases.__eo_typeof.case_98 x_a0, EoCases.__eo_typeof.case_99 x_a0, EoCases.__eo_typeof.case_100 x_a0, EoCases.__eo_typeof.case_101 x_a0, EoCases.__eo_typeof.case_102 x_a0, EoCases.__eo_typeof.case_103 x_a0, EoCases.__eo_typeof.case_104 x_a0, EoCases.__eo_typeof.case_105 x_a0, EoCases.__eo_typeof.case_106 x_a0, EoCases.__eo_typeof.case_107 x_a0, EoCases.__eo_typeof.case_108 x_a0, EoCases.__eo_typeof.case_109 x_a0, EoCases.__eo_typeof.case_110 x_a0, EoCases.__eo_typeof.case_111 x_a0] ++ [EoCases.__eo_typeof.case_112 x_a0, EoCases.__eo_typeof.case_113 x_a0, EoCases.__eo_typeof.case_114 x_a0, EoCases.__eo_typeof.case_115 x_a0, EoCases.__eo_typeof.case_116 x_a0, EoCases.__eo_typeof.case_117 x_a0, EoCases.__eo_typeof.case_118 x_a0, EoCases.__eo_typeof.case_119 x_a0, EoCases.__eo_typeof.case_120 x_a0, EoCases.__eo_typeof.case_121 x_a0, EoCases.__eo_typeof.case_122 x_a0, EoCases.__eo_typeof.case_123 x_a0, EoCases.__eo_typeof.case_124 x_a0, EoCases.__eo_typeof.case_125 x_a0, EoCases.__eo_typeof.case_126 x_a0, EoCases.__eo_typeof.case_127 x_a0] ++ [] from rfl)
    otherwise ⟨hl_112, hl_113, hl_114, hl_115, hl_116, hl_117, hl_118, hl_119, hl_120, hl_121, hl_122, hl_123, hl_124, hl_125, hl_126, hl_127⟩ using hn_a0 hl_64 hl_65 hl_66 hl_67 hl_68 hl_69 hl_70 hl_71 hl_72 hl_73 hl_74 hl_75 hl_76 hl_77 hl_78 hl_79 hl_80 hl_81 hl_82 hl_83 hl_84 hl_85 hl_86 hl_87 hl_88 hl_89 hl_90 hl_91 hl_92 hl_93 hl_94 hl_95 hl_96 hl_97 hl_98 hl_99 hl_100 hl_101 hl_102 hl_103 hl_104 hl_105 hl_106 hl_107 hl_108 hl_109 hl_110 hl_111
  group_none hinv4 hG with ⟨hl_64, hl_65, hl_66, hl_67, hl_68, hl_69, hl_70, hl_71, hl_72, hl_73, hl_74, hl_75, hl_76, hl_77, hl_78, hl_79, hl_80, hl_81, hl_82, hl_83, hl_84, hl_85, hl_86, hl_87, hl_88, hl_89, hl_90, hl_91, hl_92, hl_93, hl_94, hl_95, hl_96, hl_97, hl_98, hl_99, hl_100, hl_101, hl_102, hl_103, hl_104, hl_105, hl_106, hl_107, hl_108, hl_109, hl_110, hl_111, hl_112, hl_113, hl_114, hl_115, hl_116, hl_117, hl_118, hl_119, hl_120, hl_121, hl_122, hl_123, hl_124, hl_125, hl_126, hl_127⟩

theorem cases_2_2_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    cases_2_2_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_typeof.case_128 x_a0, EoCases.__eo_typeof.case_129 x_a0, EoCases.__eo_typeof.case_130 x_a0, EoCases.__eo_typeof.case_131 x_a0, EoCases.__eo_typeof.case_132 x_a0, EoCases.__eo_typeof.case_133 x_a0, EoCases.__eo_typeof.case_134 x_a0, EoCases.__eo_typeof.case_135 x_a0, EoCases.__eo_typeof.case_136 x_a0, EoCases.__eo_typeof.case_137 x_a0, EoCases.__eo_typeof.case_138 x_a0, EoCases.__eo_typeof.case_139 x_a0, EoCases.__eo_typeof.case_140 x_a0, EoCases.__eo_typeof.case_141 x_a0, EoCases.__eo_typeof.case_142 x_a0, EoCases.__eo_typeof.case_143 x_a0, EoCases.__eo_typeof.case_144 x_a0, EoCases.__eo_typeof.case_145 x_a0, EoCases.__eo_typeof.case_146 x_a0, EoCases.__eo_typeof.case_147 x_a0, EoCases.__eo_typeof.case_148 x_a0, EoCases.__eo_typeof.case_149 x_a0, EoCases.__eo_typeof.case_150 x_a0, EoCases.__eo_typeof.case_151 x_a0, EoCases.__eo_typeof.case_152 x_a0, EoCases.__eo_typeof.case_153 x_a0, EoCases.__eo_typeof.case_154 x_a0, EoCases.__eo_typeof.case_155 x_a0, EoCases.__eo_typeof.case_156 x_a0, EoCases.__eo_typeof.case_157 x_a0, EoCases.__eo_typeof.case_158 x_a0, EoCases.__eo_typeof.case_159 x_a0, EoCases.__eo_typeof.case_160 x_a0, EoCases.__eo_typeof.case_161 x_a0, EoCases.__eo_typeof.case_162 x_a0, EoCases.__eo_typeof.case_163 x_a0, EoCases.__eo_typeof.case_164 x_a0, EoCases.__eo_typeof.case_165 x_a0, EoCases.__eo_typeof.case_166 x_a0, EoCases.__eo_typeof.case_167 x_a0, EoCases.__eo_typeof.case_168 x_a0, EoCases.__eo_typeof.case_169 x_a0, EoCases.__eo_typeof.case_170 x_a0, EoCases.__eo_typeof.case_171 x_a0, EoCases.__eo_typeof.case_172 x_a0, EoCases.__eo_typeof.case_173 x_a0, EoCases.__eo_typeof.case_174 x_a0, EoCases.__eo_typeof.case_175 x_a0, EoCases.__eo_typeof.case_176 x_a0, EoCases.__eo_typeof.case_177 x_a0, EoCases.__eo_typeof.case_178 x_a0, EoCases.__eo_typeof.case_179 x_a0, EoCases.__eo_typeof.case_180 x_a0, EoCases.__eo_typeof.case_181 x_a0, EoCases.__eo_typeof.case_182 x_a0, EoCases.__eo_typeof.case_183 x_a0, EoCases.__eo_typeof.case_184 x_a0, EoCases.__eo_typeof.case_185 x_a0, EoCases.__eo_typeof.case_186 x_a0, EoCases.__eo_typeof.case_187 x_a0, EoCases.__eo_typeof.case_188 x_a0, EoCases.__eo_typeof.case_189 x_a0, EoCases.__eo_typeof.case_190 x_a0, EoCases.__eo_typeof.case_191 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_128 x_a0 = none ∧ EoCases.__eo_typeof.case_129 x_a0 = none ∧ EoCases.__eo_typeof.case_130 x_a0 = none ∧ EoCases.__eo_typeof.case_131 x_a0 = none ∧ EoCases.__eo_typeof.case_132 x_a0 = none ∧ EoCases.__eo_typeof.case_133 x_a0 = none ∧ EoCases.__eo_typeof.case_134 x_a0 = none ∧ EoCases.__eo_typeof.case_135 x_a0 = none ∧ EoCases.__eo_typeof.case_136 x_a0 = none ∧ EoCases.__eo_typeof.case_137 x_a0 = none ∧ EoCases.__eo_typeof.case_138 x_a0 = none ∧ EoCases.__eo_typeof.case_139 x_a0 = none ∧ EoCases.__eo_typeof.case_140 x_a0 = none ∧ EoCases.__eo_typeof.case_141 x_a0 = none ∧ EoCases.__eo_typeof.case_142 x_a0 = none ∧ EoCases.__eo_typeof.case_143 x_a0 = none ∧ EoCases.__eo_typeof.case_144 x_a0 = none ∧ EoCases.__eo_typeof.case_145 x_a0 = none ∧ EoCases.__eo_typeof.case_146 x_a0 = none ∧ EoCases.__eo_typeof.case_147 x_a0 = none ∧ EoCases.__eo_typeof.case_148 x_a0 = none ∧ EoCases.__eo_typeof.case_149 x_a0 = none ∧ EoCases.__eo_typeof.case_150 x_a0 = none ∧ EoCases.__eo_typeof.case_151 x_a0 = none ∧ EoCases.__eo_typeof.case_152 x_a0 = none ∧ EoCases.__eo_typeof.case_153 x_a0 = none ∧ EoCases.__eo_typeof.case_154 x_a0 = none ∧ EoCases.__eo_typeof.case_155 x_a0 = none ∧ EoCases.__eo_typeof.case_156 x_a0 = none ∧ EoCases.__eo_typeof.case_157 x_a0 = none ∧ EoCases.__eo_typeof.case_158 x_a0 = none ∧ EoCases.__eo_typeof.case_159 x_a0 = none ∧ EoCases.__eo_typeof.case_160 x_a0 = none ∧ EoCases.__eo_typeof.case_161 x_a0 = none ∧ EoCases.__eo_typeof.case_162 x_a0 = none ∧ EoCases.__eo_typeof.case_163 x_a0 = none ∧ EoCases.__eo_typeof.case_164 x_a0 = none ∧ EoCases.__eo_typeof.case_165 x_a0 = none ∧ EoCases.__eo_typeof.case_166 x_a0 = none ∧ EoCases.__eo_typeof.case_167 x_a0 = none ∧ EoCases.__eo_typeof.case_168 x_a0 = none ∧ EoCases.__eo_typeof.case_169 x_a0 = none ∧ EoCases.__eo_typeof.case_170 x_a0 = none ∧ EoCases.__eo_typeof.case_171 x_a0 = none ∧ EoCases.__eo_typeof.case_172 x_a0 = none ∧ EoCases.__eo_typeof.case_173 x_a0 = none ∧ EoCases.__eo_typeof.case_174 x_a0 = none ∧ EoCases.__eo_typeof.case_175 x_a0 = none ∧ EoCases.__eo_typeof.case_176 x_a0 = none ∧ EoCases.__eo_typeof.case_177 x_a0 = none ∧ EoCases.__eo_typeof.case_178 x_a0 = none ∧ EoCases.__eo_typeof.case_179 x_a0 = none ∧ EoCases.__eo_typeof.case_180 x_a0 = none ∧ EoCases.__eo_typeof.case_181 x_a0 = none ∧ EoCases.__eo_typeof.case_182 x_a0 = none ∧ EoCases.__eo_typeof.case_183 x_a0 = none ∧ EoCases.__eo_typeof.case_184 x_a0 = none ∧ EoCases.__eo_typeof.case_185 x_a0 = none ∧ EoCases.__eo_typeof.case_186 x_a0 = none ∧ EoCases.__eo_typeof.case_187 x_a0 = none ∧ EoCases.__eo_typeof.case_188 x_a0 = none ∧ EoCases.__eo_typeof.case_189 x_a0 = none ∧ EoCases.__eo_typeof.case_190 x_a0 = none ∧ EoCases.__eo_typeof.case_191 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_2_2_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  group_step with cases_1_8_eo__24eo_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_128 x_a0, EoCases.__eo_typeof.case_129 x_a0, EoCases.__eo_typeof.case_130 x_a0, EoCases.__eo_typeof.case_131 x_a0, EoCases.__eo_typeof.case_132 x_a0, EoCases.__eo_typeof.case_133 x_a0, EoCases.__eo_typeof.case_134 x_a0, EoCases.__eo_typeof.case_135 x_a0, EoCases.__eo_typeof.case_136 x_a0, EoCases.__eo_typeof.case_137 x_a0, EoCases.__eo_typeof.case_138 x_a0, EoCases.__eo_typeof.case_139 x_a0, EoCases.__eo_typeof.case_140 x_a0, EoCases.__eo_typeof.case_141 x_a0, EoCases.__eo_typeof.case_142 x_a0, EoCases.__eo_typeof.case_143 x_a0, EoCases.__eo_typeof.case_144 x_a0, EoCases.__eo_typeof.case_145 x_a0, EoCases.__eo_typeof.case_146 x_a0, EoCases.__eo_typeof.case_147 x_a0, EoCases.__eo_typeof.case_148 x_a0, EoCases.__eo_typeof.case_149 x_a0, EoCases.__eo_typeof.case_150 x_a0, EoCases.__eo_typeof.case_151 x_a0, EoCases.__eo_typeof.case_152 x_a0, EoCases.__eo_typeof.case_153 x_a0, EoCases.__eo_typeof.case_154 x_a0, EoCases.__eo_typeof.case_155 x_a0, EoCases.__eo_typeof.case_156 x_a0, EoCases.__eo_typeof.case_157 x_a0, EoCases.__eo_typeof.case_158 x_a0, EoCases.__eo_typeof.case_159 x_a0, EoCases.__eo_typeof.case_160 x_a0, EoCases.__eo_typeof.case_161 x_a0, EoCases.__eo_typeof.case_162 x_a0, EoCases.__eo_typeof.case_163 x_a0, EoCases.__eo_typeof.case_164 x_a0, EoCases.__eo_typeof.case_165 x_a0, EoCases.__eo_typeof.case_166 x_a0, EoCases.__eo_typeof.case_167 x_a0, EoCases.__eo_typeof.case_168 x_a0, EoCases.__eo_typeof.case_169 x_a0, EoCases.__eo_typeof.case_170 x_a0, EoCases.__eo_typeof.case_171 x_a0, EoCases.__eo_typeof.case_172 x_a0, EoCases.__eo_typeof.case_173 x_a0, EoCases.__eo_typeof.case_174 x_a0, EoCases.__eo_typeof.case_175 x_a0, EoCases.__eo_typeof.case_176 x_a0, EoCases.__eo_typeof.case_177 x_a0, EoCases.__eo_typeof.case_178 x_a0, EoCases.__eo_typeof.case_179 x_a0, EoCases.__eo_typeof.case_180 x_a0, EoCases.__eo_typeof.case_181 x_a0, EoCases.__eo_typeof.case_182 x_a0, EoCases.__eo_typeof.case_183 x_a0, EoCases.__eo_typeof.case_184 x_a0, EoCases.__eo_typeof.case_185 x_a0, EoCases.__eo_typeof.case_186 x_a0, EoCases.__eo_typeof.case_187 x_a0, EoCases.__eo_typeof.case_188 x_a0, EoCases.__eo_typeof.case_189 x_a0, EoCases.__eo_typeof.case_190 x_a0, EoCases.__eo_typeof.case_191 x_a0] = [] ++ [EoCases.__eo_typeof.case_128 x_a0, EoCases.__eo_typeof.case_129 x_a0, EoCases.__eo_typeof.case_130 x_a0, EoCases.__eo_typeof.case_131 x_a0, EoCases.__eo_typeof.case_132 x_a0, EoCases.__eo_typeof.case_133 x_a0, EoCases.__eo_typeof.case_134 x_a0, EoCases.__eo_typeof.case_135 x_a0, EoCases.__eo_typeof.case_136 x_a0, EoCases.__eo_typeof.case_137 x_a0, EoCases.__eo_typeof.case_138 x_a0, EoCases.__eo_typeof.case_139 x_a0, EoCases.__eo_typeof.case_140 x_a0, EoCases.__eo_typeof.case_141 x_a0, EoCases.__eo_typeof.case_142 x_a0, EoCases.__eo_typeof.case_143 x_a0] ++ [EoCases.__eo_typeof.case_144 x_a0, EoCases.__eo_typeof.case_145 x_a0, EoCases.__eo_typeof.case_146 x_a0, EoCases.__eo_typeof.case_147 x_a0, EoCases.__eo_typeof.case_148 x_a0, EoCases.__eo_typeof.case_149 x_a0, EoCases.__eo_typeof.case_150 x_a0, EoCases.__eo_typeof.case_151 x_a0, EoCases.__eo_typeof.case_152 x_a0, EoCases.__eo_typeof.case_153 x_a0, EoCases.__eo_typeof.case_154 x_a0, EoCases.__eo_typeof.case_155 x_a0, EoCases.__eo_typeof.case_156 x_a0, EoCases.__eo_typeof.case_157 x_a0, EoCases.__eo_typeof.case_158 x_a0, EoCases.__eo_typeof.case_159 x_a0, EoCases.__eo_typeof.case_160 x_a0, EoCases.__eo_typeof.case_161 x_a0, EoCases.__eo_typeof.case_162 x_a0, EoCases.__eo_typeof.case_163 x_a0, EoCases.__eo_typeof.case_164 x_a0, EoCases.__eo_typeof.case_165 x_a0, EoCases.__eo_typeof.case_166 x_a0, EoCases.__eo_typeof.case_167 x_a0, EoCases.__eo_typeof.case_168 x_a0, EoCases.__eo_typeof.case_169 x_a0, EoCases.__eo_typeof.case_170 x_a0, EoCases.__eo_typeof.case_171 x_a0, EoCases.__eo_typeof.case_172 x_a0, EoCases.__eo_typeof.case_173 x_a0, EoCases.__eo_typeof.case_174 x_a0, EoCases.__eo_typeof.case_175 x_a0, EoCases.__eo_typeof.case_176 x_a0, EoCases.__eo_typeof.case_177 x_a0, EoCases.__eo_typeof.case_178 x_a0, EoCases.__eo_typeof.case_179 x_a0, EoCases.__eo_typeof.case_180 x_a0, EoCases.__eo_typeof.case_181 x_a0, EoCases.__eo_typeof.case_182 x_a0, EoCases.__eo_typeof.case_183 x_a0, EoCases.__eo_typeof.case_184 x_a0, EoCases.__eo_typeof.case_185 x_a0, EoCases.__eo_typeof.case_186 x_a0, EoCases.__eo_typeof.case_187 x_a0, EoCases.__eo_typeof.case_188 x_a0, EoCases.__eo_typeof.case_189 x_a0, EoCases.__eo_typeof.case_190 x_a0, EoCases.__eo_typeof.case_191 x_a0] from rfl)
    otherwise ⟨hl_128, hl_129, hl_130, hl_131, hl_132, hl_133, hl_134, hl_135, hl_136, hl_137, hl_138, hl_139, hl_140, hl_141, hl_142, hl_143⟩ using hn_a0
  group_step with cases_1_9_eo__24eo_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_128 x_a0, EoCases.__eo_typeof.case_129 x_a0, EoCases.__eo_typeof.case_130 x_a0, EoCases.__eo_typeof.case_131 x_a0, EoCases.__eo_typeof.case_132 x_a0, EoCases.__eo_typeof.case_133 x_a0, EoCases.__eo_typeof.case_134 x_a0, EoCases.__eo_typeof.case_135 x_a0, EoCases.__eo_typeof.case_136 x_a0, EoCases.__eo_typeof.case_137 x_a0, EoCases.__eo_typeof.case_138 x_a0, EoCases.__eo_typeof.case_139 x_a0, EoCases.__eo_typeof.case_140 x_a0, EoCases.__eo_typeof.case_141 x_a0, EoCases.__eo_typeof.case_142 x_a0, EoCases.__eo_typeof.case_143 x_a0, EoCases.__eo_typeof.case_144 x_a0, EoCases.__eo_typeof.case_145 x_a0, EoCases.__eo_typeof.case_146 x_a0, EoCases.__eo_typeof.case_147 x_a0, EoCases.__eo_typeof.case_148 x_a0, EoCases.__eo_typeof.case_149 x_a0, EoCases.__eo_typeof.case_150 x_a0, EoCases.__eo_typeof.case_151 x_a0, EoCases.__eo_typeof.case_152 x_a0, EoCases.__eo_typeof.case_153 x_a0, EoCases.__eo_typeof.case_154 x_a0, EoCases.__eo_typeof.case_155 x_a0, EoCases.__eo_typeof.case_156 x_a0, EoCases.__eo_typeof.case_157 x_a0, EoCases.__eo_typeof.case_158 x_a0, EoCases.__eo_typeof.case_159 x_a0, EoCases.__eo_typeof.case_160 x_a0, EoCases.__eo_typeof.case_161 x_a0, EoCases.__eo_typeof.case_162 x_a0, EoCases.__eo_typeof.case_163 x_a0, EoCases.__eo_typeof.case_164 x_a0, EoCases.__eo_typeof.case_165 x_a0, EoCases.__eo_typeof.case_166 x_a0, EoCases.__eo_typeof.case_167 x_a0, EoCases.__eo_typeof.case_168 x_a0, EoCases.__eo_typeof.case_169 x_a0, EoCases.__eo_typeof.case_170 x_a0, EoCases.__eo_typeof.case_171 x_a0, EoCases.__eo_typeof.case_172 x_a0, EoCases.__eo_typeof.case_173 x_a0, EoCases.__eo_typeof.case_174 x_a0, EoCases.__eo_typeof.case_175 x_a0, EoCases.__eo_typeof.case_176 x_a0, EoCases.__eo_typeof.case_177 x_a0, EoCases.__eo_typeof.case_178 x_a0, EoCases.__eo_typeof.case_179 x_a0, EoCases.__eo_typeof.case_180 x_a0, EoCases.__eo_typeof.case_181 x_a0, EoCases.__eo_typeof.case_182 x_a0, EoCases.__eo_typeof.case_183 x_a0, EoCases.__eo_typeof.case_184 x_a0, EoCases.__eo_typeof.case_185 x_a0, EoCases.__eo_typeof.case_186 x_a0, EoCases.__eo_typeof.case_187 x_a0, EoCases.__eo_typeof.case_188 x_a0, EoCases.__eo_typeof.case_189 x_a0, EoCases.__eo_typeof.case_190 x_a0, EoCases.__eo_typeof.case_191 x_a0] = [EoCases.__eo_typeof.case_128 x_a0, EoCases.__eo_typeof.case_129 x_a0, EoCases.__eo_typeof.case_130 x_a0, EoCases.__eo_typeof.case_131 x_a0, EoCases.__eo_typeof.case_132 x_a0, EoCases.__eo_typeof.case_133 x_a0, EoCases.__eo_typeof.case_134 x_a0, EoCases.__eo_typeof.case_135 x_a0, EoCases.__eo_typeof.case_136 x_a0, EoCases.__eo_typeof.case_137 x_a0, EoCases.__eo_typeof.case_138 x_a0, EoCases.__eo_typeof.case_139 x_a0, EoCases.__eo_typeof.case_140 x_a0, EoCases.__eo_typeof.case_141 x_a0, EoCases.__eo_typeof.case_142 x_a0, EoCases.__eo_typeof.case_143 x_a0] ++ [EoCases.__eo_typeof.case_144 x_a0, EoCases.__eo_typeof.case_145 x_a0, EoCases.__eo_typeof.case_146 x_a0, EoCases.__eo_typeof.case_147 x_a0, EoCases.__eo_typeof.case_148 x_a0, EoCases.__eo_typeof.case_149 x_a0, EoCases.__eo_typeof.case_150 x_a0, EoCases.__eo_typeof.case_151 x_a0, EoCases.__eo_typeof.case_152 x_a0, EoCases.__eo_typeof.case_153 x_a0, EoCases.__eo_typeof.case_154 x_a0, EoCases.__eo_typeof.case_155 x_a0, EoCases.__eo_typeof.case_156 x_a0, EoCases.__eo_typeof.case_157 x_a0, EoCases.__eo_typeof.case_158 x_a0, EoCases.__eo_typeof.case_159 x_a0] ++ [EoCases.__eo_typeof.case_160 x_a0, EoCases.__eo_typeof.case_161 x_a0, EoCases.__eo_typeof.case_162 x_a0, EoCases.__eo_typeof.case_163 x_a0, EoCases.__eo_typeof.case_164 x_a0, EoCases.__eo_typeof.case_165 x_a0, EoCases.__eo_typeof.case_166 x_a0, EoCases.__eo_typeof.case_167 x_a0, EoCases.__eo_typeof.case_168 x_a0, EoCases.__eo_typeof.case_169 x_a0, EoCases.__eo_typeof.case_170 x_a0, EoCases.__eo_typeof.case_171 x_a0, EoCases.__eo_typeof.case_172 x_a0, EoCases.__eo_typeof.case_173 x_a0, EoCases.__eo_typeof.case_174 x_a0, EoCases.__eo_typeof.case_175 x_a0, EoCases.__eo_typeof.case_176 x_a0, EoCases.__eo_typeof.case_177 x_a0, EoCases.__eo_typeof.case_178 x_a0, EoCases.__eo_typeof.case_179 x_a0, EoCases.__eo_typeof.case_180 x_a0, EoCases.__eo_typeof.case_181 x_a0, EoCases.__eo_typeof.case_182 x_a0, EoCases.__eo_typeof.case_183 x_a0, EoCases.__eo_typeof.case_184 x_a0, EoCases.__eo_typeof.case_185 x_a0, EoCases.__eo_typeof.case_186 x_a0, EoCases.__eo_typeof.case_187 x_a0, EoCases.__eo_typeof.case_188 x_a0, EoCases.__eo_typeof.case_189 x_a0, EoCases.__eo_typeof.case_190 x_a0, EoCases.__eo_typeof.case_191 x_a0] from rfl)
    otherwise ⟨hl_144, hl_145, hl_146, hl_147, hl_148, hl_149, hl_150, hl_151, hl_152, hl_153, hl_154, hl_155, hl_156, hl_157, hl_158, hl_159⟩ using hn_a0 hl_128 hl_129 hl_130 hl_131 hl_132 hl_133 hl_134 hl_135 hl_136 hl_137 hl_138 hl_139 hl_140 hl_141 hl_142 hl_143
  group_step with cases_1_10_eo__24eo_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_128 x_a0, EoCases.__eo_typeof.case_129 x_a0, EoCases.__eo_typeof.case_130 x_a0, EoCases.__eo_typeof.case_131 x_a0, EoCases.__eo_typeof.case_132 x_a0, EoCases.__eo_typeof.case_133 x_a0, EoCases.__eo_typeof.case_134 x_a0, EoCases.__eo_typeof.case_135 x_a0, EoCases.__eo_typeof.case_136 x_a0, EoCases.__eo_typeof.case_137 x_a0, EoCases.__eo_typeof.case_138 x_a0, EoCases.__eo_typeof.case_139 x_a0, EoCases.__eo_typeof.case_140 x_a0, EoCases.__eo_typeof.case_141 x_a0, EoCases.__eo_typeof.case_142 x_a0, EoCases.__eo_typeof.case_143 x_a0, EoCases.__eo_typeof.case_144 x_a0, EoCases.__eo_typeof.case_145 x_a0, EoCases.__eo_typeof.case_146 x_a0, EoCases.__eo_typeof.case_147 x_a0, EoCases.__eo_typeof.case_148 x_a0, EoCases.__eo_typeof.case_149 x_a0, EoCases.__eo_typeof.case_150 x_a0, EoCases.__eo_typeof.case_151 x_a0, EoCases.__eo_typeof.case_152 x_a0, EoCases.__eo_typeof.case_153 x_a0, EoCases.__eo_typeof.case_154 x_a0, EoCases.__eo_typeof.case_155 x_a0, EoCases.__eo_typeof.case_156 x_a0, EoCases.__eo_typeof.case_157 x_a0, EoCases.__eo_typeof.case_158 x_a0, EoCases.__eo_typeof.case_159 x_a0, EoCases.__eo_typeof.case_160 x_a0, EoCases.__eo_typeof.case_161 x_a0, EoCases.__eo_typeof.case_162 x_a0, EoCases.__eo_typeof.case_163 x_a0, EoCases.__eo_typeof.case_164 x_a0, EoCases.__eo_typeof.case_165 x_a0, EoCases.__eo_typeof.case_166 x_a0, EoCases.__eo_typeof.case_167 x_a0, EoCases.__eo_typeof.case_168 x_a0, EoCases.__eo_typeof.case_169 x_a0, EoCases.__eo_typeof.case_170 x_a0, EoCases.__eo_typeof.case_171 x_a0, EoCases.__eo_typeof.case_172 x_a0, EoCases.__eo_typeof.case_173 x_a0, EoCases.__eo_typeof.case_174 x_a0, EoCases.__eo_typeof.case_175 x_a0, EoCases.__eo_typeof.case_176 x_a0, EoCases.__eo_typeof.case_177 x_a0, EoCases.__eo_typeof.case_178 x_a0, EoCases.__eo_typeof.case_179 x_a0, EoCases.__eo_typeof.case_180 x_a0, EoCases.__eo_typeof.case_181 x_a0, EoCases.__eo_typeof.case_182 x_a0, EoCases.__eo_typeof.case_183 x_a0, EoCases.__eo_typeof.case_184 x_a0, EoCases.__eo_typeof.case_185 x_a0, EoCases.__eo_typeof.case_186 x_a0, EoCases.__eo_typeof.case_187 x_a0, EoCases.__eo_typeof.case_188 x_a0, EoCases.__eo_typeof.case_189 x_a0, EoCases.__eo_typeof.case_190 x_a0, EoCases.__eo_typeof.case_191 x_a0] = [EoCases.__eo_typeof.case_128 x_a0, EoCases.__eo_typeof.case_129 x_a0, EoCases.__eo_typeof.case_130 x_a0, EoCases.__eo_typeof.case_131 x_a0, EoCases.__eo_typeof.case_132 x_a0, EoCases.__eo_typeof.case_133 x_a0, EoCases.__eo_typeof.case_134 x_a0, EoCases.__eo_typeof.case_135 x_a0, EoCases.__eo_typeof.case_136 x_a0, EoCases.__eo_typeof.case_137 x_a0, EoCases.__eo_typeof.case_138 x_a0, EoCases.__eo_typeof.case_139 x_a0, EoCases.__eo_typeof.case_140 x_a0, EoCases.__eo_typeof.case_141 x_a0, EoCases.__eo_typeof.case_142 x_a0, EoCases.__eo_typeof.case_143 x_a0, EoCases.__eo_typeof.case_144 x_a0, EoCases.__eo_typeof.case_145 x_a0, EoCases.__eo_typeof.case_146 x_a0, EoCases.__eo_typeof.case_147 x_a0, EoCases.__eo_typeof.case_148 x_a0, EoCases.__eo_typeof.case_149 x_a0, EoCases.__eo_typeof.case_150 x_a0, EoCases.__eo_typeof.case_151 x_a0, EoCases.__eo_typeof.case_152 x_a0, EoCases.__eo_typeof.case_153 x_a0, EoCases.__eo_typeof.case_154 x_a0, EoCases.__eo_typeof.case_155 x_a0, EoCases.__eo_typeof.case_156 x_a0, EoCases.__eo_typeof.case_157 x_a0, EoCases.__eo_typeof.case_158 x_a0, EoCases.__eo_typeof.case_159 x_a0] ++ [EoCases.__eo_typeof.case_160 x_a0, EoCases.__eo_typeof.case_161 x_a0, EoCases.__eo_typeof.case_162 x_a0, EoCases.__eo_typeof.case_163 x_a0, EoCases.__eo_typeof.case_164 x_a0, EoCases.__eo_typeof.case_165 x_a0, EoCases.__eo_typeof.case_166 x_a0, EoCases.__eo_typeof.case_167 x_a0, EoCases.__eo_typeof.case_168 x_a0, EoCases.__eo_typeof.case_169 x_a0, EoCases.__eo_typeof.case_170 x_a0, EoCases.__eo_typeof.case_171 x_a0, EoCases.__eo_typeof.case_172 x_a0, EoCases.__eo_typeof.case_173 x_a0, EoCases.__eo_typeof.case_174 x_a0, EoCases.__eo_typeof.case_175 x_a0] ++ [EoCases.__eo_typeof.case_176 x_a0, EoCases.__eo_typeof.case_177 x_a0, EoCases.__eo_typeof.case_178 x_a0, EoCases.__eo_typeof.case_179 x_a0, EoCases.__eo_typeof.case_180 x_a0, EoCases.__eo_typeof.case_181 x_a0, EoCases.__eo_typeof.case_182 x_a0, EoCases.__eo_typeof.case_183 x_a0, EoCases.__eo_typeof.case_184 x_a0, EoCases.__eo_typeof.case_185 x_a0, EoCases.__eo_typeof.case_186 x_a0, EoCases.__eo_typeof.case_187 x_a0, EoCases.__eo_typeof.case_188 x_a0, EoCases.__eo_typeof.case_189 x_a0, EoCases.__eo_typeof.case_190 x_a0, EoCases.__eo_typeof.case_191 x_a0] from rfl)
    otherwise ⟨hl_160, hl_161, hl_162, hl_163, hl_164, hl_165, hl_166, hl_167, hl_168, hl_169, hl_170, hl_171, hl_172, hl_173, hl_174, hl_175⟩ using hn_a0 hl_128 hl_129 hl_130 hl_131 hl_132 hl_133 hl_134 hl_135 hl_136 hl_137 hl_138 hl_139 hl_140 hl_141 hl_142 hl_143 hl_144 hl_145 hl_146 hl_147 hl_148 hl_149 hl_150 hl_151 hl_152 hl_153 hl_154 hl_155 hl_156 hl_157 hl_158 hl_159
  group_step with cases_1_11_eo__24eo_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_128 x_a0, EoCases.__eo_typeof.case_129 x_a0, EoCases.__eo_typeof.case_130 x_a0, EoCases.__eo_typeof.case_131 x_a0, EoCases.__eo_typeof.case_132 x_a0, EoCases.__eo_typeof.case_133 x_a0, EoCases.__eo_typeof.case_134 x_a0, EoCases.__eo_typeof.case_135 x_a0, EoCases.__eo_typeof.case_136 x_a0, EoCases.__eo_typeof.case_137 x_a0, EoCases.__eo_typeof.case_138 x_a0, EoCases.__eo_typeof.case_139 x_a0, EoCases.__eo_typeof.case_140 x_a0, EoCases.__eo_typeof.case_141 x_a0, EoCases.__eo_typeof.case_142 x_a0, EoCases.__eo_typeof.case_143 x_a0, EoCases.__eo_typeof.case_144 x_a0, EoCases.__eo_typeof.case_145 x_a0, EoCases.__eo_typeof.case_146 x_a0, EoCases.__eo_typeof.case_147 x_a0, EoCases.__eo_typeof.case_148 x_a0, EoCases.__eo_typeof.case_149 x_a0, EoCases.__eo_typeof.case_150 x_a0, EoCases.__eo_typeof.case_151 x_a0, EoCases.__eo_typeof.case_152 x_a0, EoCases.__eo_typeof.case_153 x_a0, EoCases.__eo_typeof.case_154 x_a0, EoCases.__eo_typeof.case_155 x_a0, EoCases.__eo_typeof.case_156 x_a0, EoCases.__eo_typeof.case_157 x_a0, EoCases.__eo_typeof.case_158 x_a0, EoCases.__eo_typeof.case_159 x_a0, EoCases.__eo_typeof.case_160 x_a0, EoCases.__eo_typeof.case_161 x_a0, EoCases.__eo_typeof.case_162 x_a0, EoCases.__eo_typeof.case_163 x_a0, EoCases.__eo_typeof.case_164 x_a0, EoCases.__eo_typeof.case_165 x_a0, EoCases.__eo_typeof.case_166 x_a0, EoCases.__eo_typeof.case_167 x_a0, EoCases.__eo_typeof.case_168 x_a0, EoCases.__eo_typeof.case_169 x_a0, EoCases.__eo_typeof.case_170 x_a0, EoCases.__eo_typeof.case_171 x_a0, EoCases.__eo_typeof.case_172 x_a0, EoCases.__eo_typeof.case_173 x_a0, EoCases.__eo_typeof.case_174 x_a0, EoCases.__eo_typeof.case_175 x_a0, EoCases.__eo_typeof.case_176 x_a0, EoCases.__eo_typeof.case_177 x_a0, EoCases.__eo_typeof.case_178 x_a0, EoCases.__eo_typeof.case_179 x_a0, EoCases.__eo_typeof.case_180 x_a0, EoCases.__eo_typeof.case_181 x_a0, EoCases.__eo_typeof.case_182 x_a0, EoCases.__eo_typeof.case_183 x_a0, EoCases.__eo_typeof.case_184 x_a0, EoCases.__eo_typeof.case_185 x_a0, EoCases.__eo_typeof.case_186 x_a0, EoCases.__eo_typeof.case_187 x_a0, EoCases.__eo_typeof.case_188 x_a0, EoCases.__eo_typeof.case_189 x_a0, EoCases.__eo_typeof.case_190 x_a0, EoCases.__eo_typeof.case_191 x_a0] = [EoCases.__eo_typeof.case_128 x_a0, EoCases.__eo_typeof.case_129 x_a0, EoCases.__eo_typeof.case_130 x_a0, EoCases.__eo_typeof.case_131 x_a0, EoCases.__eo_typeof.case_132 x_a0, EoCases.__eo_typeof.case_133 x_a0, EoCases.__eo_typeof.case_134 x_a0, EoCases.__eo_typeof.case_135 x_a0, EoCases.__eo_typeof.case_136 x_a0, EoCases.__eo_typeof.case_137 x_a0, EoCases.__eo_typeof.case_138 x_a0, EoCases.__eo_typeof.case_139 x_a0, EoCases.__eo_typeof.case_140 x_a0, EoCases.__eo_typeof.case_141 x_a0, EoCases.__eo_typeof.case_142 x_a0, EoCases.__eo_typeof.case_143 x_a0, EoCases.__eo_typeof.case_144 x_a0, EoCases.__eo_typeof.case_145 x_a0, EoCases.__eo_typeof.case_146 x_a0, EoCases.__eo_typeof.case_147 x_a0, EoCases.__eo_typeof.case_148 x_a0, EoCases.__eo_typeof.case_149 x_a0, EoCases.__eo_typeof.case_150 x_a0, EoCases.__eo_typeof.case_151 x_a0, EoCases.__eo_typeof.case_152 x_a0, EoCases.__eo_typeof.case_153 x_a0, EoCases.__eo_typeof.case_154 x_a0, EoCases.__eo_typeof.case_155 x_a0, EoCases.__eo_typeof.case_156 x_a0, EoCases.__eo_typeof.case_157 x_a0, EoCases.__eo_typeof.case_158 x_a0, EoCases.__eo_typeof.case_159 x_a0, EoCases.__eo_typeof.case_160 x_a0, EoCases.__eo_typeof.case_161 x_a0, EoCases.__eo_typeof.case_162 x_a0, EoCases.__eo_typeof.case_163 x_a0, EoCases.__eo_typeof.case_164 x_a0, EoCases.__eo_typeof.case_165 x_a0, EoCases.__eo_typeof.case_166 x_a0, EoCases.__eo_typeof.case_167 x_a0, EoCases.__eo_typeof.case_168 x_a0, EoCases.__eo_typeof.case_169 x_a0, EoCases.__eo_typeof.case_170 x_a0, EoCases.__eo_typeof.case_171 x_a0, EoCases.__eo_typeof.case_172 x_a0, EoCases.__eo_typeof.case_173 x_a0, EoCases.__eo_typeof.case_174 x_a0, EoCases.__eo_typeof.case_175 x_a0] ++ [EoCases.__eo_typeof.case_176 x_a0, EoCases.__eo_typeof.case_177 x_a0, EoCases.__eo_typeof.case_178 x_a0, EoCases.__eo_typeof.case_179 x_a0, EoCases.__eo_typeof.case_180 x_a0, EoCases.__eo_typeof.case_181 x_a0, EoCases.__eo_typeof.case_182 x_a0, EoCases.__eo_typeof.case_183 x_a0, EoCases.__eo_typeof.case_184 x_a0, EoCases.__eo_typeof.case_185 x_a0, EoCases.__eo_typeof.case_186 x_a0, EoCases.__eo_typeof.case_187 x_a0, EoCases.__eo_typeof.case_188 x_a0, EoCases.__eo_typeof.case_189 x_a0, EoCases.__eo_typeof.case_190 x_a0, EoCases.__eo_typeof.case_191 x_a0] ++ [] from rfl)
    otherwise ⟨hl_176, hl_177, hl_178, hl_179, hl_180, hl_181, hl_182, hl_183, hl_184, hl_185, hl_186, hl_187, hl_188, hl_189, hl_190, hl_191⟩ using hn_a0 hl_128 hl_129 hl_130 hl_131 hl_132 hl_133 hl_134 hl_135 hl_136 hl_137 hl_138 hl_139 hl_140 hl_141 hl_142 hl_143 hl_144 hl_145 hl_146 hl_147 hl_148 hl_149 hl_150 hl_151 hl_152 hl_153 hl_154 hl_155 hl_156 hl_157 hl_158 hl_159 hl_160 hl_161 hl_162 hl_163 hl_164 hl_165 hl_166 hl_167 hl_168 hl_169 hl_170 hl_171 hl_172 hl_173 hl_174 hl_175
  group_none hinv4 hG with ⟨hl_128, hl_129, hl_130, hl_131, hl_132, hl_133, hl_134, hl_135, hl_136, hl_137, hl_138, hl_139, hl_140, hl_141, hl_142, hl_143, hl_144, hl_145, hl_146, hl_147, hl_148, hl_149, hl_150, hl_151, hl_152, hl_153, hl_154, hl_155, hl_156, hl_157, hl_158, hl_159, hl_160, hl_161, hl_162, hl_163, hl_164, hl_165, hl_166, hl_167, hl_168, hl_169, hl_170, hl_171, hl_172, hl_173, hl_174, hl_175, hl_176, hl_177, hl_178, hl_179, hl_180, hl_181, hl_182, hl_183, hl_184, hl_185, hl_186, hl_187, hl_188, hl_189, hl_190, hl_191⟩

theorem cases_2_3_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    cases_2_3_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_typeof.case_192 x_a0, EoCases.__eo_typeof.case_193 x_a0, EoCases.__eo_typeof.case_194 x_a0, EoCases.__eo_typeof.case_195 x_a0, EoCases.__eo_typeof.case_196 x_a0, EoCases.__eo_typeof.case_197 x_a0, EoCases.__eo_typeof.case_198 x_a0, EoCases.__eo_typeof.case_199 x_a0, EoCases.__eo_typeof.case_200 x_a0, EoCases.__eo_typeof.case_201 x_a0, EoCases.__eo_typeof.case_202 x_a0, EoCases.__eo_typeof.case_203 x_a0, EoCases.__eo_typeof.case_204 x_a0, EoCases.__eo_typeof.case_205 x_a0, EoCases.__eo_typeof.case_206 x_a0, EoCases.__eo_typeof.case_207 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof.case_192 x_a0 = none ∧ EoCases.__eo_typeof.case_193 x_a0 = none ∧ EoCases.__eo_typeof.case_194 x_a0 = none ∧ EoCases.__eo_typeof.case_195 x_a0 = none ∧ EoCases.__eo_typeof.case_196 x_a0 = none ∧ EoCases.__eo_typeof.case_197 x_a0 = none ∧ EoCases.__eo_typeof.case_198 x_a0 = none ∧ EoCases.__eo_typeof.case_199 x_a0 = none ∧ EoCases.__eo_typeof.case_200 x_a0 = none ∧ EoCases.__eo_typeof.case_201 x_a0 = none ∧ EoCases.__eo_typeof.case_202 x_a0 = none ∧ EoCases.__eo_typeof.case_203 x_a0 = none ∧ EoCases.__eo_typeof.case_204 x_a0 = none ∧ EoCases.__eo_typeof.case_205 x_a0 = none ∧ EoCases.__eo_typeof.case_206 x_a0 = none ∧ EoCases.__eo_typeof.case_207 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_2_3_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  group_step with cases_1_12_eo__24eo_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_192 x_a0, EoCases.__eo_typeof.case_193 x_a0, EoCases.__eo_typeof.case_194 x_a0, EoCases.__eo_typeof.case_195 x_a0, EoCases.__eo_typeof.case_196 x_a0, EoCases.__eo_typeof.case_197 x_a0, EoCases.__eo_typeof.case_198 x_a0, EoCases.__eo_typeof.case_199 x_a0, EoCases.__eo_typeof.case_200 x_a0, EoCases.__eo_typeof.case_201 x_a0, EoCases.__eo_typeof.case_202 x_a0, EoCases.__eo_typeof.case_203 x_a0, EoCases.__eo_typeof.case_204 x_a0, EoCases.__eo_typeof.case_205 x_a0, EoCases.__eo_typeof.case_206 x_a0, EoCases.__eo_typeof.case_207 x_a0] = [] ++ [EoCases.__eo_typeof.case_192 x_a0, EoCases.__eo_typeof.case_193 x_a0, EoCases.__eo_typeof.case_194 x_a0, EoCases.__eo_typeof.case_195 x_a0, EoCases.__eo_typeof.case_196 x_a0, EoCases.__eo_typeof.case_197 x_a0, EoCases.__eo_typeof.case_198 x_a0, EoCases.__eo_typeof.case_199 x_a0, EoCases.__eo_typeof.case_200 x_a0, EoCases.__eo_typeof.case_201 x_a0, EoCases.__eo_typeof.case_202 x_a0, EoCases.__eo_typeof.case_203 x_a0, EoCases.__eo_typeof.case_204 x_a0, EoCases.__eo_typeof.case_205 x_a0, EoCases.__eo_typeof.case_206 x_a0, EoCases.__eo_typeof.case_207 x_a0] ++ [] from rfl)
    otherwise ⟨hl_192, hl_193, hl_194, hl_195, hl_196, hl_197, hl_198, hl_199, hl_200, hl_201, hl_202, hl_203, hl_204, hl_205, hl_206, hl_207⟩ using hn_a0
  group_none hinv1 hG with ⟨hl_192, hl_193, hl_194, hl_195, hl_196, hl_197, hl_198, hl_199, hl_200, hl_201, hl_202, hl_203, hl_204, hl_205, hl_206, hl_207⟩

/-- logos's `__eo_typeof` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5ftypeof.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_typeof x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_typeof.case_0 x_a0, EoCases.__eo_typeof.case_1 x_a0, EoCases.__eo_typeof.case_2 x_a0, EoCases.__eo_typeof.case_3 x_a0, EoCases.__eo_typeof.case_4 x_a0, EoCases.__eo_typeof.case_5 x_a0, EoCases.__eo_typeof.case_6 x_a0, EoCases.__eo_typeof.case_7 x_a0, EoCases.__eo_typeof.case_8 x_a0, EoCases.__eo_typeof.case_9 x_a0, EoCases.__eo_typeof.case_10 x_a0, EoCases.__eo_typeof.case_11 x_a0, EoCases.__eo_typeof.case_12 x_a0, EoCases.__eo_typeof.case_13 x_a0, EoCases.__eo_typeof.case_14 x_a0, EoCases.__eo_typeof.case_15 x_a0, EoCases.__eo_typeof.case_16 x_a0, EoCases.__eo_typeof.case_17 x_a0, EoCases.__eo_typeof.case_18 x_a0, EoCases.__eo_typeof.case_19 x_a0, EoCases.__eo_typeof.case_20 x_a0, EoCases.__eo_typeof.case_21 x_a0, EoCases.__eo_typeof.case_22 x_a0, EoCases.__eo_typeof.case_23 x_a0, EoCases.__eo_typeof.case_24 x_a0, EoCases.__eo_typeof.case_25 x_a0, EoCases.__eo_typeof.case_26 x_a0, EoCases.__eo_typeof.case_27 x_a0, EoCases.__eo_typeof.case_28 x_a0, EoCases.__eo_typeof.case_29 x_a0, EoCases.__eo_typeof.case_30 x_a0, EoCases.__eo_typeof.case_31 x_a0, EoCases.__eo_typeof.case_32 x_a0, EoCases.__eo_typeof.case_33 x_a0, EoCases.__eo_typeof.case_34 x_a0, EoCases.__eo_typeof.case_35 x_a0, EoCases.__eo_typeof.case_36 x_a0, EoCases.__eo_typeof.case_37 x_a0, EoCases.__eo_typeof.case_38 x_a0, EoCases.__eo_typeof.case_39 x_a0, EoCases.__eo_typeof.case_40 x_a0, EoCases.__eo_typeof.case_41 x_a0, EoCases.__eo_typeof.case_42 x_a0, EoCases.__eo_typeof.case_43 x_a0, EoCases.__eo_typeof.case_44 x_a0, EoCases.__eo_typeof.case_45 x_a0, EoCases.__eo_typeof.case_46 x_a0, EoCases.__eo_typeof.case_47 x_a0, EoCases.__eo_typeof.case_48 x_a0, EoCases.__eo_typeof.case_49 x_a0, EoCases.__eo_typeof.case_50 x_a0, EoCases.__eo_typeof.case_51 x_a0, EoCases.__eo_typeof.case_52 x_a0, EoCases.__eo_typeof.case_53 x_a0, EoCases.__eo_typeof.case_54 x_a0, EoCases.__eo_typeof.case_55 x_a0, EoCases.__eo_typeof.case_56 x_a0, EoCases.__eo_typeof.case_57 x_a0, EoCases.__eo_typeof.case_58 x_a0, EoCases.__eo_typeof.case_59 x_a0, EoCases.__eo_typeof.case_60 x_a0, EoCases.__eo_typeof.case_61 x_a0, EoCases.__eo_typeof.case_62 x_a0, EoCases.__eo_typeof.case_63 x_a0, EoCases.__eo_typeof.case_64 x_a0, EoCases.__eo_typeof.case_65 x_a0, EoCases.__eo_typeof.case_66 x_a0, EoCases.__eo_typeof.case_67 x_a0, EoCases.__eo_typeof.case_68 x_a0, EoCases.__eo_typeof.case_69 x_a0, EoCases.__eo_typeof.case_70 x_a0, EoCases.__eo_typeof.case_71 x_a0, EoCases.__eo_typeof.case_72 x_a0, EoCases.__eo_typeof.case_73 x_a0, EoCases.__eo_typeof.case_74 x_a0, EoCases.__eo_typeof.case_75 x_a0, EoCases.__eo_typeof.case_76 x_a0, EoCases.__eo_typeof.case_77 x_a0, EoCases.__eo_typeof.case_78 x_a0, EoCases.__eo_typeof.case_79 x_a0, EoCases.__eo_typeof.case_80 x_a0, EoCases.__eo_typeof.case_81 x_a0, EoCases.__eo_typeof.case_82 x_a0, EoCases.__eo_typeof.case_83 x_a0, EoCases.__eo_typeof.case_84 x_a0, EoCases.__eo_typeof.case_85 x_a0, EoCases.__eo_typeof.case_86 x_a0, EoCases.__eo_typeof.case_87 x_a0, EoCases.__eo_typeof.case_88 x_a0, EoCases.__eo_typeof.case_89 x_a0, EoCases.__eo_typeof.case_90 x_a0, EoCases.__eo_typeof.case_91 x_a0, EoCases.__eo_typeof.case_92 x_a0, EoCases.__eo_typeof.case_93 x_a0, EoCases.__eo_typeof.case_94 x_a0, EoCases.__eo_typeof.case_95 x_a0, EoCases.__eo_typeof.case_96 x_a0, EoCases.__eo_typeof.case_97 x_a0, EoCases.__eo_typeof.case_98 x_a0, EoCases.__eo_typeof.case_99 x_a0, EoCases.__eo_typeof.case_100 x_a0, EoCases.__eo_typeof.case_101 x_a0, EoCases.__eo_typeof.case_102 x_a0, EoCases.__eo_typeof.case_103 x_a0, EoCases.__eo_typeof.case_104 x_a0, EoCases.__eo_typeof.case_105 x_a0, EoCases.__eo_typeof.case_106 x_a0, EoCases.__eo_typeof.case_107 x_a0, EoCases.__eo_typeof.case_108 x_a0, EoCases.__eo_typeof.case_109 x_a0, EoCases.__eo_typeof.case_110 x_a0, EoCases.__eo_typeof.case_111 x_a0, EoCases.__eo_typeof.case_112 x_a0, EoCases.__eo_typeof.case_113 x_a0, EoCases.__eo_typeof.case_114 x_a0, EoCases.__eo_typeof.case_115 x_a0, EoCases.__eo_typeof.case_116 x_a0, EoCases.__eo_typeof.case_117 x_a0, EoCases.__eo_typeof.case_118 x_a0, EoCases.__eo_typeof.case_119 x_a0, EoCases.__eo_typeof.case_120 x_a0, EoCases.__eo_typeof.case_121 x_a0, EoCases.__eo_typeof.case_122 x_a0, EoCases.__eo_typeof.case_123 x_a0, EoCases.__eo_typeof.case_124 x_a0, EoCases.__eo_typeof.case_125 x_a0, EoCases.__eo_typeof.case_126 x_a0, EoCases.__eo_typeof.case_127 x_a0, EoCases.__eo_typeof.case_128 x_a0, EoCases.__eo_typeof.case_129 x_a0, EoCases.__eo_typeof.case_130 x_a0, EoCases.__eo_typeof.case_131 x_a0, EoCases.__eo_typeof.case_132 x_a0, EoCases.__eo_typeof.case_133 x_a0, EoCases.__eo_typeof.case_134 x_a0, EoCases.__eo_typeof.case_135 x_a0, EoCases.__eo_typeof.case_136 x_a0, EoCases.__eo_typeof.case_137 x_a0, EoCases.__eo_typeof.case_138 x_a0, EoCases.__eo_typeof.case_139 x_a0, EoCases.__eo_typeof.case_140 x_a0, EoCases.__eo_typeof.case_141 x_a0, EoCases.__eo_typeof.case_142 x_a0, EoCases.__eo_typeof.case_143 x_a0, EoCases.__eo_typeof.case_144 x_a0, EoCases.__eo_typeof.case_145 x_a0, EoCases.__eo_typeof.case_146 x_a0, EoCases.__eo_typeof.case_147 x_a0, EoCases.__eo_typeof.case_148 x_a0, EoCases.__eo_typeof.case_149 x_a0, EoCases.__eo_typeof.case_150 x_a0, EoCases.__eo_typeof.case_151 x_a0, EoCases.__eo_typeof.case_152 x_a0, EoCases.__eo_typeof.case_153 x_a0, EoCases.__eo_typeof.case_154 x_a0, EoCases.__eo_typeof.case_155 x_a0, EoCases.__eo_typeof.case_156 x_a0, EoCases.__eo_typeof.case_157 x_a0, EoCases.__eo_typeof.case_158 x_a0, EoCases.__eo_typeof.case_159 x_a0, EoCases.__eo_typeof.case_160 x_a0, EoCases.__eo_typeof.case_161 x_a0, EoCases.__eo_typeof.case_162 x_a0, EoCases.__eo_typeof.case_163 x_a0, EoCases.__eo_typeof.case_164 x_a0, EoCases.__eo_typeof.case_165 x_a0, EoCases.__eo_typeof.case_166 x_a0, EoCases.__eo_typeof.case_167 x_a0, EoCases.__eo_typeof.case_168 x_a0, EoCases.__eo_typeof.case_169 x_a0, EoCases.__eo_typeof.case_170 x_a0, EoCases.__eo_typeof.case_171 x_a0, EoCases.__eo_typeof.case_172 x_a0, EoCases.__eo_typeof.case_173 x_a0, EoCases.__eo_typeof.case_174 x_a0, EoCases.__eo_typeof.case_175 x_a0, EoCases.__eo_typeof.case_176 x_a0, EoCases.__eo_typeof.case_177 x_a0, EoCases.__eo_typeof.case_178 x_a0, EoCases.__eo_typeof.case_179 x_a0, EoCases.__eo_typeof.case_180 x_a0, EoCases.__eo_typeof.case_181 x_a0, EoCases.__eo_typeof.case_182 x_a0, EoCases.__eo_typeof.case_183 x_a0, EoCases.__eo_typeof.case_184 x_a0, EoCases.__eo_typeof.case_185 x_a0, EoCases.__eo_typeof.case_186 x_a0, EoCases.__eo_typeof.case_187 x_a0, EoCases.__eo_typeof.case_188 x_a0, EoCases.__eo_typeof.case_189 x_a0, EoCases.__eo_typeof.case_190 x_a0, EoCases.__eo_typeof.case_191 x_a0, EoCases.__eo_typeof.case_192 x_a0, EoCases.__eo_typeof.case_193 x_a0, EoCases.__eo_typeof.case_194 x_a0, EoCases.__eo_typeof.case_195 x_a0, EoCases.__eo_typeof.case_196 x_a0, EoCases.__eo_typeof.case_197 x_a0, EoCases.__eo_typeof.case_198 x_a0, EoCases.__eo_typeof.case_199 x_a0, EoCases.__eo_typeof.case_200 x_a0, EoCases.__eo_typeof.case_201 x_a0, EoCases.__eo_typeof.case_202 x_a0, EoCases.__eo_typeof.case_203 x_a0, EoCases.__eo_typeof.case_204 x_a0, EoCases.__eo_typeof.case_205 x_a0, EoCases.__eo_typeof.case_206 x_a0, EoCases.__eo_typeof.case_207 x_a0] HasStuck.stuck) := by
  logos_eq_large

theorem body_eo__24eo_5ftypeof_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5ftypeof s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5ftypeof.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5ftypeof
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  body_group_step with cases_2_0_eo__24eo_5ftypeof_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_0 x_a0, EoCases.__eo_typeof.case_1 x_a0, EoCases.__eo_typeof.case_2 x_a0, EoCases.__eo_typeof.case_3 x_a0, EoCases.__eo_typeof.case_4 x_a0, EoCases.__eo_typeof.case_5 x_a0, EoCases.__eo_typeof.case_6 x_a0, EoCases.__eo_typeof.case_7 x_a0, EoCases.__eo_typeof.case_8 x_a0, EoCases.__eo_typeof.case_9 x_a0, EoCases.__eo_typeof.case_10 x_a0, EoCases.__eo_typeof.case_11 x_a0, EoCases.__eo_typeof.case_12 x_a0, EoCases.__eo_typeof.case_13 x_a0, EoCases.__eo_typeof.case_14 x_a0, EoCases.__eo_typeof.case_15 x_a0, EoCases.__eo_typeof.case_16 x_a0, EoCases.__eo_typeof.case_17 x_a0, EoCases.__eo_typeof.case_18 x_a0, EoCases.__eo_typeof.case_19 x_a0, EoCases.__eo_typeof.case_20 x_a0, EoCases.__eo_typeof.case_21 x_a0, EoCases.__eo_typeof.case_22 x_a0, EoCases.__eo_typeof.case_23 x_a0, EoCases.__eo_typeof.case_24 x_a0, EoCases.__eo_typeof.case_25 x_a0, EoCases.__eo_typeof.case_26 x_a0, EoCases.__eo_typeof.case_27 x_a0, EoCases.__eo_typeof.case_28 x_a0, EoCases.__eo_typeof.case_29 x_a0, EoCases.__eo_typeof.case_30 x_a0, EoCases.__eo_typeof.case_31 x_a0, EoCases.__eo_typeof.case_32 x_a0, EoCases.__eo_typeof.case_33 x_a0, EoCases.__eo_typeof.case_34 x_a0, EoCases.__eo_typeof.case_35 x_a0, EoCases.__eo_typeof.case_36 x_a0, EoCases.__eo_typeof.case_37 x_a0, EoCases.__eo_typeof.case_38 x_a0, EoCases.__eo_typeof.case_39 x_a0, EoCases.__eo_typeof.case_40 x_a0, EoCases.__eo_typeof.case_41 x_a0, EoCases.__eo_typeof.case_42 x_a0, EoCases.__eo_typeof.case_43 x_a0, EoCases.__eo_typeof.case_44 x_a0, EoCases.__eo_typeof.case_45 x_a0, EoCases.__eo_typeof.case_46 x_a0, EoCases.__eo_typeof.case_47 x_a0, EoCases.__eo_typeof.case_48 x_a0, EoCases.__eo_typeof.case_49 x_a0, EoCases.__eo_typeof.case_50 x_a0, EoCases.__eo_typeof.case_51 x_a0, EoCases.__eo_typeof.case_52 x_a0, EoCases.__eo_typeof.case_53 x_a0, EoCases.__eo_typeof.case_54 x_a0, EoCases.__eo_typeof.case_55 x_a0, EoCases.__eo_typeof.case_56 x_a0, EoCases.__eo_typeof.case_57 x_a0, EoCases.__eo_typeof.case_58 x_a0, EoCases.__eo_typeof.case_59 x_a0, EoCases.__eo_typeof.case_60 x_a0, EoCases.__eo_typeof.case_61 x_a0, EoCases.__eo_typeof.case_62 x_a0, EoCases.__eo_typeof.case_63 x_a0, EoCases.__eo_typeof.case_64 x_a0, EoCases.__eo_typeof.case_65 x_a0, EoCases.__eo_typeof.case_66 x_a0, EoCases.__eo_typeof.case_67 x_a0, EoCases.__eo_typeof.case_68 x_a0, EoCases.__eo_typeof.case_69 x_a0, EoCases.__eo_typeof.case_70 x_a0, EoCases.__eo_typeof.case_71 x_a0, EoCases.__eo_typeof.case_72 x_a0, EoCases.__eo_typeof.case_73 x_a0, EoCases.__eo_typeof.case_74 x_a0, EoCases.__eo_typeof.case_75 x_a0, EoCases.__eo_typeof.case_76 x_a0, EoCases.__eo_typeof.case_77 x_a0, EoCases.__eo_typeof.case_78 x_a0, EoCases.__eo_typeof.case_79 x_a0, EoCases.__eo_typeof.case_80 x_a0, EoCases.__eo_typeof.case_81 x_a0, EoCases.__eo_typeof.case_82 x_a0, EoCases.__eo_typeof.case_83 x_a0, EoCases.__eo_typeof.case_84 x_a0, EoCases.__eo_typeof.case_85 x_a0, EoCases.__eo_typeof.case_86 x_a0, EoCases.__eo_typeof.case_87 x_a0, EoCases.__eo_typeof.case_88 x_a0, EoCases.__eo_typeof.case_89 x_a0, EoCases.__eo_typeof.case_90 x_a0, EoCases.__eo_typeof.case_91 x_a0, EoCases.__eo_typeof.case_92 x_a0, EoCases.__eo_typeof.case_93 x_a0, EoCases.__eo_typeof.case_94 x_a0, EoCases.__eo_typeof.case_95 x_a0, EoCases.__eo_typeof.case_96 x_a0, EoCases.__eo_typeof.case_97 x_a0, EoCases.__eo_typeof.case_98 x_a0, EoCases.__eo_typeof.case_99 x_a0, EoCases.__eo_typeof.case_100 x_a0, EoCases.__eo_typeof.case_101 x_a0, EoCases.__eo_typeof.case_102 x_a0, EoCases.__eo_typeof.case_103 x_a0, EoCases.__eo_typeof.case_104 x_a0, EoCases.__eo_typeof.case_105 x_a0, EoCases.__eo_typeof.case_106 x_a0, EoCases.__eo_typeof.case_107 x_a0, EoCases.__eo_typeof.case_108 x_a0, EoCases.__eo_typeof.case_109 x_a0, EoCases.__eo_typeof.case_110 x_a0, EoCases.__eo_typeof.case_111 x_a0, EoCases.__eo_typeof.case_112 x_a0, EoCases.__eo_typeof.case_113 x_a0, EoCases.__eo_typeof.case_114 x_a0, EoCases.__eo_typeof.case_115 x_a0, EoCases.__eo_typeof.case_116 x_a0, EoCases.__eo_typeof.case_117 x_a0, EoCases.__eo_typeof.case_118 x_a0, EoCases.__eo_typeof.case_119 x_a0, EoCases.__eo_typeof.case_120 x_a0, EoCases.__eo_typeof.case_121 x_a0, EoCases.__eo_typeof.case_122 x_a0, EoCases.__eo_typeof.case_123 x_a0, EoCases.__eo_typeof.case_124 x_a0, EoCases.__eo_typeof.case_125 x_a0, EoCases.__eo_typeof.case_126 x_a0, EoCases.__eo_typeof.case_127 x_a0, EoCases.__eo_typeof.case_128 x_a0, EoCases.__eo_typeof.case_129 x_a0, EoCases.__eo_typeof.case_130 x_a0, EoCases.__eo_typeof.case_131 x_a0, EoCases.__eo_typeof.case_132 x_a0, EoCases.__eo_typeof.case_133 x_a0, EoCases.__eo_typeof.case_134 x_a0, EoCases.__eo_typeof.case_135 x_a0, EoCases.__eo_typeof.case_136 x_a0, EoCases.__eo_typeof.case_137 x_a0, EoCases.__eo_typeof.case_138 x_a0, EoCases.__eo_typeof.case_139 x_a0, EoCases.__eo_typeof.case_140 x_a0, EoCases.__eo_typeof.case_141 x_a0, EoCases.__eo_typeof.case_142 x_a0, EoCases.__eo_typeof.case_143 x_a0, EoCases.__eo_typeof.case_144 x_a0, EoCases.__eo_typeof.case_145 x_a0, EoCases.__eo_typeof.case_146 x_a0, EoCases.__eo_typeof.case_147 x_a0, EoCases.__eo_typeof.case_148 x_a0, EoCases.__eo_typeof.case_149 x_a0, EoCases.__eo_typeof.case_150 x_a0, EoCases.__eo_typeof.case_151 x_a0, EoCases.__eo_typeof.case_152 x_a0, EoCases.__eo_typeof.case_153 x_a0, EoCases.__eo_typeof.case_154 x_a0, EoCases.__eo_typeof.case_155 x_a0, EoCases.__eo_typeof.case_156 x_a0, EoCases.__eo_typeof.case_157 x_a0, EoCases.__eo_typeof.case_158 x_a0, EoCases.__eo_typeof.case_159 x_a0, EoCases.__eo_typeof.case_160 x_a0, EoCases.__eo_typeof.case_161 x_a0, EoCases.__eo_typeof.case_162 x_a0, EoCases.__eo_typeof.case_163 x_a0, EoCases.__eo_typeof.case_164 x_a0, EoCases.__eo_typeof.case_165 x_a0, EoCases.__eo_typeof.case_166 x_a0, EoCases.__eo_typeof.case_167 x_a0, EoCases.__eo_typeof.case_168 x_a0, EoCases.__eo_typeof.case_169 x_a0, EoCases.__eo_typeof.case_170 x_a0, EoCases.__eo_typeof.case_171 x_a0, EoCases.__eo_typeof.case_172 x_a0, EoCases.__eo_typeof.case_173 x_a0, EoCases.__eo_typeof.case_174 x_a0, EoCases.__eo_typeof.case_175 x_a0, EoCases.__eo_typeof.case_176 x_a0, EoCases.__eo_typeof.case_177 x_a0, EoCases.__eo_typeof.case_178 x_a0, EoCases.__eo_typeof.case_179 x_a0, EoCases.__eo_typeof.case_180 x_a0, EoCases.__eo_typeof.case_181 x_a0, EoCases.__eo_typeof.case_182 x_a0, EoCases.__eo_typeof.case_183 x_a0, EoCases.__eo_typeof.case_184 x_a0, EoCases.__eo_typeof.case_185 x_a0, EoCases.__eo_typeof.case_186 x_a0, EoCases.__eo_typeof.case_187 x_a0, EoCases.__eo_typeof.case_188 x_a0, EoCases.__eo_typeof.case_189 x_a0, EoCases.__eo_typeof.case_190 x_a0, EoCases.__eo_typeof.case_191 x_a0, EoCases.__eo_typeof.case_192 x_a0, EoCases.__eo_typeof.case_193 x_a0, EoCases.__eo_typeof.case_194 x_a0, EoCases.__eo_typeof.case_195 x_a0, EoCases.__eo_typeof.case_196 x_a0, EoCases.__eo_typeof.case_197 x_a0, EoCases.__eo_typeof.case_198 x_a0, EoCases.__eo_typeof.case_199 x_a0, EoCases.__eo_typeof.case_200 x_a0, EoCases.__eo_typeof.case_201 x_a0, EoCases.__eo_typeof.case_202 x_a0, EoCases.__eo_typeof.case_203 x_a0, EoCases.__eo_typeof.case_204 x_a0, EoCases.__eo_typeof.case_205 x_a0, EoCases.__eo_typeof.case_206 x_a0, EoCases.__eo_typeof.case_207 x_a0] = [] ++ [EoCases.__eo_typeof.case_0 x_a0, EoCases.__eo_typeof.case_1 x_a0, EoCases.__eo_typeof.case_2 x_a0, EoCases.__eo_typeof.case_3 x_a0, EoCases.__eo_typeof.case_4 x_a0, EoCases.__eo_typeof.case_5 x_a0, EoCases.__eo_typeof.case_6 x_a0, EoCases.__eo_typeof.case_7 x_a0, EoCases.__eo_typeof.case_8 x_a0, EoCases.__eo_typeof.case_9 x_a0, EoCases.__eo_typeof.case_10 x_a0, EoCases.__eo_typeof.case_11 x_a0, EoCases.__eo_typeof.case_12 x_a0, EoCases.__eo_typeof.case_13 x_a0, EoCases.__eo_typeof.case_14 x_a0, EoCases.__eo_typeof.case_15 x_a0, EoCases.__eo_typeof.case_16 x_a0, EoCases.__eo_typeof.case_17 x_a0, EoCases.__eo_typeof.case_18 x_a0, EoCases.__eo_typeof.case_19 x_a0, EoCases.__eo_typeof.case_20 x_a0, EoCases.__eo_typeof.case_21 x_a0, EoCases.__eo_typeof.case_22 x_a0, EoCases.__eo_typeof.case_23 x_a0, EoCases.__eo_typeof.case_24 x_a0, EoCases.__eo_typeof.case_25 x_a0, EoCases.__eo_typeof.case_26 x_a0, EoCases.__eo_typeof.case_27 x_a0, EoCases.__eo_typeof.case_28 x_a0, EoCases.__eo_typeof.case_29 x_a0, EoCases.__eo_typeof.case_30 x_a0, EoCases.__eo_typeof.case_31 x_a0, EoCases.__eo_typeof.case_32 x_a0, EoCases.__eo_typeof.case_33 x_a0, EoCases.__eo_typeof.case_34 x_a0, EoCases.__eo_typeof.case_35 x_a0, EoCases.__eo_typeof.case_36 x_a0, EoCases.__eo_typeof.case_37 x_a0, EoCases.__eo_typeof.case_38 x_a0, EoCases.__eo_typeof.case_39 x_a0, EoCases.__eo_typeof.case_40 x_a0, EoCases.__eo_typeof.case_41 x_a0, EoCases.__eo_typeof.case_42 x_a0, EoCases.__eo_typeof.case_43 x_a0, EoCases.__eo_typeof.case_44 x_a0, EoCases.__eo_typeof.case_45 x_a0, EoCases.__eo_typeof.case_46 x_a0, EoCases.__eo_typeof.case_47 x_a0, EoCases.__eo_typeof.case_48 x_a0, EoCases.__eo_typeof.case_49 x_a0, EoCases.__eo_typeof.case_50 x_a0, EoCases.__eo_typeof.case_51 x_a0, EoCases.__eo_typeof.case_52 x_a0, EoCases.__eo_typeof.case_53 x_a0, EoCases.__eo_typeof.case_54 x_a0, EoCases.__eo_typeof.case_55 x_a0, EoCases.__eo_typeof.case_56 x_a0, EoCases.__eo_typeof.case_57 x_a0, EoCases.__eo_typeof.case_58 x_a0, EoCases.__eo_typeof.case_59 x_a0, EoCases.__eo_typeof.case_60 x_a0, EoCases.__eo_typeof.case_61 x_a0, EoCases.__eo_typeof.case_62 x_a0, EoCases.__eo_typeof.case_63 x_a0] ++ [EoCases.__eo_typeof.case_64 x_a0, EoCases.__eo_typeof.case_65 x_a0, EoCases.__eo_typeof.case_66 x_a0, EoCases.__eo_typeof.case_67 x_a0, EoCases.__eo_typeof.case_68 x_a0, EoCases.__eo_typeof.case_69 x_a0, EoCases.__eo_typeof.case_70 x_a0, EoCases.__eo_typeof.case_71 x_a0, EoCases.__eo_typeof.case_72 x_a0, EoCases.__eo_typeof.case_73 x_a0, EoCases.__eo_typeof.case_74 x_a0, EoCases.__eo_typeof.case_75 x_a0, EoCases.__eo_typeof.case_76 x_a0, EoCases.__eo_typeof.case_77 x_a0, EoCases.__eo_typeof.case_78 x_a0, EoCases.__eo_typeof.case_79 x_a0, EoCases.__eo_typeof.case_80 x_a0, EoCases.__eo_typeof.case_81 x_a0, EoCases.__eo_typeof.case_82 x_a0, EoCases.__eo_typeof.case_83 x_a0, EoCases.__eo_typeof.case_84 x_a0, EoCases.__eo_typeof.case_85 x_a0, EoCases.__eo_typeof.case_86 x_a0, EoCases.__eo_typeof.case_87 x_a0, EoCases.__eo_typeof.case_88 x_a0, EoCases.__eo_typeof.case_89 x_a0, EoCases.__eo_typeof.case_90 x_a0, EoCases.__eo_typeof.case_91 x_a0, EoCases.__eo_typeof.case_92 x_a0, EoCases.__eo_typeof.case_93 x_a0, EoCases.__eo_typeof.case_94 x_a0, EoCases.__eo_typeof.case_95 x_a0, EoCases.__eo_typeof.case_96 x_a0, EoCases.__eo_typeof.case_97 x_a0, EoCases.__eo_typeof.case_98 x_a0, EoCases.__eo_typeof.case_99 x_a0, EoCases.__eo_typeof.case_100 x_a0, EoCases.__eo_typeof.case_101 x_a0, EoCases.__eo_typeof.case_102 x_a0, EoCases.__eo_typeof.case_103 x_a0, EoCases.__eo_typeof.case_104 x_a0, EoCases.__eo_typeof.case_105 x_a0, EoCases.__eo_typeof.case_106 x_a0, EoCases.__eo_typeof.case_107 x_a0, EoCases.__eo_typeof.case_108 x_a0, EoCases.__eo_typeof.case_109 x_a0, EoCases.__eo_typeof.case_110 x_a0, EoCases.__eo_typeof.case_111 x_a0, EoCases.__eo_typeof.case_112 x_a0, EoCases.__eo_typeof.case_113 x_a0, EoCases.__eo_typeof.case_114 x_a0, EoCases.__eo_typeof.case_115 x_a0, EoCases.__eo_typeof.case_116 x_a0, EoCases.__eo_typeof.case_117 x_a0, EoCases.__eo_typeof.case_118 x_a0, EoCases.__eo_typeof.case_119 x_a0, EoCases.__eo_typeof.case_120 x_a0, EoCases.__eo_typeof.case_121 x_a0, EoCases.__eo_typeof.case_122 x_a0, EoCases.__eo_typeof.case_123 x_a0, EoCases.__eo_typeof.case_124 x_a0, EoCases.__eo_typeof.case_125 x_a0, EoCases.__eo_typeof.case_126 x_a0, EoCases.__eo_typeof.case_127 x_a0, EoCases.__eo_typeof.case_128 x_a0, EoCases.__eo_typeof.case_129 x_a0, EoCases.__eo_typeof.case_130 x_a0, EoCases.__eo_typeof.case_131 x_a0, EoCases.__eo_typeof.case_132 x_a0, EoCases.__eo_typeof.case_133 x_a0, EoCases.__eo_typeof.case_134 x_a0, EoCases.__eo_typeof.case_135 x_a0, EoCases.__eo_typeof.case_136 x_a0, EoCases.__eo_typeof.case_137 x_a0, EoCases.__eo_typeof.case_138 x_a0, EoCases.__eo_typeof.case_139 x_a0, EoCases.__eo_typeof.case_140 x_a0, EoCases.__eo_typeof.case_141 x_a0, EoCases.__eo_typeof.case_142 x_a0, EoCases.__eo_typeof.case_143 x_a0, EoCases.__eo_typeof.case_144 x_a0, EoCases.__eo_typeof.case_145 x_a0, EoCases.__eo_typeof.case_146 x_a0, EoCases.__eo_typeof.case_147 x_a0, EoCases.__eo_typeof.case_148 x_a0, EoCases.__eo_typeof.case_149 x_a0, EoCases.__eo_typeof.case_150 x_a0, EoCases.__eo_typeof.case_151 x_a0, EoCases.__eo_typeof.case_152 x_a0, EoCases.__eo_typeof.case_153 x_a0, EoCases.__eo_typeof.case_154 x_a0, EoCases.__eo_typeof.case_155 x_a0, EoCases.__eo_typeof.case_156 x_a0, EoCases.__eo_typeof.case_157 x_a0, EoCases.__eo_typeof.case_158 x_a0, EoCases.__eo_typeof.case_159 x_a0, EoCases.__eo_typeof.case_160 x_a0, EoCases.__eo_typeof.case_161 x_a0, EoCases.__eo_typeof.case_162 x_a0, EoCases.__eo_typeof.case_163 x_a0, EoCases.__eo_typeof.case_164 x_a0, EoCases.__eo_typeof.case_165 x_a0, EoCases.__eo_typeof.case_166 x_a0, EoCases.__eo_typeof.case_167 x_a0, EoCases.__eo_typeof.case_168 x_a0, EoCases.__eo_typeof.case_169 x_a0, EoCases.__eo_typeof.case_170 x_a0, EoCases.__eo_typeof.case_171 x_a0, EoCases.__eo_typeof.case_172 x_a0, EoCases.__eo_typeof.case_173 x_a0, EoCases.__eo_typeof.case_174 x_a0, EoCases.__eo_typeof.case_175 x_a0, EoCases.__eo_typeof.case_176 x_a0, EoCases.__eo_typeof.case_177 x_a0, EoCases.__eo_typeof.case_178 x_a0, EoCases.__eo_typeof.case_179 x_a0, EoCases.__eo_typeof.case_180 x_a0, EoCases.__eo_typeof.case_181 x_a0, EoCases.__eo_typeof.case_182 x_a0, EoCases.__eo_typeof.case_183 x_a0, EoCases.__eo_typeof.case_184 x_a0, EoCases.__eo_typeof.case_185 x_a0, EoCases.__eo_typeof.case_186 x_a0, EoCases.__eo_typeof.case_187 x_a0, EoCases.__eo_typeof.case_188 x_a0, EoCases.__eo_typeof.case_189 x_a0, EoCases.__eo_typeof.case_190 x_a0, EoCases.__eo_typeof.case_191 x_a0, EoCases.__eo_typeof.case_192 x_a0, EoCases.__eo_typeof.case_193 x_a0, EoCases.__eo_typeof.case_194 x_a0, EoCases.__eo_typeof.case_195 x_a0, EoCases.__eo_typeof.case_196 x_a0, EoCases.__eo_typeof.case_197 x_a0, EoCases.__eo_typeof.case_198 x_a0, EoCases.__eo_typeof.case_199 x_a0, EoCases.__eo_typeof.case_200 x_a0, EoCases.__eo_typeof.case_201 x_a0, EoCases.__eo_typeof.case_202 x_a0, EoCases.__eo_typeof.case_203 x_a0, EoCases.__eo_typeof.case_204 x_a0, EoCases.__eo_typeof.case_205 x_a0, EoCases.__eo_typeof.case_206 x_a0, EoCases.__eo_typeof.case_207 x_a0] from rfl)
    otherwise ⟨hl_0, hl_1, hl_2, hl_3, hl_4, hl_5, hl_6, hl_7, hl_8, hl_9, hl_10, hl_11, hl_12, hl_13, hl_14, hl_15, hl_16, hl_17, hl_18, hl_19, hl_20, hl_21, hl_22, hl_23, hl_24, hl_25, hl_26, hl_27, hl_28, hl_29, hl_30, hl_31, hl_32, hl_33, hl_34, hl_35, hl_36, hl_37, hl_38, hl_39, hl_40, hl_41, hl_42, hl_43, hl_44, hl_45, hl_46, hl_47, hl_48, hl_49, hl_50, hl_51, hl_52, hl_53, hl_54, hl_55, hl_56, hl_57, hl_58, hl_59, hl_60, hl_61, hl_62, hl_63⟩ using hn_a0
  body_group_step with cases_2_1_eo__24eo_5ftypeof_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_0 x_a0, EoCases.__eo_typeof.case_1 x_a0, EoCases.__eo_typeof.case_2 x_a0, EoCases.__eo_typeof.case_3 x_a0, EoCases.__eo_typeof.case_4 x_a0, EoCases.__eo_typeof.case_5 x_a0, EoCases.__eo_typeof.case_6 x_a0, EoCases.__eo_typeof.case_7 x_a0, EoCases.__eo_typeof.case_8 x_a0, EoCases.__eo_typeof.case_9 x_a0, EoCases.__eo_typeof.case_10 x_a0, EoCases.__eo_typeof.case_11 x_a0, EoCases.__eo_typeof.case_12 x_a0, EoCases.__eo_typeof.case_13 x_a0, EoCases.__eo_typeof.case_14 x_a0, EoCases.__eo_typeof.case_15 x_a0, EoCases.__eo_typeof.case_16 x_a0, EoCases.__eo_typeof.case_17 x_a0, EoCases.__eo_typeof.case_18 x_a0, EoCases.__eo_typeof.case_19 x_a0, EoCases.__eo_typeof.case_20 x_a0, EoCases.__eo_typeof.case_21 x_a0, EoCases.__eo_typeof.case_22 x_a0, EoCases.__eo_typeof.case_23 x_a0, EoCases.__eo_typeof.case_24 x_a0, EoCases.__eo_typeof.case_25 x_a0, EoCases.__eo_typeof.case_26 x_a0, EoCases.__eo_typeof.case_27 x_a0, EoCases.__eo_typeof.case_28 x_a0, EoCases.__eo_typeof.case_29 x_a0, EoCases.__eo_typeof.case_30 x_a0, EoCases.__eo_typeof.case_31 x_a0, EoCases.__eo_typeof.case_32 x_a0, EoCases.__eo_typeof.case_33 x_a0, EoCases.__eo_typeof.case_34 x_a0, EoCases.__eo_typeof.case_35 x_a0, EoCases.__eo_typeof.case_36 x_a0, EoCases.__eo_typeof.case_37 x_a0, EoCases.__eo_typeof.case_38 x_a0, EoCases.__eo_typeof.case_39 x_a0, EoCases.__eo_typeof.case_40 x_a0, EoCases.__eo_typeof.case_41 x_a0, EoCases.__eo_typeof.case_42 x_a0, EoCases.__eo_typeof.case_43 x_a0, EoCases.__eo_typeof.case_44 x_a0, EoCases.__eo_typeof.case_45 x_a0, EoCases.__eo_typeof.case_46 x_a0, EoCases.__eo_typeof.case_47 x_a0, EoCases.__eo_typeof.case_48 x_a0, EoCases.__eo_typeof.case_49 x_a0, EoCases.__eo_typeof.case_50 x_a0, EoCases.__eo_typeof.case_51 x_a0, EoCases.__eo_typeof.case_52 x_a0, EoCases.__eo_typeof.case_53 x_a0, EoCases.__eo_typeof.case_54 x_a0, EoCases.__eo_typeof.case_55 x_a0, EoCases.__eo_typeof.case_56 x_a0, EoCases.__eo_typeof.case_57 x_a0, EoCases.__eo_typeof.case_58 x_a0, EoCases.__eo_typeof.case_59 x_a0, EoCases.__eo_typeof.case_60 x_a0, EoCases.__eo_typeof.case_61 x_a0, EoCases.__eo_typeof.case_62 x_a0, EoCases.__eo_typeof.case_63 x_a0, EoCases.__eo_typeof.case_64 x_a0, EoCases.__eo_typeof.case_65 x_a0, EoCases.__eo_typeof.case_66 x_a0, EoCases.__eo_typeof.case_67 x_a0, EoCases.__eo_typeof.case_68 x_a0, EoCases.__eo_typeof.case_69 x_a0, EoCases.__eo_typeof.case_70 x_a0, EoCases.__eo_typeof.case_71 x_a0, EoCases.__eo_typeof.case_72 x_a0, EoCases.__eo_typeof.case_73 x_a0, EoCases.__eo_typeof.case_74 x_a0, EoCases.__eo_typeof.case_75 x_a0, EoCases.__eo_typeof.case_76 x_a0, EoCases.__eo_typeof.case_77 x_a0, EoCases.__eo_typeof.case_78 x_a0, EoCases.__eo_typeof.case_79 x_a0, EoCases.__eo_typeof.case_80 x_a0, EoCases.__eo_typeof.case_81 x_a0, EoCases.__eo_typeof.case_82 x_a0, EoCases.__eo_typeof.case_83 x_a0, EoCases.__eo_typeof.case_84 x_a0, EoCases.__eo_typeof.case_85 x_a0, EoCases.__eo_typeof.case_86 x_a0, EoCases.__eo_typeof.case_87 x_a0, EoCases.__eo_typeof.case_88 x_a0, EoCases.__eo_typeof.case_89 x_a0, EoCases.__eo_typeof.case_90 x_a0, EoCases.__eo_typeof.case_91 x_a0, EoCases.__eo_typeof.case_92 x_a0, EoCases.__eo_typeof.case_93 x_a0, EoCases.__eo_typeof.case_94 x_a0, EoCases.__eo_typeof.case_95 x_a0, EoCases.__eo_typeof.case_96 x_a0, EoCases.__eo_typeof.case_97 x_a0, EoCases.__eo_typeof.case_98 x_a0, EoCases.__eo_typeof.case_99 x_a0, EoCases.__eo_typeof.case_100 x_a0, EoCases.__eo_typeof.case_101 x_a0, EoCases.__eo_typeof.case_102 x_a0, EoCases.__eo_typeof.case_103 x_a0, EoCases.__eo_typeof.case_104 x_a0, EoCases.__eo_typeof.case_105 x_a0, EoCases.__eo_typeof.case_106 x_a0, EoCases.__eo_typeof.case_107 x_a0, EoCases.__eo_typeof.case_108 x_a0, EoCases.__eo_typeof.case_109 x_a0, EoCases.__eo_typeof.case_110 x_a0, EoCases.__eo_typeof.case_111 x_a0, EoCases.__eo_typeof.case_112 x_a0, EoCases.__eo_typeof.case_113 x_a0, EoCases.__eo_typeof.case_114 x_a0, EoCases.__eo_typeof.case_115 x_a0, EoCases.__eo_typeof.case_116 x_a0, EoCases.__eo_typeof.case_117 x_a0, EoCases.__eo_typeof.case_118 x_a0, EoCases.__eo_typeof.case_119 x_a0, EoCases.__eo_typeof.case_120 x_a0, EoCases.__eo_typeof.case_121 x_a0, EoCases.__eo_typeof.case_122 x_a0, EoCases.__eo_typeof.case_123 x_a0, EoCases.__eo_typeof.case_124 x_a0, EoCases.__eo_typeof.case_125 x_a0, EoCases.__eo_typeof.case_126 x_a0, EoCases.__eo_typeof.case_127 x_a0, EoCases.__eo_typeof.case_128 x_a0, EoCases.__eo_typeof.case_129 x_a0, EoCases.__eo_typeof.case_130 x_a0, EoCases.__eo_typeof.case_131 x_a0, EoCases.__eo_typeof.case_132 x_a0, EoCases.__eo_typeof.case_133 x_a0, EoCases.__eo_typeof.case_134 x_a0, EoCases.__eo_typeof.case_135 x_a0, EoCases.__eo_typeof.case_136 x_a0, EoCases.__eo_typeof.case_137 x_a0, EoCases.__eo_typeof.case_138 x_a0, EoCases.__eo_typeof.case_139 x_a0, EoCases.__eo_typeof.case_140 x_a0, EoCases.__eo_typeof.case_141 x_a0, EoCases.__eo_typeof.case_142 x_a0, EoCases.__eo_typeof.case_143 x_a0, EoCases.__eo_typeof.case_144 x_a0, EoCases.__eo_typeof.case_145 x_a0, EoCases.__eo_typeof.case_146 x_a0, EoCases.__eo_typeof.case_147 x_a0, EoCases.__eo_typeof.case_148 x_a0, EoCases.__eo_typeof.case_149 x_a0, EoCases.__eo_typeof.case_150 x_a0, EoCases.__eo_typeof.case_151 x_a0, EoCases.__eo_typeof.case_152 x_a0, EoCases.__eo_typeof.case_153 x_a0, EoCases.__eo_typeof.case_154 x_a0, EoCases.__eo_typeof.case_155 x_a0, EoCases.__eo_typeof.case_156 x_a0, EoCases.__eo_typeof.case_157 x_a0, EoCases.__eo_typeof.case_158 x_a0, EoCases.__eo_typeof.case_159 x_a0, EoCases.__eo_typeof.case_160 x_a0, EoCases.__eo_typeof.case_161 x_a0, EoCases.__eo_typeof.case_162 x_a0, EoCases.__eo_typeof.case_163 x_a0, EoCases.__eo_typeof.case_164 x_a0, EoCases.__eo_typeof.case_165 x_a0, EoCases.__eo_typeof.case_166 x_a0, EoCases.__eo_typeof.case_167 x_a0, EoCases.__eo_typeof.case_168 x_a0, EoCases.__eo_typeof.case_169 x_a0, EoCases.__eo_typeof.case_170 x_a0, EoCases.__eo_typeof.case_171 x_a0, EoCases.__eo_typeof.case_172 x_a0, EoCases.__eo_typeof.case_173 x_a0, EoCases.__eo_typeof.case_174 x_a0, EoCases.__eo_typeof.case_175 x_a0, EoCases.__eo_typeof.case_176 x_a0, EoCases.__eo_typeof.case_177 x_a0, EoCases.__eo_typeof.case_178 x_a0, EoCases.__eo_typeof.case_179 x_a0, EoCases.__eo_typeof.case_180 x_a0, EoCases.__eo_typeof.case_181 x_a0, EoCases.__eo_typeof.case_182 x_a0, EoCases.__eo_typeof.case_183 x_a0, EoCases.__eo_typeof.case_184 x_a0, EoCases.__eo_typeof.case_185 x_a0, EoCases.__eo_typeof.case_186 x_a0, EoCases.__eo_typeof.case_187 x_a0, EoCases.__eo_typeof.case_188 x_a0, EoCases.__eo_typeof.case_189 x_a0, EoCases.__eo_typeof.case_190 x_a0, EoCases.__eo_typeof.case_191 x_a0, EoCases.__eo_typeof.case_192 x_a0, EoCases.__eo_typeof.case_193 x_a0, EoCases.__eo_typeof.case_194 x_a0, EoCases.__eo_typeof.case_195 x_a0, EoCases.__eo_typeof.case_196 x_a0, EoCases.__eo_typeof.case_197 x_a0, EoCases.__eo_typeof.case_198 x_a0, EoCases.__eo_typeof.case_199 x_a0, EoCases.__eo_typeof.case_200 x_a0, EoCases.__eo_typeof.case_201 x_a0, EoCases.__eo_typeof.case_202 x_a0, EoCases.__eo_typeof.case_203 x_a0, EoCases.__eo_typeof.case_204 x_a0, EoCases.__eo_typeof.case_205 x_a0, EoCases.__eo_typeof.case_206 x_a0, EoCases.__eo_typeof.case_207 x_a0] = [EoCases.__eo_typeof.case_0 x_a0, EoCases.__eo_typeof.case_1 x_a0, EoCases.__eo_typeof.case_2 x_a0, EoCases.__eo_typeof.case_3 x_a0, EoCases.__eo_typeof.case_4 x_a0, EoCases.__eo_typeof.case_5 x_a0, EoCases.__eo_typeof.case_6 x_a0, EoCases.__eo_typeof.case_7 x_a0, EoCases.__eo_typeof.case_8 x_a0, EoCases.__eo_typeof.case_9 x_a0, EoCases.__eo_typeof.case_10 x_a0, EoCases.__eo_typeof.case_11 x_a0, EoCases.__eo_typeof.case_12 x_a0, EoCases.__eo_typeof.case_13 x_a0, EoCases.__eo_typeof.case_14 x_a0, EoCases.__eo_typeof.case_15 x_a0, EoCases.__eo_typeof.case_16 x_a0, EoCases.__eo_typeof.case_17 x_a0, EoCases.__eo_typeof.case_18 x_a0, EoCases.__eo_typeof.case_19 x_a0, EoCases.__eo_typeof.case_20 x_a0, EoCases.__eo_typeof.case_21 x_a0, EoCases.__eo_typeof.case_22 x_a0, EoCases.__eo_typeof.case_23 x_a0, EoCases.__eo_typeof.case_24 x_a0, EoCases.__eo_typeof.case_25 x_a0, EoCases.__eo_typeof.case_26 x_a0, EoCases.__eo_typeof.case_27 x_a0, EoCases.__eo_typeof.case_28 x_a0, EoCases.__eo_typeof.case_29 x_a0, EoCases.__eo_typeof.case_30 x_a0, EoCases.__eo_typeof.case_31 x_a0, EoCases.__eo_typeof.case_32 x_a0, EoCases.__eo_typeof.case_33 x_a0, EoCases.__eo_typeof.case_34 x_a0, EoCases.__eo_typeof.case_35 x_a0, EoCases.__eo_typeof.case_36 x_a0, EoCases.__eo_typeof.case_37 x_a0, EoCases.__eo_typeof.case_38 x_a0, EoCases.__eo_typeof.case_39 x_a0, EoCases.__eo_typeof.case_40 x_a0, EoCases.__eo_typeof.case_41 x_a0, EoCases.__eo_typeof.case_42 x_a0, EoCases.__eo_typeof.case_43 x_a0, EoCases.__eo_typeof.case_44 x_a0, EoCases.__eo_typeof.case_45 x_a0, EoCases.__eo_typeof.case_46 x_a0, EoCases.__eo_typeof.case_47 x_a0, EoCases.__eo_typeof.case_48 x_a0, EoCases.__eo_typeof.case_49 x_a0, EoCases.__eo_typeof.case_50 x_a0, EoCases.__eo_typeof.case_51 x_a0, EoCases.__eo_typeof.case_52 x_a0, EoCases.__eo_typeof.case_53 x_a0, EoCases.__eo_typeof.case_54 x_a0, EoCases.__eo_typeof.case_55 x_a0, EoCases.__eo_typeof.case_56 x_a0, EoCases.__eo_typeof.case_57 x_a0, EoCases.__eo_typeof.case_58 x_a0, EoCases.__eo_typeof.case_59 x_a0, EoCases.__eo_typeof.case_60 x_a0, EoCases.__eo_typeof.case_61 x_a0, EoCases.__eo_typeof.case_62 x_a0, EoCases.__eo_typeof.case_63 x_a0] ++ [EoCases.__eo_typeof.case_64 x_a0, EoCases.__eo_typeof.case_65 x_a0, EoCases.__eo_typeof.case_66 x_a0, EoCases.__eo_typeof.case_67 x_a0, EoCases.__eo_typeof.case_68 x_a0, EoCases.__eo_typeof.case_69 x_a0, EoCases.__eo_typeof.case_70 x_a0, EoCases.__eo_typeof.case_71 x_a0, EoCases.__eo_typeof.case_72 x_a0, EoCases.__eo_typeof.case_73 x_a0, EoCases.__eo_typeof.case_74 x_a0, EoCases.__eo_typeof.case_75 x_a0, EoCases.__eo_typeof.case_76 x_a0, EoCases.__eo_typeof.case_77 x_a0, EoCases.__eo_typeof.case_78 x_a0, EoCases.__eo_typeof.case_79 x_a0, EoCases.__eo_typeof.case_80 x_a0, EoCases.__eo_typeof.case_81 x_a0, EoCases.__eo_typeof.case_82 x_a0, EoCases.__eo_typeof.case_83 x_a0, EoCases.__eo_typeof.case_84 x_a0, EoCases.__eo_typeof.case_85 x_a0, EoCases.__eo_typeof.case_86 x_a0, EoCases.__eo_typeof.case_87 x_a0, EoCases.__eo_typeof.case_88 x_a0, EoCases.__eo_typeof.case_89 x_a0, EoCases.__eo_typeof.case_90 x_a0, EoCases.__eo_typeof.case_91 x_a0, EoCases.__eo_typeof.case_92 x_a0, EoCases.__eo_typeof.case_93 x_a0, EoCases.__eo_typeof.case_94 x_a0, EoCases.__eo_typeof.case_95 x_a0, EoCases.__eo_typeof.case_96 x_a0, EoCases.__eo_typeof.case_97 x_a0, EoCases.__eo_typeof.case_98 x_a0, EoCases.__eo_typeof.case_99 x_a0, EoCases.__eo_typeof.case_100 x_a0, EoCases.__eo_typeof.case_101 x_a0, EoCases.__eo_typeof.case_102 x_a0, EoCases.__eo_typeof.case_103 x_a0, EoCases.__eo_typeof.case_104 x_a0, EoCases.__eo_typeof.case_105 x_a0, EoCases.__eo_typeof.case_106 x_a0, EoCases.__eo_typeof.case_107 x_a0, EoCases.__eo_typeof.case_108 x_a0, EoCases.__eo_typeof.case_109 x_a0, EoCases.__eo_typeof.case_110 x_a0, EoCases.__eo_typeof.case_111 x_a0, EoCases.__eo_typeof.case_112 x_a0, EoCases.__eo_typeof.case_113 x_a0, EoCases.__eo_typeof.case_114 x_a0, EoCases.__eo_typeof.case_115 x_a0, EoCases.__eo_typeof.case_116 x_a0, EoCases.__eo_typeof.case_117 x_a0, EoCases.__eo_typeof.case_118 x_a0, EoCases.__eo_typeof.case_119 x_a0, EoCases.__eo_typeof.case_120 x_a0, EoCases.__eo_typeof.case_121 x_a0, EoCases.__eo_typeof.case_122 x_a0, EoCases.__eo_typeof.case_123 x_a0, EoCases.__eo_typeof.case_124 x_a0, EoCases.__eo_typeof.case_125 x_a0, EoCases.__eo_typeof.case_126 x_a0, EoCases.__eo_typeof.case_127 x_a0] ++ [EoCases.__eo_typeof.case_128 x_a0, EoCases.__eo_typeof.case_129 x_a0, EoCases.__eo_typeof.case_130 x_a0, EoCases.__eo_typeof.case_131 x_a0, EoCases.__eo_typeof.case_132 x_a0, EoCases.__eo_typeof.case_133 x_a0, EoCases.__eo_typeof.case_134 x_a0, EoCases.__eo_typeof.case_135 x_a0, EoCases.__eo_typeof.case_136 x_a0, EoCases.__eo_typeof.case_137 x_a0, EoCases.__eo_typeof.case_138 x_a0, EoCases.__eo_typeof.case_139 x_a0, EoCases.__eo_typeof.case_140 x_a0, EoCases.__eo_typeof.case_141 x_a0, EoCases.__eo_typeof.case_142 x_a0, EoCases.__eo_typeof.case_143 x_a0, EoCases.__eo_typeof.case_144 x_a0, EoCases.__eo_typeof.case_145 x_a0, EoCases.__eo_typeof.case_146 x_a0, EoCases.__eo_typeof.case_147 x_a0, EoCases.__eo_typeof.case_148 x_a0, EoCases.__eo_typeof.case_149 x_a0, EoCases.__eo_typeof.case_150 x_a0, EoCases.__eo_typeof.case_151 x_a0, EoCases.__eo_typeof.case_152 x_a0, EoCases.__eo_typeof.case_153 x_a0, EoCases.__eo_typeof.case_154 x_a0, EoCases.__eo_typeof.case_155 x_a0, EoCases.__eo_typeof.case_156 x_a0, EoCases.__eo_typeof.case_157 x_a0, EoCases.__eo_typeof.case_158 x_a0, EoCases.__eo_typeof.case_159 x_a0, EoCases.__eo_typeof.case_160 x_a0, EoCases.__eo_typeof.case_161 x_a0, EoCases.__eo_typeof.case_162 x_a0, EoCases.__eo_typeof.case_163 x_a0, EoCases.__eo_typeof.case_164 x_a0, EoCases.__eo_typeof.case_165 x_a0, EoCases.__eo_typeof.case_166 x_a0, EoCases.__eo_typeof.case_167 x_a0, EoCases.__eo_typeof.case_168 x_a0, EoCases.__eo_typeof.case_169 x_a0, EoCases.__eo_typeof.case_170 x_a0, EoCases.__eo_typeof.case_171 x_a0, EoCases.__eo_typeof.case_172 x_a0, EoCases.__eo_typeof.case_173 x_a0, EoCases.__eo_typeof.case_174 x_a0, EoCases.__eo_typeof.case_175 x_a0, EoCases.__eo_typeof.case_176 x_a0, EoCases.__eo_typeof.case_177 x_a0, EoCases.__eo_typeof.case_178 x_a0, EoCases.__eo_typeof.case_179 x_a0, EoCases.__eo_typeof.case_180 x_a0, EoCases.__eo_typeof.case_181 x_a0, EoCases.__eo_typeof.case_182 x_a0, EoCases.__eo_typeof.case_183 x_a0, EoCases.__eo_typeof.case_184 x_a0, EoCases.__eo_typeof.case_185 x_a0, EoCases.__eo_typeof.case_186 x_a0, EoCases.__eo_typeof.case_187 x_a0, EoCases.__eo_typeof.case_188 x_a0, EoCases.__eo_typeof.case_189 x_a0, EoCases.__eo_typeof.case_190 x_a0, EoCases.__eo_typeof.case_191 x_a0, EoCases.__eo_typeof.case_192 x_a0, EoCases.__eo_typeof.case_193 x_a0, EoCases.__eo_typeof.case_194 x_a0, EoCases.__eo_typeof.case_195 x_a0, EoCases.__eo_typeof.case_196 x_a0, EoCases.__eo_typeof.case_197 x_a0, EoCases.__eo_typeof.case_198 x_a0, EoCases.__eo_typeof.case_199 x_a0, EoCases.__eo_typeof.case_200 x_a0, EoCases.__eo_typeof.case_201 x_a0, EoCases.__eo_typeof.case_202 x_a0, EoCases.__eo_typeof.case_203 x_a0, EoCases.__eo_typeof.case_204 x_a0, EoCases.__eo_typeof.case_205 x_a0, EoCases.__eo_typeof.case_206 x_a0, EoCases.__eo_typeof.case_207 x_a0] from rfl)
    otherwise ⟨hl_64, hl_65, hl_66, hl_67, hl_68, hl_69, hl_70, hl_71, hl_72, hl_73, hl_74, hl_75, hl_76, hl_77, hl_78, hl_79, hl_80, hl_81, hl_82, hl_83, hl_84, hl_85, hl_86, hl_87, hl_88, hl_89, hl_90, hl_91, hl_92, hl_93, hl_94, hl_95, hl_96, hl_97, hl_98, hl_99, hl_100, hl_101, hl_102, hl_103, hl_104, hl_105, hl_106, hl_107, hl_108, hl_109, hl_110, hl_111, hl_112, hl_113, hl_114, hl_115, hl_116, hl_117, hl_118, hl_119, hl_120, hl_121, hl_122, hl_123, hl_124, hl_125, hl_126, hl_127⟩ using hn_a0 hl_0 hl_1 hl_2 hl_3 hl_4 hl_5 hl_6 hl_7 hl_8 hl_9 hl_10 hl_11 hl_12 hl_13 hl_14 hl_15 hl_16 hl_17 hl_18 hl_19 hl_20 hl_21 hl_22 hl_23 hl_24 hl_25 hl_26 hl_27 hl_28 hl_29 hl_30 hl_31 hl_32 hl_33 hl_34 hl_35 hl_36 hl_37 hl_38 hl_39 hl_40 hl_41 hl_42 hl_43 hl_44 hl_45 hl_46 hl_47 hl_48 hl_49 hl_50 hl_51 hl_52 hl_53 hl_54 hl_55 hl_56 hl_57 hl_58 hl_59 hl_60 hl_61 hl_62 hl_63
  body_group_step with cases_2_2_eo__24eo_5ftypeof_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_0 x_a0, EoCases.__eo_typeof.case_1 x_a0, EoCases.__eo_typeof.case_2 x_a0, EoCases.__eo_typeof.case_3 x_a0, EoCases.__eo_typeof.case_4 x_a0, EoCases.__eo_typeof.case_5 x_a0, EoCases.__eo_typeof.case_6 x_a0, EoCases.__eo_typeof.case_7 x_a0, EoCases.__eo_typeof.case_8 x_a0, EoCases.__eo_typeof.case_9 x_a0, EoCases.__eo_typeof.case_10 x_a0, EoCases.__eo_typeof.case_11 x_a0, EoCases.__eo_typeof.case_12 x_a0, EoCases.__eo_typeof.case_13 x_a0, EoCases.__eo_typeof.case_14 x_a0, EoCases.__eo_typeof.case_15 x_a0, EoCases.__eo_typeof.case_16 x_a0, EoCases.__eo_typeof.case_17 x_a0, EoCases.__eo_typeof.case_18 x_a0, EoCases.__eo_typeof.case_19 x_a0, EoCases.__eo_typeof.case_20 x_a0, EoCases.__eo_typeof.case_21 x_a0, EoCases.__eo_typeof.case_22 x_a0, EoCases.__eo_typeof.case_23 x_a0, EoCases.__eo_typeof.case_24 x_a0, EoCases.__eo_typeof.case_25 x_a0, EoCases.__eo_typeof.case_26 x_a0, EoCases.__eo_typeof.case_27 x_a0, EoCases.__eo_typeof.case_28 x_a0, EoCases.__eo_typeof.case_29 x_a0, EoCases.__eo_typeof.case_30 x_a0, EoCases.__eo_typeof.case_31 x_a0, EoCases.__eo_typeof.case_32 x_a0, EoCases.__eo_typeof.case_33 x_a0, EoCases.__eo_typeof.case_34 x_a0, EoCases.__eo_typeof.case_35 x_a0, EoCases.__eo_typeof.case_36 x_a0, EoCases.__eo_typeof.case_37 x_a0, EoCases.__eo_typeof.case_38 x_a0, EoCases.__eo_typeof.case_39 x_a0, EoCases.__eo_typeof.case_40 x_a0, EoCases.__eo_typeof.case_41 x_a0, EoCases.__eo_typeof.case_42 x_a0, EoCases.__eo_typeof.case_43 x_a0, EoCases.__eo_typeof.case_44 x_a0, EoCases.__eo_typeof.case_45 x_a0, EoCases.__eo_typeof.case_46 x_a0, EoCases.__eo_typeof.case_47 x_a0, EoCases.__eo_typeof.case_48 x_a0, EoCases.__eo_typeof.case_49 x_a0, EoCases.__eo_typeof.case_50 x_a0, EoCases.__eo_typeof.case_51 x_a0, EoCases.__eo_typeof.case_52 x_a0, EoCases.__eo_typeof.case_53 x_a0, EoCases.__eo_typeof.case_54 x_a0, EoCases.__eo_typeof.case_55 x_a0, EoCases.__eo_typeof.case_56 x_a0, EoCases.__eo_typeof.case_57 x_a0, EoCases.__eo_typeof.case_58 x_a0, EoCases.__eo_typeof.case_59 x_a0, EoCases.__eo_typeof.case_60 x_a0, EoCases.__eo_typeof.case_61 x_a0, EoCases.__eo_typeof.case_62 x_a0, EoCases.__eo_typeof.case_63 x_a0, EoCases.__eo_typeof.case_64 x_a0, EoCases.__eo_typeof.case_65 x_a0, EoCases.__eo_typeof.case_66 x_a0, EoCases.__eo_typeof.case_67 x_a0, EoCases.__eo_typeof.case_68 x_a0, EoCases.__eo_typeof.case_69 x_a0, EoCases.__eo_typeof.case_70 x_a0, EoCases.__eo_typeof.case_71 x_a0, EoCases.__eo_typeof.case_72 x_a0, EoCases.__eo_typeof.case_73 x_a0, EoCases.__eo_typeof.case_74 x_a0, EoCases.__eo_typeof.case_75 x_a0, EoCases.__eo_typeof.case_76 x_a0, EoCases.__eo_typeof.case_77 x_a0, EoCases.__eo_typeof.case_78 x_a0, EoCases.__eo_typeof.case_79 x_a0, EoCases.__eo_typeof.case_80 x_a0, EoCases.__eo_typeof.case_81 x_a0, EoCases.__eo_typeof.case_82 x_a0, EoCases.__eo_typeof.case_83 x_a0, EoCases.__eo_typeof.case_84 x_a0, EoCases.__eo_typeof.case_85 x_a0, EoCases.__eo_typeof.case_86 x_a0, EoCases.__eo_typeof.case_87 x_a0, EoCases.__eo_typeof.case_88 x_a0, EoCases.__eo_typeof.case_89 x_a0, EoCases.__eo_typeof.case_90 x_a0, EoCases.__eo_typeof.case_91 x_a0, EoCases.__eo_typeof.case_92 x_a0, EoCases.__eo_typeof.case_93 x_a0, EoCases.__eo_typeof.case_94 x_a0, EoCases.__eo_typeof.case_95 x_a0, EoCases.__eo_typeof.case_96 x_a0, EoCases.__eo_typeof.case_97 x_a0, EoCases.__eo_typeof.case_98 x_a0, EoCases.__eo_typeof.case_99 x_a0, EoCases.__eo_typeof.case_100 x_a0, EoCases.__eo_typeof.case_101 x_a0, EoCases.__eo_typeof.case_102 x_a0, EoCases.__eo_typeof.case_103 x_a0, EoCases.__eo_typeof.case_104 x_a0, EoCases.__eo_typeof.case_105 x_a0, EoCases.__eo_typeof.case_106 x_a0, EoCases.__eo_typeof.case_107 x_a0, EoCases.__eo_typeof.case_108 x_a0, EoCases.__eo_typeof.case_109 x_a0, EoCases.__eo_typeof.case_110 x_a0, EoCases.__eo_typeof.case_111 x_a0, EoCases.__eo_typeof.case_112 x_a0, EoCases.__eo_typeof.case_113 x_a0, EoCases.__eo_typeof.case_114 x_a0, EoCases.__eo_typeof.case_115 x_a0, EoCases.__eo_typeof.case_116 x_a0, EoCases.__eo_typeof.case_117 x_a0, EoCases.__eo_typeof.case_118 x_a0, EoCases.__eo_typeof.case_119 x_a0, EoCases.__eo_typeof.case_120 x_a0, EoCases.__eo_typeof.case_121 x_a0, EoCases.__eo_typeof.case_122 x_a0, EoCases.__eo_typeof.case_123 x_a0, EoCases.__eo_typeof.case_124 x_a0, EoCases.__eo_typeof.case_125 x_a0, EoCases.__eo_typeof.case_126 x_a0, EoCases.__eo_typeof.case_127 x_a0, EoCases.__eo_typeof.case_128 x_a0, EoCases.__eo_typeof.case_129 x_a0, EoCases.__eo_typeof.case_130 x_a0, EoCases.__eo_typeof.case_131 x_a0, EoCases.__eo_typeof.case_132 x_a0, EoCases.__eo_typeof.case_133 x_a0, EoCases.__eo_typeof.case_134 x_a0, EoCases.__eo_typeof.case_135 x_a0, EoCases.__eo_typeof.case_136 x_a0, EoCases.__eo_typeof.case_137 x_a0, EoCases.__eo_typeof.case_138 x_a0, EoCases.__eo_typeof.case_139 x_a0, EoCases.__eo_typeof.case_140 x_a0, EoCases.__eo_typeof.case_141 x_a0, EoCases.__eo_typeof.case_142 x_a0, EoCases.__eo_typeof.case_143 x_a0, EoCases.__eo_typeof.case_144 x_a0, EoCases.__eo_typeof.case_145 x_a0, EoCases.__eo_typeof.case_146 x_a0, EoCases.__eo_typeof.case_147 x_a0, EoCases.__eo_typeof.case_148 x_a0, EoCases.__eo_typeof.case_149 x_a0, EoCases.__eo_typeof.case_150 x_a0, EoCases.__eo_typeof.case_151 x_a0, EoCases.__eo_typeof.case_152 x_a0, EoCases.__eo_typeof.case_153 x_a0, EoCases.__eo_typeof.case_154 x_a0, EoCases.__eo_typeof.case_155 x_a0, EoCases.__eo_typeof.case_156 x_a0, EoCases.__eo_typeof.case_157 x_a0, EoCases.__eo_typeof.case_158 x_a0, EoCases.__eo_typeof.case_159 x_a0, EoCases.__eo_typeof.case_160 x_a0, EoCases.__eo_typeof.case_161 x_a0, EoCases.__eo_typeof.case_162 x_a0, EoCases.__eo_typeof.case_163 x_a0, EoCases.__eo_typeof.case_164 x_a0, EoCases.__eo_typeof.case_165 x_a0, EoCases.__eo_typeof.case_166 x_a0, EoCases.__eo_typeof.case_167 x_a0, EoCases.__eo_typeof.case_168 x_a0, EoCases.__eo_typeof.case_169 x_a0, EoCases.__eo_typeof.case_170 x_a0, EoCases.__eo_typeof.case_171 x_a0, EoCases.__eo_typeof.case_172 x_a0, EoCases.__eo_typeof.case_173 x_a0, EoCases.__eo_typeof.case_174 x_a0, EoCases.__eo_typeof.case_175 x_a0, EoCases.__eo_typeof.case_176 x_a0, EoCases.__eo_typeof.case_177 x_a0, EoCases.__eo_typeof.case_178 x_a0, EoCases.__eo_typeof.case_179 x_a0, EoCases.__eo_typeof.case_180 x_a0, EoCases.__eo_typeof.case_181 x_a0, EoCases.__eo_typeof.case_182 x_a0, EoCases.__eo_typeof.case_183 x_a0, EoCases.__eo_typeof.case_184 x_a0, EoCases.__eo_typeof.case_185 x_a0, EoCases.__eo_typeof.case_186 x_a0, EoCases.__eo_typeof.case_187 x_a0, EoCases.__eo_typeof.case_188 x_a0, EoCases.__eo_typeof.case_189 x_a0, EoCases.__eo_typeof.case_190 x_a0, EoCases.__eo_typeof.case_191 x_a0, EoCases.__eo_typeof.case_192 x_a0, EoCases.__eo_typeof.case_193 x_a0, EoCases.__eo_typeof.case_194 x_a0, EoCases.__eo_typeof.case_195 x_a0, EoCases.__eo_typeof.case_196 x_a0, EoCases.__eo_typeof.case_197 x_a0, EoCases.__eo_typeof.case_198 x_a0, EoCases.__eo_typeof.case_199 x_a0, EoCases.__eo_typeof.case_200 x_a0, EoCases.__eo_typeof.case_201 x_a0, EoCases.__eo_typeof.case_202 x_a0, EoCases.__eo_typeof.case_203 x_a0, EoCases.__eo_typeof.case_204 x_a0, EoCases.__eo_typeof.case_205 x_a0, EoCases.__eo_typeof.case_206 x_a0, EoCases.__eo_typeof.case_207 x_a0] = [EoCases.__eo_typeof.case_0 x_a0, EoCases.__eo_typeof.case_1 x_a0, EoCases.__eo_typeof.case_2 x_a0, EoCases.__eo_typeof.case_3 x_a0, EoCases.__eo_typeof.case_4 x_a0, EoCases.__eo_typeof.case_5 x_a0, EoCases.__eo_typeof.case_6 x_a0, EoCases.__eo_typeof.case_7 x_a0, EoCases.__eo_typeof.case_8 x_a0, EoCases.__eo_typeof.case_9 x_a0, EoCases.__eo_typeof.case_10 x_a0, EoCases.__eo_typeof.case_11 x_a0, EoCases.__eo_typeof.case_12 x_a0, EoCases.__eo_typeof.case_13 x_a0, EoCases.__eo_typeof.case_14 x_a0, EoCases.__eo_typeof.case_15 x_a0, EoCases.__eo_typeof.case_16 x_a0, EoCases.__eo_typeof.case_17 x_a0, EoCases.__eo_typeof.case_18 x_a0, EoCases.__eo_typeof.case_19 x_a0, EoCases.__eo_typeof.case_20 x_a0, EoCases.__eo_typeof.case_21 x_a0, EoCases.__eo_typeof.case_22 x_a0, EoCases.__eo_typeof.case_23 x_a0, EoCases.__eo_typeof.case_24 x_a0, EoCases.__eo_typeof.case_25 x_a0, EoCases.__eo_typeof.case_26 x_a0, EoCases.__eo_typeof.case_27 x_a0, EoCases.__eo_typeof.case_28 x_a0, EoCases.__eo_typeof.case_29 x_a0, EoCases.__eo_typeof.case_30 x_a0, EoCases.__eo_typeof.case_31 x_a0, EoCases.__eo_typeof.case_32 x_a0, EoCases.__eo_typeof.case_33 x_a0, EoCases.__eo_typeof.case_34 x_a0, EoCases.__eo_typeof.case_35 x_a0, EoCases.__eo_typeof.case_36 x_a0, EoCases.__eo_typeof.case_37 x_a0, EoCases.__eo_typeof.case_38 x_a0, EoCases.__eo_typeof.case_39 x_a0, EoCases.__eo_typeof.case_40 x_a0, EoCases.__eo_typeof.case_41 x_a0, EoCases.__eo_typeof.case_42 x_a0, EoCases.__eo_typeof.case_43 x_a0, EoCases.__eo_typeof.case_44 x_a0, EoCases.__eo_typeof.case_45 x_a0, EoCases.__eo_typeof.case_46 x_a0, EoCases.__eo_typeof.case_47 x_a0, EoCases.__eo_typeof.case_48 x_a0, EoCases.__eo_typeof.case_49 x_a0, EoCases.__eo_typeof.case_50 x_a0, EoCases.__eo_typeof.case_51 x_a0, EoCases.__eo_typeof.case_52 x_a0, EoCases.__eo_typeof.case_53 x_a0, EoCases.__eo_typeof.case_54 x_a0, EoCases.__eo_typeof.case_55 x_a0, EoCases.__eo_typeof.case_56 x_a0, EoCases.__eo_typeof.case_57 x_a0, EoCases.__eo_typeof.case_58 x_a0, EoCases.__eo_typeof.case_59 x_a0, EoCases.__eo_typeof.case_60 x_a0, EoCases.__eo_typeof.case_61 x_a0, EoCases.__eo_typeof.case_62 x_a0, EoCases.__eo_typeof.case_63 x_a0, EoCases.__eo_typeof.case_64 x_a0, EoCases.__eo_typeof.case_65 x_a0, EoCases.__eo_typeof.case_66 x_a0, EoCases.__eo_typeof.case_67 x_a0, EoCases.__eo_typeof.case_68 x_a0, EoCases.__eo_typeof.case_69 x_a0, EoCases.__eo_typeof.case_70 x_a0, EoCases.__eo_typeof.case_71 x_a0, EoCases.__eo_typeof.case_72 x_a0, EoCases.__eo_typeof.case_73 x_a0, EoCases.__eo_typeof.case_74 x_a0, EoCases.__eo_typeof.case_75 x_a0, EoCases.__eo_typeof.case_76 x_a0, EoCases.__eo_typeof.case_77 x_a0, EoCases.__eo_typeof.case_78 x_a0, EoCases.__eo_typeof.case_79 x_a0, EoCases.__eo_typeof.case_80 x_a0, EoCases.__eo_typeof.case_81 x_a0, EoCases.__eo_typeof.case_82 x_a0, EoCases.__eo_typeof.case_83 x_a0, EoCases.__eo_typeof.case_84 x_a0, EoCases.__eo_typeof.case_85 x_a0, EoCases.__eo_typeof.case_86 x_a0, EoCases.__eo_typeof.case_87 x_a0, EoCases.__eo_typeof.case_88 x_a0, EoCases.__eo_typeof.case_89 x_a0, EoCases.__eo_typeof.case_90 x_a0, EoCases.__eo_typeof.case_91 x_a0, EoCases.__eo_typeof.case_92 x_a0, EoCases.__eo_typeof.case_93 x_a0, EoCases.__eo_typeof.case_94 x_a0, EoCases.__eo_typeof.case_95 x_a0, EoCases.__eo_typeof.case_96 x_a0, EoCases.__eo_typeof.case_97 x_a0, EoCases.__eo_typeof.case_98 x_a0, EoCases.__eo_typeof.case_99 x_a0, EoCases.__eo_typeof.case_100 x_a0, EoCases.__eo_typeof.case_101 x_a0, EoCases.__eo_typeof.case_102 x_a0, EoCases.__eo_typeof.case_103 x_a0, EoCases.__eo_typeof.case_104 x_a0, EoCases.__eo_typeof.case_105 x_a0, EoCases.__eo_typeof.case_106 x_a0, EoCases.__eo_typeof.case_107 x_a0, EoCases.__eo_typeof.case_108 x_a0, EoCases.__eo_typeof.case_109 x_a0, EoCases.__eo_typeof.case_110 x_a0, EoCases.__eo_typeof.case_111 x_a0, EoCases.__eo_typeof.case_112 x_a0, EoCases.__eo_typeof.case_113 x_a0, EoCases.__eo_typeof.case_114 x_a0, EoCases.__eo_typeof.case_115 x_a0, EoCases.__eo_typeof.case_116 x_a0, EoCases.__eo_typeof.case_117 x_a0, EoCases.__eo_typeof.case_118 x_a0, EoCases.__eo_typeof.case_119 x_a0, EoCases.__eo_typeof.case_120 x_a0, EoCases.__eo_typeof.case_121 x_a0, EoCases.__eo_typeof.case_122 x_a0, EoCases.__eo_typeof.case_123 x_a0, EoCases.__eo_typeof.case_124 x_a0, EoCases.__eo_typeof.case_125 x_a0, EoCases.__eo_typeof.case_126 x_a0, EoCases.__eo_typeof.case_127 x_a0] ++ [EoCases.__eo_typeof.case_128 x_a0, EoCases.__eo_typeof.case_129 x_a0, EoCases.__eo_typeof.case_130 x_a0, EoCases.__eo_typeof.case_131 x_a0, EoCases.__eo_typeof.case_132 x_a0, EoCases.__eo_typeof.case_133 x_a0, EoCases.__eo_typeof.case_134 x_a0, EoCases.__eo_typeof.case_135 x_a0, EoCases.__eo_typeof.case_136 x_a0, EoCases.__eo_typeof.case_137 x_a0, EoCases.__eo_typeof.case_138 x_a0, EoCases.__eo_typeof.case_139 x_a0, EoCases.__eo_typeof.case_140 x_a0, EoCases.__eo_typeof.case_141 x_a0, EoCases.__eo_typeof.case_142 x_a0, EoCases.__eo_typeof.case_143 x_a0, EoCases.__eo_typeof.case_144 x_a0, EoCases.__eo_typeof.case_145 x_a0, EoCases.__eo_typeof.case_146 x_a0, EoCases.__eo_typeof.case_147 x_a0, EoCases.__eo_typeof.case_148 x_a0, EoCases.__eo_typeof.case_149 x_a0, EoCases.__eo_typeof.case_150 x_a0, EoCases.__eo_typeof.case_151 x_a0, EoCases.__eo_typeof.case_152 x_a0, EoCases.__eo_typeof.case_153 x_a0, EoCases.__eo_typeof.case_154 x_a0, EoCases.__eo_typeof.case_155 x_a0, EoCases.__eo_typeof.case_156 x_a0, EoCases.__eo_typeof.case_157 x_a0, EoCases.__eo_typeof.case_158 x_a0, EoCases.__eo_typeof.case_159 x_a0, EoCases.__eo_typeof.case_160 x_a0, EoCases.__eo_typeof.case_161 x_a0, EoCases.__eo_typeof.case_162 x_a0, EoCases.__eo_typeof.case_163 x_a0, EoCases.__eo_typeof.case_164 x_a0, EoCases.__eo_typeof.case_165 x_a0, EoCases.__eo_typeof.case_166 x_a0, EoCases.__eo_typeof.case_167 x_a0, EoCases.__eo_typeof.case_168 x_a0, EoCases.__eo_typeof.case_169 x_a0, EoCases.__eo_typeof.case_170 x_a0, EoCases.__eo_typeof.case_171 x_a0, EoCases.__eo_typeof.case_172 x_a0, EoCases.__eo_typeof.case_173 x_a0, EoCases.__eo_typeof.case_174 x_a0, EoCases.__eo_typeof.case_175 x_a0, EoCases.__eo_typeof.case_176 x_a0, EoCases.__eo_typeof.case_177 x_a0, EoCases.__eo_typeof.case_178 x_a0, EoCases.__eo_typeof.case_179 x_a0, EoCases.__eo_typeof.case_180 x_a0, EoCases.__eo_typeof.case_181 x_a0, EoCases.__eo_typeof.case_182 x_a0, EoCases.__eo_typeof.case_183 x_a0, EoCases.__eo_typeof.case_184 x_a0, EoCases.__eo_typeof.case_185 x_a0, EoCases.__eo_typeof.case_186 x_a0, EoCases.__eo_typeof.case_187 x_a0, EoCases.__eo_typeof.case_188 x_a0, EoCases.__eo_typeof.case_189 x_a0, EoCases.__eo_typeof.case_190 x_a0, EoCases.__eo_typeof.case_191 x_a0] ++ [EoCases.__eo_typeof.case_192 x_a0, EoCases.__eo_typeof.case_193 x_a0, EoCases.__eo_typeof.case_194 x_a0, EoCases.__eo_typeof.case_195 x_a0, EoCases.__eo_typeof.case_196 x_a0, EoCases.__eo_typeof.case_197 x_a0, EoCases.__eo_typeof.case_198 x_a0, EoCases.__eo_typeof.case_199 x_a0, EoCases.__eo_typeof.case_200 x_a0, EoCases.__eo_typeof.case_201 x_a0, EoCases.__eo_typeof.case_202 x_a0, EoCases.__eo_typeof.case_203 x_a0, EoCases.__eo_typeof.case_204 x_a0, EoCases.__eo_typeof.case_205 x_a0, EoCases.__eo_typeof.case_206 x_a0, EoCases.__eo_typeof.case_207 x_a0] from rfl)
    otherwise ⟨hl_128, hl_129, hl_130, hl_131, hl_132, hl_133, hl_134, hl_135, hl_136, hl_137, hl_138, hl_139, hl_140, hl_141, hl_142, hl_143, hl_144, hl_145, hl_146, hl_147, hl_148, hl_149, hl_150, hl_151, hl_152, hl_153, hl_154, hl_155, hl_156, hl_157, hl_158, hl_159, hl_160, hl_161, hl_162, hl_163, hl_164, hl_165, hl_166, hl_167, hl_168, hl_169, hl_170, hl_171, hl_172, hl_173, hl_174, hl_175, hl_176, hl_177, hl_178, hl_179, hl_180, hl_181, hl_182, hl_183, hl_184, hl_185, hl_186, hl_187, hl_188, hl_189, hl_190, hl_191⟩ using hn_a0 hl_0 hl_1 hl_2 hl_3 hl_4 hl_5 hl_6 hl_7 hl_8 hl_9 hl_10 hl_11 hl_12 hl_13 hl_14 hl_15 hl_16 hl_17 hl_18 hl_19 hl_20 hl_21 hl_22 hl_23 hl_24 hl_25 hl_26 hl_27 hl_28 hl_29 hl_30 hl_31 hl_32 hl_33 hl_34 hl_35 hl_36 hl_37 hl_38 hl_39 hl_40 hl_41 hl_42 hl_43 hl_44 hl_45 hl_46 hl_47 hl_48 hl_49 hl_50 hl_51 hl_52 hl_53 hl_54 hl_55 hl_56 hl_57 hl_58 hl_59 hl_60 hl_61 hl_62 hl_63 hl_64 hl_65 hl_66 hl_67 hl_68 hl_69 hl_70 hl_71 hl_72 hl_73 hl_74 hl_75 hl_76 hl_77 hl_78 hl_79 hl_80 hl_81 hl_82 hl_83 hl_84 hl_85 hl_86 hl_87 hl_88 hl_89 hl_90 hl_91 hl_92 hl_93 hl_94 hl_95 hl_96 hl_97 hl_98 hl_99 hl_100 hl_101 hl_102 hl_103 hl_104 hl_105 hl_106 hl_107 hl_108 hl_109 hl_110 hl_111 hl_112 hl_113 hl_114 hl_115 hl_116 hl_117 hl_118 hl_119 hl_120 hl_121 hl_122 hl_123 hl_124 hl_125 hl_126 hl_127
  body_group_step with cases_2_3_eo__24eo_5ftypeof_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_typeof.case_0 x_a0, EoCases.__eo_typeof.case_1 x_a0, EoCases.__eo_typeof.case_2 x_a0, EoCases.__eo_typeof.case_3 x_a0, EoCases.__eo_typeof.case_4 x_a0, EoCases.__eo_typeof.case_5 x_a0, EoCases.__eo_typeof.case_6 x_a0, EoCases.__eo_typeof.case_7 x_a0, EoCases.__eo_typeof.case_8 x_a0, EoCases.__eo_typeof.case_9 x_a0, EoCases.__eo_typeof.case_10 x_a0, EoCases.__eo_typeof.case_11 x_a0, EoCases.__eo_typeof.case_12 x_a0, EoCases.__eo_typeof.case_13 x_a0, EoCases.__eo_typeof.case_14 x_a0, EoCases.__eo_typeof.case_15 x_a0, EoCases.__eo_typeof.case_16 x_a0, EoCases.__eo_typeof.case_17 x_a0, EoCases.__eo_typeof.case_18 x_a0, EoCases.__eo_typeof.case_19 x_a0, EoCases.__eo_typeof.case_20 x_a0, EoCases.__eo_typeof.case_21 x_a0, EoCases.__eo_typeof.case_22 x_a0, EoCases.__eo_typeof.case_23 x_a0, EoCases.__eo_typeof.case_24 x_a0, EoCases.__eo_typeof.case_25 x_a0, EoCases.__eo_typeof.case_26 x_a0, EoCases.__eo_typeof.case_27 x_a0, EoCases.__eo_typeof.case_28 x_a0, EoCases.__eo_typeof.case_29 x_a0, EoCases.__eo_typeof.case_30 x_a0, EoCases.__eo_typeof.case_31 x_a0, EoCases.__eo_typeof.case_32 x_a0, EoCases.__eo_typeof.case_33 x_a0, EoCases.__eo_typeof.case_34 x_a0, EoCases.__eo_typeof.case_35 x_a0, EoCases.__eo_typeof.case_36 x_a0, EoCases.__eo_typeof.case_37 x_a0, EoCases.__eo_typeof.case_38 x_a0, EoCases.__eo_typeof.case_39 x_a0, EoCases.__eo_typeof.case_40 x_a0, EoCases.__eo_typeof.case_41 x_a0, EoCases.__eo_typeof.case_42 x_a0, EoCases.__eo_typeof.case_43 x_a0, EoCases.__eo_typeof.case_44 x_a0, EoCases.__eo_typeof.case_45 x_a0, EoCases.__eo_typeof.case_46 x_a0, EoCases.__eo_typeof.case_47 x_a0, EoCases.__eo_typeof.case_48 x_a0, EoCases.__eo_typeof.case_49 x_a0, EoCases.__eo_typeof.case_50 x_a0, EoCases.__eo_typeof.case_51 x_a0, EoCases.__eo_typeof.case_52 x_a0, EoCases.__eo_typeof.case_53 x_a0, EoCases.__eo_typeof.case_54 x_a0, EoCases.__eo_typeof.case_55 x_a0, EoCases.__eo_typeof.case_56 x_a0, EoCases.__eo_typeof.case_57 x_a0, EoCases.__eo_typeof.case_58 x_a0, EoCases.__eo_typeof.case_59 x_a0, EoCases.__eo_typeof.case_60 x_a0, EoCases.__eo_typeof.case_61 x_a0, EoCases.__eo_typeof.case_62 x_a0, EoCases.__eo_typeof.case_63 x_a0, EoCases.__eo_typeof.case_64 x_a0, EoCases.__eo_typeof.case_65 x_a0, EoCases.__eo_typeof.case_66 x_a0, EoCases.__eo_typeof.case_67 x_a0, EoCases.__eo_typeof.case_68 x_a0, EoCases.__eo_typeof.case_69 x_a0, EoCases.__eo_typeof.case_70 x_a0, EoCases.__eo_typeof.case_71 x_a0, EoCases.__eo_typeof.case_72 x_a0, EoCases.__eo_typeof.case_73 x_a0, EoCases.__eo_typeof.case_74 x_a0, EoCases.__eo_typeof.case_75 x_a0, EoCases.__eo_typeof.case_76 x_a0, EoCases.__eo_typeof.case_77 x_a0, EoCases.__eo_typeof.case_78 x_a0, EoCases.__eo_typeof.case_79 x_a0, EoCases.__eo_typeof.case_80 x_a0, EoCases.__eo_typeof.case_81 x_a0, EoCases.__eo_typeof.case_82 x_a0, EoCases.__eo_typeof.case_83 x_a0, EoCases.__eo_typeof.case_84 x_a0, EoCases.__eo_typeof.case_85 x_a0, EoCases.__eo_typeof.case_86 x_a0, EoCases.__eo_typeof.case_87 x_a0, EoCases.__eo_typeof.case_88 x_a0, EoCases.__eo_typeof.case_89 x_a0, EoCases.__eo_typeof.case_90 x_a0, EoCases.__eo_typeof.case_91 x_a0, EoCases.__eo_typeof.case_92 x_a0, EoCases.__eo_typeof.case_93 x_a0, EoCases.__eo_typeof.case_94 x_a0, EoCases.__eo_typeof.case_95 x_a0, EoCases.__eo_typeof.case_96 x_a0, EoCases.__eo_typeof.case_97 x_a0, EoCases.__eo_typeof.case_98 x_a0, EoCases.__eo_typeof.case_99 x_a0, EoCases.__eo_typeof.case_100 x_a0, EoCases.__eo_typeof.case_101 x_a0, EoCases.__eo_typeof.case_102 x_a0, EoCases.__eo_typeof.case_103 x_a0, EoCases.__eo_typeof.case_104 x_a0, EoCases.__eo_typeof.case_105 x_a0, EoCases.__eo_typeof.case_106 x_a0, EoCases.__eo_typeof.case_107 x_a0, EoCases.__eo_typeof.case_108 x_a0, EoCases.__eo_typeof.case_109 x_a0, EoCases.__eo_typeof.case_110 x_a0, EoCases.__eo_typeof.case_111 x_a0, EoCases.__eo_typeof.case_112 x_a0, EoCases.__eo_typeof.case_113 x_a0, EoCases.__eo_typeof.case_114 x_a0, EoCases.__eo_typeof.case_115 x_a0, EoCases.__eo_typeof.case_116 x_a0, EoCases.__eo_typeof.case_117 x_a0, EoCases.__eo_typeof.case_118 x_a0, EoCases.__eo_typeof.case_119 x_a0, EoCases.__eo_typeof.case_120 x_a0, EoCases.__eo_typeof.case_121 x_a0, EoCases.__eo_typeof.case_122 x_a0, EoCases.__eo_typeof.case_123 x_a0, EoCases.__eo_typeof.case_124 x_a0, EoCases.__eo_typeof.case_125 x_a0, EoCases.__eo_typeof.case_126 x_a0, EoCases.__eo_typeof.case_127 x_a0, EoCases.__eo_typeof.case_128 x_a0, EoCases.__eo_typeof.case_129 x_a0, EoCases.__eo_typeof.case_130 x_a0, EoCases.__eo_typeof.case_131 x_a0, EoCases.__eo_typeof.case_132 x_a0, EoCases.__eo_typeof.case_133 x_a0, EoCases.__eo_typeof.case_134 x_a0, EoCases.__eo_typeof.case_135 x_a0, EoCases.__eo_typeof.case_136 x_a0, EoCases.__eo_typeof.case_137 x_a0, EoCases.__eo_typeof.case_138 x_a0, EoCases.__eo_typeof.case_139 x_a0, EoCases.__eo_typeof.case_140 x_a0, EoCases.__eo_typeof.case_141 x_a0, EoCases.__eo_typeof.case_142 x_a0, EoCases.__eo_typeof.case_143 x_a0, EoCases.__eo_typeof.case_144 x_a0, EoCases.__eo_typeof.case_145 x_a0, EoCases.__eo_typeof.case_146 x_a0, EoCases.__eo_typeof.case_147 x_a0, EoCases.__eo_typeof.case_148 x_a0, EoCases.__eo_typeof.case_149 x_a0, EoCases.__eo_typeof.case_150 x_a0, EoCases.__eo_typeof.case_151 x_a0, EoCases.__eo_typeof.case_152 x_a0, EoCases.__eo_typeof.case_153 x_a0, EoCases.__eo_typeof.case_154 x_a0, EoCases.__eo_typeof.case_155 x_a0, EoCases.__eo_typeof.case_156 x_a0, EoCases.__eo_typeof.case_157 x_a0, EoCases.__eo_typeof.case_158 x_a0, EoCases.__eo_typeof.case_159 x_a0, EoCases.__eo_typeof.case_160 x_a0, EoCases.__eo_typeof.case_161 x_a0, EoCases.__eo_typeof.case_162 x_a0, EoCases.__eo_typeof.case_163 x_a0, EoCases.__eo_typeof.case_164 x_a0, EoCases.__eo_typeof.case_165 x_a0, EoCases.__eo_typeof.case_166 x_a0, EoCases.__eo_typeof.case_167 x_a0, EoCases.__eo_typeof.case_168 x_a0, EoCases.__eo_typeof.case_169 x_a0, EoCases.__eo_typeof.case_170 x_a0, EoCases.__eo_typeof.case_171 x_a0, EoCases.__eo_typeof.case_172 x_a0, EoCases.__eo_typeof.case_173 x_a0, EoCases.__eo_typeof.case_174 x_a0, EoCases.__eo_typeof.case_175 x_a0, EoCases.__eo_typeof.case_176 x_a0, EoCases.__eo_typeof.case_177 x_a0, EoCases.__eo_typeof.case_178 x_a0, EoCases.__eo_typeof.case_179 x_a0, EoCases.__eo_typeof.case_180 x_a0, EoCases.__eo_typeof.case_181 x_a0, EoCases.__eo_typeof.case_182 x_a0, EoCases.__eo_typeof.case_183 x_a0, EoCases.__eo_typeof.case_184 x_a0, EoCases.__eo_typeof.case_185 x_a0, EoCases.__eo_typeof.case_186 x_a0, EoCases.__eo_typeof.case_187 x_a0, EoCases.__eo_typeof.case_188 x_a0, EoCases.__eo_typeof.case_189 x_a0, EoCases.__eo_typeof.case_190 x_a0, EoCases.__eo_typeof.case_191 x_a0, EoCases.__eo_typeof.case_192 x_a0, EoCases.__eo_typeof.case_193 x_a0, EoCases.__eo_typeof.case_194 x_a0, EoCases.__eo_typeof.case_195 x_a0, EoCases.__eo_typeof.case_196 x_a0, EoCases.__eo_typeof.case_197 x_a0, EoCases.__eo_typeof.case_198 x_a0, EoCases.__eo_typeof.case_199 x_a0, EoCases.__eo_typeof.case_200 x_a0, EoCases.__eo_typeof.case_201 x_a0, EoCases.__eo_typeof.case_202 x_a0, EoCases.__eo_typeof.case_203 x_a0, EoCases.__eo_typeof.case_204 x_a0, EoCases.__eo_typeof.case_205 x_a0, EoCases.__eo_typeof.case_206 x_a0, EoCases.__eo_typeof.case_207 x_a0] = [EoCases.__eo_typeof.case_0 x_a0, EoCases.__eo_typeof.case_1 x_a0, EoCases.__eo_typeof.case_2 x_a0, EoCases.__eo_typeof.case_3 x_a0, EoCases.__eo_typeof.case_4 x_a0, EoCases.__eo_typeof.case_5 x_a0, EoCases.__eo_typeof.case_6 x_a0, EoCases.__eo_typeof.case_7 x_a0, EoCases.__eo_typeof.case_8 x_a0, EoCases.__eo_typeof.case_9 x_a0, EoCases.__eo_typeof.case_10 x_a0, EoCases.__eo_typeof.case_11 x_a0, EoCases.__eo_typeof.case_12 x_a0, EoCases.__eo_typeof.case_13 x_a0, EoCases.__eo_typeof.case_14 x_a0, EoCases.__eo_typeof.case_15 x_a0, EoCases.__eo_typeof.case_16 x_a0, EoCases.__eo_typeof.case_17 x_a0, EoCases.__eo_typeof.case_18 x_a0, EoCases.__eo_typeof.case_19 x_a0, EoCases.__eo_typeof.case_20 x_a0, EoCases.__eo_typeof.case_21 x_a0, EoCases.__eo_typeof.case_22 x_a0, EoCases.__eo_typeof.case_23 x_a0, EoCases.__eo_typeof.case_24 x_a0, EoCases.__eo_typeof.case_25 x_a0, EoCases.__eo_typeof.case_26 x_a0, EoCases.__eo_typeof.case_27 x_a0, EoCases.__eo_typeof.case_28 x_a0, EoCases.__eo_typeof.case_29 x_a0, EoCases.__eo_typeof.case_30 x_a0, EoCases.__eo_typeof.case_31 x_a0, EoCases.__eo_typeof.case_32 x_a0, EoCases.__eo_typeof.case_33 x_a0, EoCases.__eo_typeof.case_34 x_a0, EoCases.__eo_typeof.case_35 x_a0, EoCases.__eo_typeof.case_36 x_a0, EoCases.__eo_typeof.case_37 x_a0, EoCases.__eo_typeof.case_38 x_a0, EoCases.__eo_typeof.case_39 x_a0, EoCases.__eo_typeof.case_40 x_a0, EoCases.__eo_typeof.case_41 x_a0, EoCases.__eo_typeof.case_42 x_a0, EoCases.__eo_typeof.case_43 x_a0, EoCases.__eo_typeof.case_44 x_a0, EoCases.__eo_typeof.case_45 x_a0, EoCases.__eo_typeof.case_46 x_a0, EoCases.__eo_typeof.case_47 x_a0, EoCases.__eo_typeof.case_48 x_a0, EoCases.__eo_typeof.case_49 x_a0, EoCases.__eo_typeof.case_50 x_a0, EoCases.__eo_typeof.case_51 x_a0, EoCases.__eo_typeof.case_52 x_a0, EoCases.__eo_typeof.case_53 x_a0, EoCases.__eo_typeof.case_54 x_a0, EoCases.__eo_typeof.case_55 x_a0, EoCases.__eo_typeof.case_56 x_a0, EoCases.__eo_typeof.case_57 x_a0, EoCases.__eo_typeof.case_58 x_a0, EoCases.__eo_typeof.case_59 x_a0, EoCases.__eo_typeof.case_60 x_a0, EoCases.__eo_typeof.case_61 x_a0, EoCases.__eo_typeof.case_62 x_a0, EoCases.__eo_typeof.case_63 x_a0, EoCases.__eo_typeof.case_64 x_a0, EoCases.__eo_typeof.case_65 x_a0, EoCases.__eo_typeof.case_66 x_a0, EoCases.__eo_typeof.case_67 x_a0, EoCases.__eo_typeof.case_68 x_a0, EoCases.__eo_typeof.case_69 x_a0, EoCases.__eo_typeof.case_70 x_a0, EoCases.__eo_typeof.case_71 x_a0, EoCases.__eo_typeof.case_72 x_a0, EoCases.__eo_typeof.case_73 x_a0, EoCases.__eo_typeof.case_74 x_a0, EoCases.__eo_typeof.case_75 x_a0, EoCases.__eo_typeof.case_76 x_a0, EoCases.__eo_typeof.case_77 x_a0, EoCases.__eo_typeof.case_78 x_a0, EoCases.__eo_typeof.case_79 x_a0, EoCases.__eo_typeof.case_80 x_a0, EoCases.__eo_typeof.case_81 x_a0, EoCases.__eo_typeof.case_82 x_a0, EoCases.__eo_typeof.case_83 x_a0, EoCases.__eo_typeof.case_84 x_a0, EoCases.__eo_typeof.case_85 x_a0, EoCases.__eo_typeof.case_86 x_a0, EoCases.__eo_typeof.case_87 x_a0, EoCases.__eo_typeof.case_88 x_a0, EoCases.__eo_typeof.case_89 x_a0, EoCases.__eo_typeof.case_90 x_a0, EoCases.__eo_typeof.case_91 x_a0, EoCases.__eo_typeof.case_92 x_a0, EoCases.__eo_typeof.case_93 x_a0, EoCases.__eo_typeof.case_94 x_a0, EoCases.__eo_typeof.case_95 x_a0, EoCases.__eo_typeof.case_96 x_a0, EoCases.__eo_typeof.case_97 x_a0, EoCases.__eo_typeof.case_98 x_a0, EoCases.__eo_typeof.case_99 x_a0, EoCases.__eo_typeof.case_100 x_a0, EoCases.__eo_typeof.case_101 x_a0, EoCases.__eo_typeof.case_102 x_a0, EoCases.__eo_typeof.case_103 x_a0, EoCases.__eo_typeof.case_104 x_a0, EoCases.__eo_typeof.case_105 x_a0, EoCases.__eo_typeof.case_106 x_a0, EoCases.__eo_typeof.case_107 x_a0, EoCases.__eo_typeof.case_108 x_a0, EoCases.__eo_typeof.case_109 x_a0, EoCases.__eo_typeof.case_110 x_a0, EoCases.__eo_typeof.case_111 x_a0, EoCases.__eo_typeof.case_112 x_a0, EoCases.__eo_typeof.case_113 x_a0, EoCases.__eo_typeof.case_114 x_a0, EoCases.__eo_typeof.case_115 x_a0, EoCases.__eo_typeof.case_116 x_a0, EoCases.__eo_typeof.case_117 x_a0, EoCases.__eo_typeof.case_118 x_a0, EoCases.__eo_typeof.case_119 x_a0, EoCases.__eo_typeof.case_120 x_a0, EoCases.__eo_typeof.case_121 x_a0, EoCases.__eo_typeof.case_122 x_a0, EoCases.__eo_typeof.case_123 x_a0, EoCases.__eo_typeof.case_124 x_a0, EoCases.__eo_typeof.case_125 x_a0, EoCases.__eo_typeof.case_126 x_a0, EoCases.__eo_typeof.case_127 x_a0, EoCases.__eo_typeof.case_128 x_a0, EoCases.__eo_typeof.case_129 x_a0, EoCases.__eo_typeof.case_130 x_a0, EoCases.__eo_typeof.case_131 x_a0, EoCases.__eo_typeof.case_132 x_a0, EoCases.__eo_typeof.case_133 x_a0, EoCases.__eo_typeof.case_134 x_a0, EoCases.__eo_typeof.case_135 x_a0, EoCases.__eo_typeof.case_136 x_a0, EoCases.__eo_typeof.case_137 x_a0, EoCases.__eo_typeof.case_138 x_a0, EoCases.__eo_typeof.case_139 x_a0, EoCases.__eo_typeof.case_140 x_a0, EoCases.__eo_typeof.case_141 x_a0, EoCases.__eo_typeof.case_142 x_a0, EoCases.__eo_typeof.case_143 x_a0, EoCases.__eo_typeof.case_144 x_a0, EoCases.__eo_typeof.case_145 x_a0, EoCases.__eo_typeof.case_146 x_a0, EoCases.__eo_typeof.case_147 x_a0, EoCases.__eo_typeof.case_148 x_a0, EoCases.__eo_typeof.case_149 x_a0, EoCases.__eo_typeof.case_150 x_a0, EoCases.__eo_typeof.case_151 x_a0, EoCases.__eo_typeof.case_152 x_a0, EoCases.__eo_typeof.case_153 x_a0, EoCases.__eo_typeof.case_154 x_a0, EoCases.__eo_typeof.case_155 x_a0, EoCases.__eo_typeof.case_156 x_a0, EoCases.__eo_typeof.case_157 x_a0, EoCases.__eo_typeof.case_158 x_a0, EoCases.__eo_typeof.case_159 x_a0, EoCases.__eo_typeof.case_160 x_a0, EoCases.__eo_typeof.case_161 x_a0, EoCases.__eo_typeof.case_162 x_a0, EoCases.__eo_typeof.case_163 x_a0, EoCases.__eo_typeof.case_164 x_a0, EoCases.__eo_typeof.case_165 x_a0, EoCases.__eo_typeof.case_166 x_a0, EoCases.__eo_typeof.case_167 x_a0, EoCases.__eo_typeof.case_168 x_a0, EoCases.__eo_typeof.case_169 x_a0, EoCases.__eo_typeof.case_170 x_a0, EoCases.__eo_typeof.case_171 x_a0, EoCases.__eo_typeof.case_172 x_a0, EoCases.__eo_typeof.case_173 x_a0, EoCases.__eo_typeof.case_174 x_a0, EoCases.__eo_typeof.case_175 x_a0, EoCases.__eo_typeof.case_176 x_a0, EoCases.__eo_typeof.case_177 x_a0, EoCases.__eo_typeof.case_178 x_a0, EoCases.__eo_typeof.case_179 x_a0, EoCases.__eo_typeof.case_180 x_a0, EoCases.__eo_typeof.case_181 x_a0, EoCases.__eo_typeof.case_182 x_a0, EoCases.__eo_typeof.case_183 x_a0, EoCases.__eo_typeof.case_184 x_a0, EoCases.__eo_typeof.case_185 x_a0, EoCases.__eo_typeof.case_186 x_a0, EoCases.__eo_typeof.case_187 x_a0, EoCases.__eo_typeof.case_188 x_a0, EoCases.__eo_typeof.case_189 x_a0, EoCases.__eo_typeof.case_190 x_a0, EoCases.__eo_typeof.case_191 x_a0] ++ [EoCases.__eo_typeof.case_192 x_a0, EoCases.__eo_typeof.case_193 x_a0, EoCases.__eo_typeof.case_194 x_a0, EoCases.__eo_typeof.case_195 x_a0, EoCases.__eo_typeof.case_196 x_a0, EoCases.__eo_typeof.case_197 x_a0, EoCases.__eo_typeof.case_198 x_a0, EoCases.__eo_typeof.case_199 x_a0, EoCases.__eo_typeof.case_200 x_a0, EoCases.__eo_typeof.case_201 x_a0, EoCases.__eo_typeof.case_202 x_a0, EoCases.__eo_typeof.case_203 x_a0, EoCases.__eo_typeof.case_204 x_a0, EoCases.__eo_typeof.case_205 x_a0, EoCases.__eo_typeof.case_206 x_a0, EoCases.__eo_typeof.case_207 x_a0] ++ [] from rfl)
    otherwise ⟨hl_192, hl_193, hl_194, hl_195, hl_196, hl_197, hl_198, hl_199, hl_200, hl_201, hl_202, hl_203, hl_204, hl_205, hl_206, hl_207⟩ using hn_a0 hl_0 hl_1 hl_2 hl_3 hl_4 hl_5 hl_6 hl_7 hl_8 hl_9 hl_10 hl_11 hl_12 hl_13 hl_14 hl_15 hl_16 hl_17 hl_18 hl_19 hl_20 hl_21 hl_22 hl_23 hl_24 hl_25 hl_26 hl_27 hl_28 hl_29 hl_30 hl_31 hl_32 hl_33 hl_34 hl_35 hl_36 hl_37 hl_38 hl_39 hl_40 hl_41 hl_42 hl_43 hl_44 hl_45 hl_46 hl_47 hl_48 hl_49 hl_50 hl_51 hl_52 hl_53 hl_54 hl_55 hl_56 hl_57 hl_58 hl_59 hl_60 hl_61 hl_62 hl_63 hl_64 hl_65 hl_66 hl_67 hl_68 hl_69 hl_70 hl_71 hl_72 hl_73 hl_74 hl_75 hl_76 hl_77 hl_78 hl_79 hl_80 hl_81 hl_82 hl_83 hl_84 hl_85 hl_86 hl_87 hl_88 hl_89 hl_90 hl_91 hl_92 hl_93 hl_94 hl_95 hl_96 hl_97 hl_98 hl_99 hl_100 hl_101 hl_102 hl_103 hl_104 hl_105 hl_106 hl_107 hl_108 hl_109 hl_110 hl_111 hl_112 hl_113 hl_114 hl_115 hl_116 hl_117 hl_118 hl_119 hl_120 hl_121 hl_122 hl_123 hl_124 hl_125 hl_126 hl_127 hl_128 hl_129 hl_130 hl_131 hl_132 hl_133 hl_134 hl_135 hl_136 hl_137 hl_138 hl_139 hl_140 hl_141 hl_142 hl_143 hl_144 hl_145 hl_146 hl_147 hl_148 hl_149 hl_150 hl_151 hl_152 hl_153 hl_154 hl_155 hl_156 hl_157 hl_158 hl_159 hl_160 hl_161 hl_162 hl_163 hl_164 hl_165 hl_166 hl_167 hl_168 hl_169 hl_170 hl_171 hl_172 hl_173 hl_174 hl_175 hl_176 hl_177 hl_178 hl_179 hl_180 hl_181 hl_182 hl_183 hl_184 hl_185 hl_186 hl_187 hl_188 hl_189 hl_190 hl_191
  body_stuck hinv4 hG using hn_a0 hl_0 hl_1 hl_2 hl_3 hl_4 hl_5 hl_6 hl_7 hl_8 hl_9 hl_10 hl_11 hl_12 hl_13 hl_14 hl_15 hl_16 hl_17 hl_18 hl_19 hl_20 hl_21 hl_22 hl_23 hl_24 hl_25 hl_26 hl_27 hl_28 hl_29 hl_30 hl_31 hl_32 hl_33 hl_34 hl_35 hl_36 hl_37 hl_38 hl_39 hl_40 hl_41 hl_42 hl_43 hl_44 hl_45 hl_46 hl_47 hl_48 hl_49 hl_50 hl_51 hl_52 hl_53 hl_54 hl_55 hl_56 hl_57 hl_58 hl_59 hl_60 hl_61 hl_62 hl_63 hl_64 hl_65 hl_66 hl_67 hl_68 hl_69 hl_70 hl_71 hl_72 hl_73 hl_74 hl_75 hl_76 hl_77 hl_78 hl_79 hl_80 hl_81 hl_82 hl_83 hl_84 hl_85 hl_86 hl_87 hl_88 hl_89 hl_90 hl_91 hl_92 hl_93 hl_94 hl_95 hl_96 hl_97 hl_98 hl_99 hl_100 hl_101 hl_102 hl_103 hl_104 hl_105 hl_106 hl_107 hl_108 hl_109 hl_110 hl_111 hl_112 hl_113 hl_114 hl_115 hl_116 hl_117 hl_118 hl_119 hl_120 hl_121 hl_122 hl_123 hl_124 hl_125 hl_126 hl_127 hl_128 hl_129 hl_130 hl_131 hl_132 hl_133 hl_134 hl_135 hl_136 hl_137 hl_138 hl_139 hl_140 hl_141 hl_142 hl_143 hl_144 hl_145 hl_146 hl_147 hl_148 hl_149 hl_150 hl_151 hl_152 hl_153 hl_154 hl_155 hl_156 hl_157 hl_158 hl_159 hl_160 hl_161 hl_162 hl_163 hl_164 hl_165 hl_166 hl_167 hl_168 hl_169 hl_170 hl_171 hl_172 hl_173 hl_174 hl_175 hl_176 hl_177 hl_178 hl_179 hl_180 hl_181 hl_182 hl_183 hl_184 hl_185 hl_186 hl_187 hl_188 hl_189 hl_190 hl_191 hl_192 hl_193 hl_194 hl_195 hl_196 hl_197 hl_198 hl_199 hl_200 hl_201 hl_202 hl_203 hl_204 hl_205 hl_206 hl_207 in EoCases.__eo_typeof.case_0 EoCases.__eo_typeof.case_1 EoCases.__eo_typeof.case_2 EoCases.__eo_typeof.case_3 EoCases.__eo_typeof.case_4 EoCases.__eo_typeof.case_5 EoCases.__eo_typeof.case_6 EoCases.__eo_typeof.case_7 EoCases.__eo_typeof.case_8 EoCases.__eo_typeof.case_9 EoCases.__eo_typeof.case_10 EoCases.__eo_typeof.case_11 EoCases.__eo_typeof.case_12 EoCases.__eo_typeof.case_13 EoCases.__eo_typeof.case_14 EoCases.__eo_typeof.case_15 EoCases.__eo_typeof.case_16 EoCases.__eo_typeof.case_17 EoCases.__eo_typeof.case_18 EoCases.__eo_typeof.case_19 EoCases.__eo_typeof.case_20 EoCases.__eo_typeof.case_21 EoCases.__eo_typeof.case_22 EoCases.__eo_typeof.case_23 EoCases.__eo_typeof.case_24 EoCases.__eo_typeof.case_25 EoCases.__eo_typeof.case_26 EoCases.__eo_typeof.case_27 EoCases.__eo_typeof.case_28 EoCases.__eo_typeof.case_29 EoCases.__eo_typeof.case_30 EoCases.__eo_typeof.case_31 EoCases.__eo_typeof.case_32 EoCases.__eo_typeof.case_33 EoCases.__eo_typeof.case_34 EoCases.__eo_typeof.case_35 EoCases.__eo_typeof.case_36 EoCases.__eo_typeof.case_37 EoCases.__eo_typeof.case_38 EoCases.__eo_typeof.case_39 EoCases.__eo_typeof.case_40 EoCases.__eo_typeof.case_41 EoCases.__eo_typeof.case_42 EoCases.__eo_typeof.case_43 EoCases.__eo_typeof.case_44 EoCases.__eo_typeof.case_45 EoCases.__eo_typeof.case_46 EoCases.__eo_typeof.case_47 EoCases.__eo_typeof.case_48 EoCases.__eo_typeof.case_49 EoCases.__eo_typeof.case_50 EoCases.__eo_typeof.case_51 EoCases.__eo_typeof.case_52 EoCases.__eo_typeof.case_53 EoCases.__eo_typeof.case_54 EoCases.__eo_typeof.case_55 EoCases.__eo_typeof.case_56 EoCases.__eo_typeof.case_57 EoCases.__eo_typeof.case_58 EoCases.__eo_typeof.case_59 EoCases.__eo_typeof.case_60 EoCases.__eo_typeof.case_61 EoCases.__eo_typeof.case_62 EoCases.__eo_typeof.case_63 EoCases.__eo_typeof.case_64 EoCases.__eo_typeof.case_65 EoCases.__eo_typeof.case_66 EoCases.__eo_typeof.case_67 EoCases.__eo_typeof.case_68 EoCases.__eo_typeof.case_69 EoCases.__eo_typeof.case_70 EoCases.__eo_typeof.case_71 EoCases.__eo_typeof.case_72 EoCases.__eo_typeof.case_73 EoCases.__eo_typeof.case_74 EoCases.__eo_typeof.case_75 EoCases.__eo_typeof.case_76 EoCases.__eo_typeof.case_77 EoCases.__eo_typeof.case_78 EoCases.__eo_typeof.case_79 EoCases.__eo_typeof.case_80 EoCases.__eo_typeof.case_81 EoCases.__eo_typeof.case_82 EoCases.__eo_typeof.case_83 EoCases.__eo_typeof.case_84 EoCases.__eo_typeof.case_85 EoCases.__eo_typeof.case_86 EoCases.__eo_typeof.case_87 EoCases.__eo_typeof.case_88 EoCases.__eo_typeof.case_89 EoCases.__eo_typeof.case_90 EoCases.__eo_typeof.case_91 EoCases.__eo_typeof.case_92 EoCases.__eo_typeof.case_93 EoCases.__eo_typeof.case_94 EoCases.__eo_typeof.case_95 EoCases.__eo_typeof.case_96 EoCases.__eo_typeof.case_97 EoCases.__eo_typeof.case_98 EoCases.__eo_typeof.case_99 EoCases.__eo_typeof.case_100 EoCases.__eo_typeof.case_101 EoCases.__eo_typeof.case_102 EoCases.__eo_typeof.case_103 EoCases.__eo_typeof.case_104 EoCases.__eo_typeof.case_105 EoCases.__eo_typeof.case_106 EoCases.__eo_typeof.case_107 EoCases.__eo_typeof.case_108 EoCases.__eo_typeof.case_109 EoCases.__eo_typeof.case_110 EoCases.__eo_typeof.case_111 EoCases.__eo_typeof.case_112 EoCases.__eo_typeof.case_113 EoCases.__eo_typeof.case_114 EoCases.__eo_typeof.case_115 EoCases.__eo_typeof.case_116 EoCases.__eo_typeof.case_117 EoCases.__eo_typeof.case_118 EoCases.__eo_typeof.case_119 EoCases.__eo_typeof.case_120 EoCases.__eo_typeof.case_121 EoCases.__eo_typeof.case_122 EoCases.__eo_typeof.case_123 EoCases.__eo_typeof.case_124 EoCases.__eo_typeof.case_125 EoCases.__eo_typeof.case_126 EoCases.__eo_typeof.case_127 EoCases.__eo_typeof.case_128 EoCases.__eo_typeof.case_129 EoCases.__eo_typeof.case_130 EoCases.__eo_typeof.case_131 EoCases.__eo_typeof.case_132 EoCases.__eo_typeof.case_133 EoCases.__eo_typeof.case_134 EoCases.__eo_typeof.case_135 EoCases.__eo_typeof.case_136 EoCases.__eo_typeof.case_137 EoCases.__eo_typeof.case_138 EoCases.__eo_typeof.case_139 EoCases.__eo_typeof.case_140 EoCases.__eo_typeof.case_141 EoCases.__eo_typeof.case_142 EoCases.__eo_typeof.case_143 EoCases.__eo_typeof.case_144 EoCases.__eo_typeof.case_145 EoCases.__eo_typeof.case_146 EoCases.__eo_typeof.case_147 EoCases.__eo_typeof.case_148 EoCases.__eo_typeof.case_149 EoCases.__eo_typeof.case_150 EoCases.__eo_typeof.case_151 EoCases.__eo_typeof.case_152 EoCases.__eo_typeof.case_153 EoCases.__eo_typeof.case_154 EoCases.__eo_typeof.case_155 EoCases.__eo_typeof.case_156 EoCases.__eo_typeof.case_157 EoCases.__eo_typeof.case_158 EoCases.__eo_typeof.case_159 EoCases.__eo_typeof.case_160 EoCases.__eo_typeof.case_161 EoCases.__eo_typeof.case_162 EoCases.__eo_typeof.case_163 EoCases.__eo_typeof.case_164 EoCases.__eo_typeof.case_165 EoCases.__eo_typeof.case_166 EoCases.__eo_typeof.case_167 EoCases.__eo_typeof.case_168 EoCases.__eo_typeof.case_169 EoCases.__eo_typeof.case_170 EoCases.__eo_typeof.case_171 EoCases.__eo_typeof.case_172 EoCases.__eo_typeof.case_173 EoCases.__eo_typeof.case_174 EoCases.__eo_typeof.case_175 EoCases.__eo_typeof.case_176 EoCases.__eo_typeof.case_177 EoCases.__eo_typeof.case_178 EoCases.__eo_typeof.case_179 EoCases.__eo_typeof.case_180 EoCases.__eo_typeof.case_181 EoCases.__eo_typeof.case_182 EoCases.__eo_typeof.case_183 EoCases.__eo_typeof.case_184 EoCases.__eo_typeof.case_185 EoCases.__eo_typeof.case_186 EoCases.__eo_typeof.case_187 EoCases.__eo_typeof.case_188 EoCases.__eo_typeof.case_189 EoCases.__eo_typeof.case_190 EoCases.__eo_typeof.case_191 EoCases.__eo_typeof.case_192 EoCases.__eo_typeof.case_193 EoCases.__eo_typeof.case_194 EoCases.__eo_typeof.case_195 EoCases.__eo_typeof.case_196 EoCases.__eo_typeof.case_197 EoCases.__eo_typeof.case_198 EoCases.__eo_typeof.case_199 EoCases.__eo_typeof.case_200 EoCases.__eo_typeof.case_201 EoCases.__eo_typeof.case_202 EoCases.__eo_typeof.case_203 EoCases.__eo_typeof.case_204 EoCases.__eo_typeof.case_205 EoCases.__eo_typeof.case_206 EoCases.__eo_typeof.case_207

theorem eo__24eo_5ftypeof_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5ftypeof.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5ftypeof
  apply WP.dspec_mono (Store.framed_type_cached s hinv hrem h64 cache.TypeCacheKind.Eunoia a0
    (fun s1 => body_eo__24eo_5ftypeof s1 a0) (fun s' t => Represents.rep s' t (__eo_typeof x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, y0, hargs, hb0, hr⟩ := ProgramSem.of_4294967296 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_4294967296 ⟨a0, x_a0, rfl, Rep.mono hpre h_a0, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5ftypeof_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

end pathos_compiled_checker
