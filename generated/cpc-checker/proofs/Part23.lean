module
public import $PROOFS$.Head
public import $PROOFS$.Part22
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

theorem case_169_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_169_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_169 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_169 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_169_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_169
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_169
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__2f_5ftotal.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_169
  store_step with ih.eo__24eo_5fto_5fsmt s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 dropping h_v4 h_v5 h_v6 hinv1 s1 v4 v5 v6
  store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v7 dropping h_v2 hinv2 s2 v2
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fsm_2e_2f_5ftotal.construct s3 e_v9 (by rw [he_v9]; rfl) h_v7 h_v8 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying dropping h_v7 h_v8 he_v9 hinv3 e_v9 s3 v7 v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_to_smt.case_169 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_170_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_170_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_170 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_170 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_170_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_170
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__40div_5fby_5fzero.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v1 h_v2 dropping h_a0 he_v3 e_v3
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_170
  store_step with ih.eo__24eo_5fto_5fsmt s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying dropping h_v1 h_v2 h_v3 hinv1 s1 v1 v2 v3
  simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.raw_int_u32_spec s2 0#u32 (0) (by scalar_tac) hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_v4 dropping hinv2 s2
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.raw_int_u32_spec s3 1#u32 (1) (by scalar_tac) hinv3 h64 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_v4 h_v5 dropping hinv3 s3
  step as ⟨e_v7, he_v7⟩
  store_step with Store.native_spec_mk_rational s4 e_v7 (by rw [he_v7]; rfl) h_v5 h_v6 hinv4 h64 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_v4 dropping h_v5 h_v6 he_v7 hinv4 e_v7 s4 v5 v6
  rw [← Bridge.native_mk_rational] at h_v7
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eRational.construct s5 e_v8 (by rw [he_v8]; rfl) h_v7 hinv5 h64 as ⟨v8, s6, hinv6, h_v8⟩ growing hG carrying h_v4 dropping h_v7 he_v8 hinv5 e_v8 s5 v7
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fsm_2e_2f.construct s6 e_v9 (by rw [he_v9]; rfl) h_v4 h_v8 hinv6 h64 as ⟨v9, s7, hinv7, h_v9⟩ growing hG carrying dropping h_v4 h_v8 he_v9 hinv6 e_v9 s6 v4 v8
  case_done hinv7 hG with h_v9 in EoCases.__eo_to_smt.case_170 using hn_v1 hn_v2

theorem case_171_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_171_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_171 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_171 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_171_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_171
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_171
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_forall.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v4 h_v5 dropping h_a0 h_v1 h_v2 he_v6 e_v6 v1 v2
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_171
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s1 e_v7 (by rw [he_v7]; exact empty_args) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v5 dropping h_v4 h_v6 he_v7 hinv1 e_v7 s1 v4 v6
  pat_same v5 v7 with h_v5 h_v7 using hinv2 else hinv2 hG in EoCases.__eo_to_smt.case_171
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eNone.construct s2 e_v8 (by rw [he_v8]; exact empty_args) hinv2 h64 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying dropping h_v5 h_v7 he_v8 hinv2 e_v8 s2 v5 v7
  case_done hinv3 hG with h_v8 in EoCases.__eo_to_smt.case_171 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_172_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_172_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_172 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_172 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_172_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_172
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_172
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_forall.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_172
  store_step with ih.eo__24eo_5fto_5fsmt s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v5 dropping h_v2 h_v4 h_v6 hinv1 s1 v2 v4 v6
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__24emb_5fsm_2enot.construct s2 e_v8 (by rw [he_v8]; rfl) h_v7 hinv2 h64 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v5 dropping h_v7 he_v8 hinv2 e_v8 s2 v7
  store_step with ih.eo__24eo_5fto_5fsmt_5fexists s3 v5 v8 _ _ hinv3 h64 (hG.rem hrem) h_v5 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying dropping h_v5 h_v8 hinv3 s3 v5 v8
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo__24emb_5fsm_2enot.construct s4 e_v10 (by rw [he_v10]; rfl) h_v9 hinv4 h64 as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying dropping h_v9 he_v10 hinv4 e_v10 s4 v9
  case_done hinv5 hG with h_v10 in EoCases.__eo_to_smt.case_172 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_173_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_173_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_173 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_173 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_173_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_173
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_173
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_exists.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v4 h_v5 dropping h_a0 h_v1 h_v2 he_v6 e_v6 v1 v2
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_173
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s1 e_v7 (by rw [he_v7]; exact empty_args) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v5 dropping h_v4 h_v6 he_v7 hinv1 e_v7 s1 v4 v6
  pat_same v5 v7 with h_v5 h_v7 using hinv2 else hinv2 hG in EoCases.__eo_to_smt.case_173
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eNone.construct s2 e_v8 (by rw [he_v8]; exact empty_args) hinv2 h64 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying dropping h_v5 h_v7 he_v8 hinv2 e_v8 s2 v5 v7
  case_done hinv3 hG with h_v8 in EoCases.__eo_to_smt.case_173 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_174_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_174_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_174 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_174 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_174_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_174
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_174
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_exists.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_174
  store_step with ih.eo__24eo_5fto_5fsmt s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v5 dropping h_v2 h_v4 h_v6 hinv1 s1 v2 v4 v6
  store_step with ih.eo__24eo_5fto_5fsmt_5fexists s2 v5 v7 _ _ hinv2 h64 (hG.rem hrem) h_v5 h_v7 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying dropping h_v5 h_v7 hinv2 s2 v5 v7
  case_done hinv3 hG with h_v8 in EoCases.__eo_to_smt.case_174 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_175_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_175_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_175 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_175 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_175_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__40quantifiers_5fskolemize.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__eo_to_smt.case_175
  obtain ⟨hn_v1, hn_v2⟩ := CtorSpec.eo__40quantifiers_5fskolemize.fields_ne_stuck hinv h_a0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_175
  pat_unapply h_v4 as ⟨v7, v8, x_v7, x_v8, h_v7, h_v8, hn_v7, hn_v8⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_175
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_forall.construct s e_v9 (by rw [he_v9]; exact empty_args) hinv h64 as ⟨v9, s1, hinv1, h_v9⟩ growing hG carrying h_v2 h_v5 h_v7 h_v8 dropping h_a0 h_v1 h_v4 he_v9 e_v9 v1 v4
  pat_same v7 v9 with h_v7 h_v9 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_175
  store_step with ih.eo__24eo_5fto_5fsmt_5fnat_5fis_5fvalid s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v10, s2, hinv2, h_v10⟩ growing hG carrying h_v2 h_v5 h_v8 dropping h_v7 h_v9 hinv1 s1 v7 v9
  have h_ite_v16 := (show if_21_eo__24eo_5fto_5fsmt s2 v10 v5 v2 v8 ⦃ r s' => s'.Inv ∧ s2.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_21_eo__24eo_5fto_5fsmt
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s2
    rcases Store.boolean_value_native h_v10 with ⟨hx_11, hbv_11⟩ | ⟨hx_11, hbv_11⟩
    · ite_branch hbv_11
      store_step with ih.eo__24eo_5fto_5fsmt s2 v5 _ hinv2 h64 (hG.rem hrem) h_v5 as ⟨v11, s3, hinv3, h_v11⟩ growing hG carrying h_v2 h_v8 dropping h_v10 h_v5 v10 v5
      step as ⟨e_v12, he_v12⟩
      store_step with CtorSpec.eo__24emb_5fsm_2enot.construct s3 e_v12 (by rw [he_v12]; rfl) h_v11 hinv3 h64 as ⟨v12, s4, hinv4, h_v12⟩ growing hG carrying h_v2 h_v8 dropping h_v11 he_v12 e_v12 v11
      store_step with ih.eo__24eo_5fto_5fsmt_5fnat s4 v2 _ hinv4 h64 (hG.rem hrem) h_v2 as ⟨v13, s5, hinv5, h_v13⟩ growing hG carrying h_v8 h_v12 dropping h_v2 hinv4 s4 v2
      store_step with ih.eo__24eo_5fto_5fsmt_5fquantifiers_5fskolemize s5 v8 v12 v13 _ _ _ hinv5 h64 (hG.rem hrem) h_v8 h_v12 h_v13 as ⟨v14, s6, hinv6, h_v14⟩ growing hG carrying dropping h_v12 h_v13 h_v8 hinv5 s5 v12 v13 v8
      ite_done hinv6 hG with (native_ite_true_rep _ hx_11 h_v14)
    · ite_branch hbv_11
      step as ⟨e_v15, he_v15⟩
      store_step with CtorSpec.eo__24emb_5fsm_2eNone.construct s2 e_v15 (by rw [he_v15]; exact empty_args) hinv2 h64 as ⟨v15, s3, hinv3, h_v15⟩ growing hG carrying dropping h_v10 h_v2 h_v5 h_v8 he_v15 hinv2 e_v15 s2 v10 v2 v5 v8
      ite_done hinv3 hG with (native_ite_false_rep _ hx_11 h_v15))
  store_step with h_ite_v16 as ⟨v16, s3, hinv3, h_v16⟩ growing hG carrying dropping h_ite_v16 h_v10 h_v2 h_v5 h_v8 hinv2 s2 v10 v2 v5 v8
  case_done hinv3 hG with h_v16 in EoCases.__eo_to_smt.case_175 using hn_v1 hn_v2 hn_v4 hn_v5 hn_v7 hn_v8

theorem case_176_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_176_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_176 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_176 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_176_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_176
  pat_destruct CtorSpec.eo_int_5fto_5fbv.destruct h_v1 as ⟨v4, x_v4, h_v4⟩ else hinv hG in EoCases.__eo_to_smt.case_176
  obtain hn_v4 := CtorSpec.eo_int_5fto_5fbv.fields_ne_stuck hinv h_v1
  store_step with ih.eo__24eo_5fto_5fsmt s v4 _ hinv h64 hrem h_v4 as ⟨v5, s1, hinv1, h_v5⟩ growing hG carrying h_v2 dropping h_a0 h_v1 h_v4 v1 v4
  store_step with ih.eo__24eo_5fto_5fsmt s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v6, s2, hinv2, h_v6⟩ growing hG carrying h_v5 dropping h_v2 hinv1 s1 v2
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eint_5fto_5fbv.construct s2 e_v7 (by rw [he_v7]; rfl) h_v5 h_v6 hinv2 h64 as ⟨v7, s3, hinv3, h_v7⟩ growing hG carrying dropping h_v5 h_v6 he_v7 hinv2 e_v7 s2 v5 v6
  case_done hinv3 hG with h_v7 in EoCases.__eo_to_smt.case_176 using hn_v1 hn_v2 hn_v4

theorem case_177_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_177_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_177 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_177 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_177_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_177
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_ubv_5fto_5fint.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v1 h_v2 dropping h_a0 he_v3 e_v3
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_177
  store_step with ih.eo__24eo_5fto_5fsmt s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying dropping h_v1 h_v2 h_v3 hinv1 s1 v1 v2 v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eubv_5fto_5fint.construct s2 e_v5 (by rw [he_v5]; rfl) h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying dropping h_v4 he_v5 hinv2 e_v5 s2 v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_to_smt.case_177 using hn_v1 hn_v2

theorem case_178_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_178_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_178 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_178 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_178_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_178
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_sbv_5fto_5fint.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v1 h_v2 dropping h_a0 he_v3 e_v3
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_to_smt.case_178
  store_step with ih.eo__24eo_5fto_5fsmt s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying dropping h_v1 h_v2 h_v3 hinv1 s1 v1 v2 v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5fsm_2esbv_5fto_5fint.construct s2 e_v5 (by rw [he_v5]; rfl) h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying dropping h_v4 he_v5 hinv2 e_v5 s2 v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_to_smt.case_178 using hn_v1 hn_v2

theorem case_179_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_179_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_179 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_179 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_179_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__40const.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__eo_to_smt.case_179
  obtain ⟨hn_v1, hn_v2⟩ := CtorSpec.eo__40const.fields_ne_stuck hinv h_a0
  store_step with ih.eo__24eo_5fto_5fsmt_5fnat_5fis_5fvalid s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v1 h_v2 dropping h_a0
  have h_ite_v9 := (show if_22_eo__24eo_5fto_5fsmt s1 v3 v1 v2 ⦃ r s' => s'.Inv ∧ s1.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_22_eo__24eo_5fto_5fsmt
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s1
    rcases Store.boolean_value_native h_v3 with ⟨hx_4, hbv_4⟩ | ⟨hx_4, hbv_4⟩
    · ite_branch hbv_4
      store_step with ih.eo__24eo_5fto_5fsmt_5fnat s1 v1 _ hinv1 h64 (hG.rem hrem) h_v1 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v2 dropping h_v1 h_v3 v1 v3
      step as ⟨e_v5, he_v5⟩
      store_step with Store.native_spec_const_id s2 e_v5 (by rw [he_v5]; rfl) h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_v2 dropping h_v4 he_v5 e_v5 v4
      rw [← Bridge.native_const_id] at h_v5
      store_step with ih.eo__24eo_5fto_5fsmt_5ftype s3 v2 _ hinv3 h64 (hG.rem hrem) h_v2 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_v5 dropping h_v2 hinv3 s3 v2
      step as ⟨e_v7, he_v7⟩
      store_step with CtorSpec.eo__24emb_5fsm_2eUConst.construct s4 e_v7 (by rw [he_v7]; rfl) h_v5 h_v6 hinv4 h64 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying dropping h_v5 h_v6 he_v7 hinv4 e_v7 s4 v5 v6
      ite_done hinv5 hG with (native_ite_true_rep _ hx_4 h_v7)
    · ite_branch hbv_4
      step as ⟨e_v8, he_v8⟩
      store_step with CtorSpec.eo__24emb_5fsm_2eNone.construct s1 e_v8 (by rw [he_v8]; exact empty_args) hinv1 h64 as ⟨v8, s2, hinv2, h_v8⟩ growing hG carrying dropping h_v1 h_v2 h_v3 he_v8 hinv1 e_v8 s1 v1 v2 v3
      ite_done hinv2 hG with (native_ite_false_rep _ hx_4 h_v8))
  store_step with h_ite_v9 as ⟨v9, s2, hinv2, h_v9⟩ growing hG carrying dropping h_ite_v9 h_v1 h_v2 h_v3 hinv1 s1 v1 v2 v3
  case_done hinv2 hG with h_v9 in EoCases.__eo_to_smt.case_179 using hn_v1 hn_v2

theorem case_180_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_180_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_180 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_180 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_180_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_180
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_180
  store_step with Store.apply_rep s v4 v5 _ _ hinv h64 h_v4 h_v5 (by ns_tac) (by ns_tac) as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 dropping h_a0 h_v1 h_v4 h_v5 v1 v4 v5
  store_step with ih.eo__24eo_5fto_5fsmt s1 v6 _ hinv1 h64 (hG.rem hrem) h_v6 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 dropping h_v6 hinv1 s1 v6
  store_step with ih.eo__24eo_5fto_5fsmt s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v7 dropping h_v2 hinv2 s2 v2
  store_step with ih.eo__24eo_5fto_5fsmt_5fapply s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying dropping h_v7 h_v8 hinv3 s3 v7 v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_to_smt.case_180 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_181_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_181_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_181 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_181 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_181_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt.case_181
  store_step with ih.eo__24eo_5fto_5fsmt s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v2 dropping h_a0 h_v1 v1
  store_step with ih.eo__24eo_5fto_5fsmt s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v3 dropping h_v2 hinv1 s1 v2
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eApply.construct s2 e_v5 (by rw [he_v5]; rfl) h_v3 h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying dropping h_v3 h_v4 he_v5 hinv2 e_v5 s2 v3 v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_to_smt.case_181 using hn_v1 hn_v2

theorem case_182_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_182_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt.case_182 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_182 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_182_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eNone.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying dropping he_v0 e_v0
  case_done hinv1 hG with h_v0 in EoCases.__eo_to_smt.case_182 using

theorem cases_0_0_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_0_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_to_smt.case_0 x_a0, EoCases.__eo_to_smt.case_1 x_a0, EoCases.__eo_to_smt.case_2 x_a0, EoCases.__eo_to_smt.case_3 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_0 x_a0 = none ∧ EoCases.__eo_to_smt.case_1 x_a0 = none ∧ EoCases.__eo_to_smt.case_2 x_a0 = none ∧ EoCases.__eo_to_smt.case_3 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_0_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  group_step with case_0_eo__24eo_5fto_5fsmt_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_0 x_a0, EoCases.__eo_to_smt.case_1 x_a0, EoCases.__eo_to_smt.case_2 x_a0, EoCases.__eo_to_smt.case_3 x_a0] = [] ++ [EoCases.__eo_to_smt.case_0 x_a0] ++ [EoCases.__eo_to_smt.case_1 x_a0, EoCases.__eo_to_smt.case_2 x_a0, EoCases.__eo_to_smt.case_3 x_a0] from rfl)
    otherwise ⟨hl_0⟩ using
  group_step with case_1_eo__24eo_5fto_5fsmt_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_0 x_a0, EoCases.__eo_to_smt.case_1 x_a0, EoCases.__eo_to_smt.case_2 x_a0, EoCases.__eo_to_smt.case_3 x_a0] = [EoCases.__eo_to_smt.case_0 x_a0] ++ [EoCases.__eo_to_smt.case_1 x_a0] ++ [EoCases.__eo_to_smt.case_2 x_a0, EoCases.__eo_to_smt.case_3 x_a0] from rfl)
    otherwise ⟨hl_1⟩ using hl_0
  group_step with case_2_eo__24eo_5fto_5fsmt_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_0 x_a0, EoCases.__eo_to_smt.case_1 x_a0, EoCases.__eo_to_smt.case_2 x_a0, EoCases.__eo_to_smt.case_3 x_a0] = [EoCases.__eo_to_smt.case_0 x_a0, EoCases.__eo_to_smt.case_1 x_a0] ++ [EoCases.__eo_to_smt.case_2 x_a0] ++ [EoCases.__eo_to_smt.case_3 x_a0] from rfl)
    otherwise ⟨hl_2⟩ using hl_0 hl_1
  group_step with case_3_eo__24eo_5fto_5fsmt_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_0 x_a0, EoCases.__eo_to_smt.case_1 x_a0, EoCases.__eo_to_smt.case_2 x_a0, EoCases.__eo_to_smt.case_3 x_a0] = [EoCases.__eo_to_smt.case_0 x_a0, EoCases.__eo_to_smt.case_1 x_a0, EoCases.__eo_to_smt.case_2 x_a0] ++ [EoCases.__eo_to_smt.case_3 x_a0] ++ [] from rfl)
    otherwise ⟨hl_3⟩ using hl_0 hl_1 hl_2
  group_none hinv4 hG with ⟨hl_0, hl_1, hl_2, hl_3⟩

theorem cases_0_1_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_1_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_to_smt.case_4 x_a0, EoCases.__eo_to_smt.case_5 x_a0, EoCases.__eo_to_smt.case_6 x_a0, EoCases.__eo_to_smt.case_7 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_4 x_a0 = none ∧ EoCases.__eo_to_smt.case_5 x_a0 = none ∧ EoCases.__eo_to_smt.case_6 x_a0 = none ∧ EoCases.__eo_to_smt.case_7 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_1_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  group_step with case_4_eo__24eo_5fto_5fsmt_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_4 x_a0, EoCases.__eo_to_smt.case_5 x_a0, EoCases.__eo_to_smt.case_6 x_a0, EoCases.__eo_to_smt.case_7 x_a0] = [] ++ [EoCases.__eo_to_smt.case_4 x_a0] ++ [EoCases.__eo_to_smt.case_5 x_a0, EoCases.__eo_to_smt.case_6 x_a0, EoCases.__eo_to_smt.case_7 x_a0] from rfl)
    otherwise ⟨hl_4⟩ using
  group_step with case_5_eo__24eo_5fto_5fsmt_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_4 x_a0, EoCases.__eo_to_smt.case_5 x_a0, EoCases.__eo_to_smt.case_6 x_a0, EoCases.__eo_to_smt.case_7 x_a0] = [EoCases.__eo_to_smt.case_4 x_a0] ++ [EoCases.__eo_to_smt.case_5 x_a0] ++ [EoCases.__eo_to_smt.case_6 x_a0, EoCases.__eo_to_smt.case_7 x_a0] from rfl)
    otherwise ⟨hl_5⟩ using hl_4
  group_step with case_6_eo__24eo_5fto_5fsmt_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_4 x_a0, EoCases.__eo_to_smt.case_5 x_a0, EoCases.__eo_to_smt.case_6 x_a0, EoCases.__eo_to_smt.case_7 x_a0] = [EoCases.__eo_to_smt.case_4 x_a0, EoCases.__eo_to_smt.case_5 x_a0] ++ [EoCases.__eo_to_smt.case_6 x_a0] ++ [EoCases.__eo_to_smt.case_7 x_a0] from rfl)
    otherwise ⟨hl_6⟩ using hl_4 hl_5
  group_step with case_7_eo__24eo_5fto_5fsmt_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_4 x_a0, EoCases.__eo_to_smt.case_5 x_a0, EoCases.__eo_to_smt.case_6 x_a0, EoCases.__eo_to_smt.case_7 x_a0] = [EoCases.__eo_to_smt.case_4 x_a0, EoCases.__eo_to_smt.case_5 x_a0, EoCases.__eo_to_smt.case_6 x_a0] ++ [EoCases.__eo_to_smt.case_7 x_a0] ++ [] from rfl)
    otherwise ⟨hl_7⟩ using hl_4 hl_5 hl_6
  group_none hinv4 hG with ⟨hl_4, hl_5, hl_6, hl_7⟩

theorem cases_0_2_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_2_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_to_smt.case_8 x_a0, EoCases.__eo_to_smt.case_9 x_a0, EoCases.__eo_to_smt.case_10 x_a0, EoCases.__eo_to_smt.case_11 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_8 x_a0 = none ∧ EoCases.__eo_to_smt.case_9 x_a0 = none ∧ EoCases.__eo_to_smt.case_10 x_a0 = none ∧ EoCases.__eo_to_smt.case_11 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_2_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  group_step with case_8_eo__24eo_5fto_5fsmt_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_8 x_a0, EoCases.__eo_to_smt.case_9 x_a0, EoCases.__eo_to_smt.case_10 x_a0, EoCases.__eo_to_smt.case_11 x_a0] = [] ++ [EoCases.__eo_to_smt.case_8 x_a0] ++ [EoCases.__eo_to_smt.case_9 x_a0, EoCases.__eo_to_smt.case_10 x_a0, EoCases.__eo_to_smt.case_11 x_a0] from rfl)
    otherwise ⟨hl_8⟩ using
  group_step with case_9_eo__24eo_5fto_5fsmt_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_8 x_a0, EoCases.__eo_to_smt.case_9 x_a0, EoCases.__eo_to_smt.case_10 x_a0, EoCases.__eo_to_smt.case_11 x_a0] = [EoCases.__eo_to_smt.case_8 x_a0] ++ [EoCases.__eo_to_smt.case_9 x_a0] ++ [EoCases.__eo_to_smt.case_10 x_a0, EoCases.__eo_to_smt.case_11 x_a0] from rfl)
    otherwise ⟨hl_9⟩ using hl_8
  group_step with case_10_eo__24eo_5fto_5fsmt_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_8 x_a0, EoCases.__eo_to_smt.case_9 x_a0, EoCases.__eo_to_smt.case_10 x_a0, EoCases.__eo_to_smt.case_11 x_a0] = [EoCases.__eo_to_smt.case_8 x_a0, EoCases.__eo_to_smt.case_9 x_a0] ++ [EoCases.__eo_to_smt.case_10 x_a0] ++ [EoCases.__eo_to_smt.case_11 x_a0] from rfl)
    otherwise ⟨hl_10⟩ using hl_8 hl_9
  group_step with case_11_eo__24eo_5fto_5fsmt_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_8 x_a0, EoCases.__eo_to_smt.case_9 x_a0, EoCases.__eo_to_smt.case_10 x_a0, EoCases.__eo_to_smt.case_11 x_a0] = [EoCases.__eo_to_smt.case_8 x_a0, EoCases.__eo_to_smt.case_9 x_a0, EoCases.__eo_to_smt.case_10 x_a0] ++ [EoCases.__eo_to_smt.case_11 x_a0] ++ [] from rfl)
    otherwise ⟨hl_11⟩ using hl_8 hl_9 hl_10
  group_none hinv4 hG with ⟨hl_8, hl_9, hl_10, hl_11⟩

theorem cases_0_3_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_3_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_to_smt.case_12 x_a0, EoCases.__eo_to_smt.case_13 x_a0, EoCases.__eo_to_smt.case_14 x_a0, EoCases.__eo_to_smt.case_15 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_12 x_a0 = none ∧ EoCases.__eo_to_smt.case_13 x_a0 = none ∧ EoCases.__eo_to_smt.case_14 x_a0 = none ∧ EoCases.__eo_to_smt.case_15 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_3_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  group_step with case_12_eo__24eo_5fto_5fsmt_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_12 x_a0, EoCases.__eo_to_smt.case_13 x_a0, EoCases.__eo_to_smt.case_14 x_a0, EoCases.__eo_to_smt.case_15 x_a0] = [] ++ [EoCases.__eo_to_smt.case_12 x_a0] ++ [EoCases.__eo_to_smt.case_13 x_a0, EoCases.__eo_to_smt.case_14 x_a0, EoCases.__eo_to_smt.case_15 x_a0] from rfl)
    otherwise ⟨hl_12⟩ using
  group_step with case_13_eo__24eo_5fto_5fsmt_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_12 x_a0, EoCases.__eo_to_smt.case_13 x_a0, EoCases.__eo_to_smt.case_14 x_a0, EoCases.__eo_to_smt.case_15 x_a0] = [EoCases.__eo_to_smt.case_12 x_a0] ++ [EoCases.__eo_to_smt.case_13 x_a0] ++ [EoCases.__eo_to_smt.case_14 x_a0, EoCases.__eo_to_smt.case_15 x_a0] from rfl)
    otherwise ⟨hl_13⟩ using hl_12
  group_step with case_14_eo__24eo_5fto_5fsmt_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_12 x_a0, EoCases.__eo_to_smt.case_13 x_a0, EoCases.__eo_to_smt.case_14 x_a0, EoCases.__eo_to_smt.case_15 x_a0] = [EoCases.__eo_to_smt.case_12 x_a0, EoCases.__eo_to_smt.case_13 x_a0] ++ [EoCases.__eo_to_smt.case_14 x_a0] ++ [EoCases.__eo_to_smt.case_15 x_a0] from rfl)
    otherwise ⟨hl_14⟩ using hl_12 hl_13
  group_step with case_15_eo__24eo_5fto_5fsmt_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_12 x_a0, EoCases.__eo_to_smt.case_13 x_a0, EoCases.__eo_to_smt.case_14 x_a0, EoCases.__eo_to_smt.case_15 x_a0] = [EoCases.__eo_to_smt.case_12 x_a0, EoCases.__eo_to_smt.case_13 x_a0, EoCases.__eo_to_smt.case_14 x_a0] ++ [EoCases.__eo_to_smt.case_15 x_a0] ++ [] from rfl)
    otherwise ⟨hl_15⟩ using hl_12 hl_13 hl_14
  group_none hinv4 hG with ⟨hl_12, hl_13, hl_14, hl_15⟩

theorem cases_0_4_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_4_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_to_smt.case_16 x_a0, EoCases.__eo_to_smt.case_17 x_a0, EoCases.__eo_to_smt.case_18 x_a0, EoCases.__eo_to_smt.case_19 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_16 x_a0 = none ∧ EoCases.__eo_to_smt.case_17 x_a0 = none ∧ EoCases.__eo_to_smt.case_18 x_a0 = none ∧ EoCases.__eo_to_smt.case_19 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_4_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  group_step with case_16_eo__24eo_5fto_5fsmt_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_16 x_a0, EoCases.__eo_to_smt.case_17 x_a0, EoCases.__eo_to_smt.case_18 x_a0, EoCases.__eo_to_smt.case_19 x_a0] = [] ++ [EoCases.__eo_to_smt.case_16 x_a0] ++ [EoCases.__eo_to_smt.case_17 x_a0, EoCases.__eo_to_smt.case_18 x_a0, EoCases.__eo_to_smt.case_19 x_a0] from rfl)
    otherwise ⟨hl_16⟩ using
  group_step with case_17_eo__24eo_5fto_5fsmt_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_16 x_a0, EoCases.__eo_to_smt.case_17 x_a0, EoCases.__eo_to_smt.case_18 x_a0, EoCases.__eo_to_smt.case_19 x_a0] = [EoCases.__eo_to_smt.case_16 x_a0] ++ [EoCases.__eo_to_smt.case_17 x_a0] ++ [EoCases.__eo_to_smt.case_18 x_a0, EoCases.__eo_to_smt.case_19 x_a0] from rfl)
    otherwise ⟨hl_17⟩ using hl_16
  group_step with case_18_eo__24eo_5fto_5fsmt_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_16 x_a0, EoCases.__eo_to_smt.case_17 x_a0, EoCases.__eo_to_smt.case_18 x_a0, EoCases.__eo_to_smt.case_19 x_a0] = [EoCases.__eo_to_smt.case_16 x_a0, EoCases.__eo_to_smt.case_17 x_a0] ++ [EoCases.__eo_to_smt.case_18 x_a0] ++ [EoCases.__eo_to_smt.case_19 x_a0] from rfl)
    otherwise ⟨hl_18⟩ using hl_16 hl_17
  group_step with case_19_eo__24eo_5fto_5fsmt_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_16 x_a0, EoCases.__eo_to_smt.case_17 x_a0, EoCases.__eo_to_smt.case_18 x_a0, EoCases.__eo_to_smt.case_19 x_a0] = [EoCases.__eo_to_smt.case_16 x_a0, EoCases.__eo_to_smt.case_17 x_a0, EoCases.__eo_to_smt.case_18 x_a0] ++ [EoCases.__eo_to_smt.case_19 x_a0] ++ [] from rfl)
    otherwise ⟨hl_19⟩ using hl_16 hl_17 hl_18
  group_none hinv4 hG with ⟨hl_16, hl_17, hl_18, hl_19⟩

theorem cases_0_5_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_5_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_to_smt.case_20 x_a0, EoCases.__eo_to_smt.case_21 x_a0, EoCases.__eo_to_smt.case_22 x_a0, EoCases.__eo_to_smt.case_23 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_20 x_a0 = none ∧ EoCases.__eo_to_smt.case_21 x_a0 = none ∧ EoCases.__eo_to_smt.case_22 x_a0 = none ∧ EoCases.__eo_to_smt.case_23 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_5_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  group_step with case_20_eo__24eo_5fto_5fsmt_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_20 x_a0, EoCases.__eo_to_smt.case_21 x_a0, EoCases.__eo_to_smt.case_22 x_a0, EoCases.__eo_to_smt.case_23 x_a0] = [] ++ [EoCases.__eo_to_smt.case_20 x_a0] ++ [EoCases.__eo_to_smt.case_21 x_a0, EoCases.__eo_to_smt.case_22 x_a0, EoCases.__eo_to_smt.case_23 x_a0] from rfl)
    otherwise ⟨hl_20⟩ using
  group_step with case_21_eo__24eo_5fto_5fsmt_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_20 x_a0, EoCases.__eo_to_smt.case_21 x_a0, EoCases.__eo_to_smt.case_22 x_a0, EoCases.__eo_to_smt.case_23 x_a0] = [EoCases.__eo_to_smt.case_20 x_a0] ++ [EoCases.__eo_to_smt.case_21 x_a0] ++ [EoCases.__eo_to_smt.case_22 x_a0, EoCases.__eo_to_smt.case_23 x_a0] from rfl)
    otherwise ⟨hl_21⟩ using hl_20
  group_step with case_22_eo__24eo_5fto_5fsmt_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_20 x_a0, EoCases.__eo_to_smt.case_21 x_a0, EoCases.__eo_to_smt.case_22 x_a0, EoCases.__eo_to_smt.case_23 x_a0] = [EoCases.__eo_to_smt.case_20 x_a0, EoCases.__eo_to_smt.case_21 x_a0] ++ [EoCases.__eo_to_smt.case_22 x_a0] ++ [EoCases.__eo_to_smt.case_23 x_a0] from rfl)
    otherwise ⟨hl_22⟩ using hl_20 hl_21
  group_step with case_23_eo__24eo_5fto_5fsmt_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_20 x_a0, EoCases.__eo_to_smt.case_21 x_a0, EoCases.__eo_to_smt.case_22 x_a0, EoCases.__eo_to_smt.case_23 x_a0] = [EoCases.__eo_to_smt.case_20 x_a0, EoCases.__eo_to_smt.case_21 x_a0, EoCases.__eo_to_smt.case_22 x_a0] ++ [EoCases.__eo_to_smt.case_23 x_a0] ++ [] from rfl)
    otherwise ⟨hl_23⟩ using hl_20 hl_21 hl_22
  group_none hinv4 hG with ⟨hl_20, hl_21, hl_22, hl_23⟩

theorem cases_0_6_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_6_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_to_smt.case_24 x_a0, EoCases.__eo_to_smt.case_25 x_a0, EoCases.__eo_to_smt.case_26 x_a0, EoCases.__eo_to_smt.case_27 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_24 x_a0 = none ∧ EoCases.__eo_to_smt.case_25 x_a0 = none ∧ EoCases.__eo_to_smt.case_26 x_a0 = none ∧ EoCases.__eo_to_smt.case_27 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_6_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  group_step with case_24_eo__24eo_5fto_5fsmt_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_24 x_a0, EoCases.__eo_to_smt.case_25 x_a0, EoCases.__eo_to_smt.case_26 x_a0, EoCases.__eo_to_smt.case_27 x_a0] = [] ++ [EoCases.__eo_to_smt.case_24 x_a0] ++ [EoCases.__eo_to_smt.case_25 x_a0, EoCases.__eo_to_smt.case_26 x_a0, EoCases.__eo_to_smt.case_27 x_a0] from rfl)
    otherwise ⟨hl_24⟩ using
  group_step with case_25_eo__24eo_5fto_5fsmt_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_24 x_a0, EoCases.__eo_to_smt.case_25 x_a0, EoCases.__eo_to_smt.case_26 x_a0, EoCases.__eo_to_smt.case_27 x_a0] = [EoCases.__eo_to_smt.case_24 x_a0] ++ [EoCases.__eo_to_smt.case_25 x_a0] ++ [EoCases.__eo_to_smt.case_26 x_a0, EoCases.__eo_to_smt.case_27 x_a0] from rfl)
    otherwise ⟨hl_25⟩ using hl_24
  group_step with case_26_eo__24eo_5fto_5fsmt_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_24 x_a0, EoCases.__eo_to_smt.case_25 x_a0, EoCases.__eo_to_smt.case_26 x_a0, EoCases.__eo_to_smt.case_27 x_a0] = [EoCases.__eo_to_smt.case_24 x_a0, EoCases.__eo_to_smt.case_25 x_a0] ++ [EoCases.__eo_to_smt.case_26 x_a0] ++ [EoCases.__eo_to_smt.case_27 x_a0] from rfl)
    otherwise ⟨hl_26⟩ using hl_24 hl_25
  group_step with case_27_eo__24eo_5fto_5fsmt_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_24 x_a0, EoCases.__eo_to_smt.case_25 x_a0, EoCases.__eo_to_smt.case_26 x_a0, EoCases.__eo_to_smt.case_27 x_a0] = [EoCases.__eo_to_smt.case_24 x_a0, EoCases.__eo_to_smt.case_25 x_a0, EoCases.__eo_to_smt.case_26 x_a0] ++ [EoCases.__eo_to_smt.case_27 x_a0] ++ [] from rfl)
    otherwise ⟨hl_27⟩ using hl_24 hl_25 hl_26
  group_none hinv4 hG with ⟨hl_24, hl_25, hl_26, hl_27⟩

theorem cases_0_7_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_7_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_to_smt.case_28 x_a0, EoCases.__eo_to_smt.case_29 x_a0, EoCases.__eo_to_smt.case_30 x_a0, EoCases.__eo_to_smt.case_31 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_28 x_a0 = none ∧ EoCases.__eo_to_smt.case_29 x_a0 = none ∧ EoCases.__eo_to_smt.case_30 x_a0 = none ∧ EoCases.__eo_to_smt.case_31 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_7_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  group_step with case_28_eo__24eo_5fto_5fsmt_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_28 x_a0, EoCases.__eo_to_smt.case_29 x_a0, EoCases.__eo_to_smt.case_30 x_a0, EoCases.__eo_to_smt.case_31 x_a0] = [] ++ [EoCases.__eo_to_smt.case_28 x_a0] ++ [EoCases.__eo_to_smt.case_29 x_a0, EoCases.__eo_to_smt.case_30 x_a0, EoCases.__eo_to_smt.case_31 x_a0] from rfl)
    otherwise ⟨hl_28⟩ using
  group_step with case_29_eo__24eo_5fto_5fsmt_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_28 x_a0, EoCases.__eo_to_smt.case_29 x_a0, EoCases.__eo_to_smt.case_30 x_a0, EoCases.__eo_to_smt.case_31 x_a0] = [EoCases.__eo_to_smt.case_28 x_a0] ++ [EoCases.__eo_to_smt.case_29 x_a0] ++ [EoCases.__eo_to_smt.case_30 x_a0, EoCases.__eo_to_smt.case_31 x_a0] from rfl)
    otherwise ⟨hl_29⟩ using hl_28
  group_step with case_30_eo__24eo_5fto_5fsmt_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_28 x_a0, EoCases.__eo_to_smt.case_29 x_a0, EoCases.__eo_to_smt.case_30 x_a0, EoCases.__eo_to_smt.case_31 x_a0] = [EoCases.__eo_to_smt.case_28 x_a0, EoCases.__eo_to_smt.case_29 x_a0] ++ [EoCases.__eo_to_smt.case_30 x_a0] ++ [EoCases.__eo_to_smt.case_31 x_a0] from rfl)
    otherwise ⟨hl_30⟩ using hl_28 hl_29
  group_step with case_31_eo__24eo_5fto_5fsmt_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_28 x_a0, EoCases.__eo_to_smt.case_29 x_a0, EoCases.__eo_to_smt.case_30 x_a0, EoCases.__eo_to_smt.case_31 x_a0] = [EoCases.__eo_to_smt.case_28 x_a0, EoCases.__eo_to_smt.case_29 x_a0, EoCases.__eo_to_smt.case_30 x_a0] ++ [EoCases.__eo_to_smt.case_31 x_a0] ++ [] from rfl)
    otherwise ⟨hl_31⟩ using hl_28 hl_29 hl_30
  group_none hinv4 hG with ⟨hl_28, hl_29, hl_30, hl_31⟩

theorem cases_0_8_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_8_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_to_smt.case_32 x_a0, EoCases.__eo_to_smt.case_33 x_a0, EoCases.__eo_to_smt.case_34 x_a0, EoCases.__eo_to_smt.case_35 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_32 x_a0 = none ∧ EoCases.__eo_to_smt.case_33 x_a0 = none ∧ EoCases.__eo_to_smt.case_34 x_a0 = none ∧ EoCases.__eo_to_smt.case_35 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_8_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  group_step with case_32_eo__24eo_5fto_5fsmt_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_32 x_a0, EoCases.__eo_to_smt.case_33 x_a0, EoCases.__eo_to_smt.case_34 x_a0, EoCases.__eo_to_smt.case_35 x_a0] = [] ++ [EoCases.__eo_to_smt.case_32 x_a0] ++ [EoCases.__eo_to_smt.case_33 x_a0, EoCases.__eo_to_smt.case_34 x_a0, EoCases.__eo_to_smt.case_35 x_a0] from rfl)
    otherwise ⟨hl_32⟩ using
  group_step with case_33_eo__24eo_5fto_5fsmt_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_32 x_a0, EoCases.__eo_to_smt.case_33 x_a0, EoCases.__eo_to_smt.case_34 x_a0, EoCases.__eo_to_smt.case_35 x_a0] = [EoCases.__eo_to_smt.case_32 x_a0] ++ [EoCases.__eo_to_smt.case_33 x_a0] ++ [EoCases.__eo_to_smt.case_34 x_a0, EoCases.__eo_to_smt.case_35 x_a0] from rfl)
    otherwise ⟨hl_33⟩ using hl_32
  group_step with case_34_eo__24eo_5fto_5fsmt_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_32 x_a0, EoCases.__eo_to_smt.case_33 x_a0, EoCases.__eo_to_smt.case_34 x_a0, EoCases.__eo_to_smt.case_35 x_a0] = [EoCases.__eo_to_smt.case_32 x_a0, EoCases.__eo_to_smt.case_33 x_a0] ++ [EoCases.__eo_to_smt.case_34 x_a0] ++ [EoCases.__eo_to_smt.case_35 x_a0] from rfl)
    otherwise ⟨hl_34⟩ using hl_32 hl_33
  group_step with case_35_eo__24eo_5fto_5fsmt_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_32 x_a0, EoCases.__eo_to_smt.case_33 x_a0, EoCases.__eo_to_smt.case_34 x_a0, EoCases.__eo_to_smt.case_35 x_a0] = [EoCases.__eo_to_smt.case_32 x_a0, EoCases.__eo_to_smt.case_33 x_a0, EoCases.__eo_to_smt.case_34 x_a0] ++ [EoCases.__eo_to_smt.case_35 x_a0] ++ [] from rfl)
    otherwise ⟨hl_35⟩ using hl_32 hl_33 hl_34
  group_none hinv4 hG with ⟨hl_32, hl_33, hl_34, hl_35⟩

theorem cases_0_9_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_9_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_to_smt.case_36 x_a0, EoCases.__eo_to_smt.case_37 x_a0, EoCases.__eo_to_smt.case_38 x_a0, EoCases.__eo_to_smt.case_39 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_36 x_a0 = none ∧ EoCases.__eo_to_smt.case_37 x_a0 = none ∧ EoCases.__eo_to_smt.case_38 x_a0 = none ∧ EoCases.__eo_to_smt.case_39 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_9_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  group_step with case_36_eo__24eo_5fto_5fsmt_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_36 x_a0, EoCases.__eo_to_smt.case_37 x_a0, EoCases.__eo_to_smt.case_38 x_a0, EoCases.__eo_to_smt.case_39 x_a0] = [] ++ [EoCases.__eo_to_smt.case_36 x_a0] ++ [EoCases.__eo_to_smt.case_37 x_a0, EoCases.__eo_to_smt.case_38 x_a0, EoCases.__eo_to_smt.case_39 x_a0] from rfl)
    otherwise ⟨hl_36⟩ using
  group_step with case_37_eo__24eo_5fto_5fsmt_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_36 x_a0, EoCases.__eo_to_smt.case_37 x_a0, EoCases.__eo_to_smt.case_38 x_a0, EoCases.__eo_to_smt.case_39 x_a0] = [EoCases.__eo_to_smt.case_36 x_a0] ++ [EoCases.__eo_to_smt.case_37 x_a0] ++ [EoCases.__eo_to_smt.case_38 x_a0, EoCases.__eo_to_smt.case_39 x_a0] from rfl)
    otherwise ⟨hl_37⟩ using hl_36
  group_step with case_38_eo__24eo_5fto_5fsmt_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_36 x_a0, EoCases.__eo_to_smt.case_37 x_a0, EoCases.__eo_to_smt.case_38 x_a0, EoCases.__eo_to_smt.case_39 x_a0] = [EoCases.__eo_to_smt.case_36 x_a0, EoCases.__eo_to_smt.case_37 x_a0] ++ [EoCases.__eo_to_smt.case_38 x_a0] ++ [EoCases.__eo_to_smt.case_39 x_a0] from rfl)
    otherwise ⟨hl_38⟩ using hl_36 hl_37
  group_step with case_39_eo__24eo_5fto_5fsmt_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_36 x_a0, EoCases.__eo_to_smt.case_37 x_a0, EoCases.__eo_to_smt.case_38 x_a0, EoCases.__eo_to_smt.case_39 x_a0] = [EoCases.__eo_to_smt.case_36 x_a0, EoCases.__eo_to_smt.case_37 x_a0, EoCases.__eo_to_smt.case_38 x_a0] ++ [EoCases.__eo_to_smt.case_39 x_a0] ++ [] from rfl)
    otherwise ⟨hl_39⟩ using hl_36 hl_37 hl_38
  group_none hinv4 hG with ⟨hl_36, hl_37, hl_38, hl_39⟩

theorem cases_0_10_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_10_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_to_smt.case_40 x_a0, EoCases.__eo_to_smt.case_41 x_a0, EoCases.__eo_to_smt.case_42 x_a0, EoCases.__eo_to_smt.case_43 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_40 x_a0 = none ∧ EoCases.__eo_to_smt.case_41 x_a0 = none ∧ EoCases.__eo_to_smt.case_42 x_a0 = none ∧ EoCases.__eo_to_smt.case_43 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_10_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  group_step with case_40_eo__24eo_5fto_5fsmt_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_40 x_a0, EoCases.__eo_to_smt.case_41 x_a0, EoCases.__eo_to_smt.case_42 x_a0, EoCases.__eo_to_smt.case_43 x_a0] = [] ++ [EoCases.__eo_to_smt.case_40 x_a0] ++ [EoCases.__eo_to_smt.case_41 x_a0, EoCases.__eo_to_smt.case_42 x_a0, EoCases.__eo_to_smt.case_43 x_a0] from rfl)
    otherwise ⟨hl_40⟩ using
  group_step with case_41_eo__24eo_5fto_5fsmt_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_40 x_a0, EoCases.__eo_to_smt.case_41 x_a0, EoCases.__eo_to_smt.case_42 x_a0, EoCases.__eo_to_smt.case_43 x_a0] = [EoCases.__eo_to_smt.case_40 x_a0] ++ [EoCases.__eo_to_smt.case_41 x_a0] ++ [EoCases.__eo_to_smt.case_42 x_a0, EoCases.__eo_to_smt.case_43 x_a0] from rfl)
    otherwise ⟨hl_41⟩ using hl_40
  group_step with case_42_eo__24eo_5fto_5fsmt_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_40 x_a0, EoCases.__eo_to_smt.case_41 x_a0, EoCases.__eo_to_smt.case_42 x_a0, EoCases.__eo_to_smt.case_43 x_a0] = [EoCases.__eo_to_smt.case_40 x_a0, EoCases.__eo_to_smt.case_41 x_a0] ++ [EoCases.__eo_to_smt.case_42 x_a0] ++ [EoCases.__eo_to_smt.case_43 x_a0] from rfl)
    otherwise ⟨hl_42⟩ using hl_40 hl_41
  group_step with case_43_eo__24eo_5fto_5fsmt_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_40 x_a0, EoCases.__eo_to_smt.case_41 x_a0, EoCases.__eo_to_smt.case_42 x_a0, EoCases.__eo_to_smt.case_43 x_a0] = [EoCases.__eo_to_smt.case_40 x_a0, EoCases.__eo_to_smt.case_41 x_a0, EoCases.__eo_to_smt.case_42 x_a0] ++ [EoCases.__eo_to_smt.case_43 x_a0] ++ [] from rfl)
    otherwise ⟨hl_43⟩ using hl_40 hl_41 hl_42
  group_none hinv4 hG with ⟨hl_40, hl_41, hl_42, hl_43⟩

theorem cases_0_11_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_11_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_to_smt.case_44 x_a0, EoCases.__eo_to_smt.case_45 x_a0, EoCases.__eo_to_smt.case_46 x_a0, EoCases.__eo_to_smt.case_47 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_44 x_a0 = none ∧ EoCases.__eo_to_smt.case_45 x_a0 = none ∧ EoCases.__eo_to_smt.case_46 x_a0 = none ∧ EoCases.__eo_to_smt.case_47 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_11_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  group_step with case_44_eo__24eo_5fto_5fsmt_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_44 x_a0, EoCases.__eo_to_smt.case_45 x_a0, EoCases.__eo_to_smt.case_46 x_a0, EoCases.__eo_to_smt.case_47 x_a0] = [] ++ [EoCases.__eo_to_smt.case_44 x_a0] ++ [EoCases.__eo_to_smt.case_45 x_a0, EoCases.__eo_to_smt.case_46 x_a0, EoCases.__eo_to_smt.case_47 x_a0] from rfl)
    otherwise ⟨hl_44⟩ using
  group_step with case_45_eo__24eo_5fto_5fsmt_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_44 x_a0, EoCases.__eo_to_smt.case_45 x_a0, EoCases.__eo_to_smt.case_46 x_a0, EoCases.__eo_to_smt.case_47 x_a0] = [EoCases.__eo_to_smt.case_44 x_a0] ++ [EoCases.__eo_to_smt.case_45 x_a0] ++ [EoCases.__eo_to_smt.case_46 x_a0, EoCases.__eo_to_smt.case_47 x_a0] from rfl)
    otherwise ⟨hl_45⟩ using hl_44
  group_step with case_46_eo__24eo_5fto_5fsmt_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_44 x_a0, EoCases.__eo_to_smt.case_45 x_a0, EoCases.__eo_to_smt.case_46 x_a0, EoCases.__eo_to_smt.case_47 x_a0] = [EoCases.__eo_to_smt.case_44 x_a0, EoCases.__eo_to_smt.case_45 x_a0] ++ [EoCases.__eo_to_smt.case_46 x_a0] ++ [EoCases.__eo_to_smt.case_47 x_a0] from rfl)
    otherwise ⟨hl_46⟩ using hl_44 hl_45
  group_step with case_47_eo__24eo_5fto_5fsmt_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_44 x_a0, EoCases.__eo_to_smt.case_45 x_a0, EoCases.__eo_to_smt.case_46 x_a0, EoCases.__eo_to_smt.case_47 x_a0] = [EoCases.__eo_to_smt.case_44 x_a0, EoCases.__eo_to_smt.case_45 x_a0, EoCases.__eo_to_smt.case_46 x_a0] ++ [EoCases.__eo_to_smt.case_47 x_a0] ++ [] from rfl)
    otherwise ⟨hl_47⟩ using hl_44 hl_45 hl_46
  group_none hinv4 hG with ⟨hl_44, hl_45, hl_46, hl_47⟩

theorem cases_0_12_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_12_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_to_smt.case_48 x_a0, EoCases.__eo_to_smt.case_49 x_a0, EoCases.__eo_to_smt.case_50 x_a0, EoCases.__eo_to_smt.case_51 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_48 x_a0 = none ∧ EoCases.__eo_to_smt.case_49 x_a0 = none ∧ EoCases.__eo_to_smt.case_50 x_a0 = none ∧ EoCases.__eo_to_smt.case_51 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_12_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  group_step with case_48_eo__24eo_5fto_5fsmt_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_48 x_a0, EoCases.__eo_to_smt.case_49 x_a0, EoCases.__eo_to_smt.case_50 x_a0, EoCases.__eo_to_smt.case_51 x_a0] = [] ++ [EoCases.__eo_to_smt.case_48 x_a0] ++ [EoCases.__eo_to_smt.case_49 x_a0, EoCases.__eo_to_smt.case_50 x_a0, EoCases.__eo_to_smt.case_51 x_a0] from rfl)
    otherwise ⟨hl_48⟩ using
  group_step with case_49_eo__24eo_5fto_5fsmt_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_48 x_a0, EoCases.__eo_to_smt.case_49 x_a0, EoCases.__eo_to_smt.case_50 x_a0, EoCases.__eo_to_smt.case_51 x_a0] = [EoCases.__eo_to_smt.case_48 x_a0] ++ [EoCases.__eo_to_smt.case_49 x_a0] ++ [EoCases.__eo_to_smt.case_50 x_a0, EoCases.__eo_to_smt.case_51 x_a0] from rfl)
    otherwise ⟨hl_49⟩ using hl_48
  group_step with case_50_eo__24eo_5fto_5fsmt_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_48 x_a0, EoCases.__eo_to_smt.case_49 x_a0, EoCases.__eo_to_smt.case_50 x_a0, EoCases.__eo_to_smt.case_51 x_a0] = [EoCases.__eo_to_smt.case_48 x_a0, EoCases.__eo_to_smt.case_49 x_a0] ++ [EoCases.__eo_to_smt.case_50 x_a0] ++ [EoCases.__eo_to_smt.case_51 x_a0] from rfl)
    otherwise ⟨hl_50⟩ using hl_48 hl_49
  group_step with case_51_eo__24eo_5fto_5fsmt_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_48 x_a0, EoCases.__eo_to_smt.case_49 x_a0, EoCases.__eo_to_smt.case_50 x_a0, EoCases.__eo_to_smt.case_51 x_a0] = [EoCases.__eo_to_smt.case_48 x_a0, EoCases.__eo_to_smt.case_49 x_a0, EoCases.__eo_to_smt.case_50 x_a0] ++ [EoCases.__eo_to_smt.case_51 x_a0] ++ [] from rfl)
    otherwise ⟨hl_51⟩ using hl_48 hl_49 hl_50
  group_none hinv4 hG with ⟨hl_48, hl_49, hl_50, hl_51⟩

theorem cases_0_13_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_13_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_to_smt.case_52 x_a0, EoCases.__eo_to_smt.case_53 x_a0, EoCases.__eo_to_smt.case_54 x_a0, EoCases.__eo_to_smt.case_55 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_52 x_a0 = none ∧ EoCases.__eo_to_smt.case_53 x_a0 = none ∧ EoCases.__eo_to_smt.case_54 x_a0 = none ∧ EoCases.__eo_to_smt.case_55 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_13_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  group_step with case_52_eo__24eo_5fto_5fsmt_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_52 x_a0, EoCases.__eo_to_smt.case_53 x_a0, EoCases.__eo_to_smt.case_54 x_a0, EoCases.__eo_to_smt.case_55 x_a0] = [] ++ [EoCases.__eo_to_smt.case_52 x_a0] ++ [EoCases.__eo_to_smt.case_53 x_a0, EoCases.__eo_to_smt.case_54 x_a0, EoCases.__eo_to_smt.case_55 x_a0] from rfl)
    otherwise ⟨hl_52⟩ using
  group_step with case_53_eo__24eo_5fto_5fsmt_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_52 x_a0, EoCases.__eo_to_smt.case_53 x_a0, EoCases.__eo_to_smt.case_54 x_a0, EoCases.__eo_to_smt.case_55 x_a0] = [EoCases.__eo_to_smt.case_52 x_a0] ++ [EoCases.__eo_to_smt.case_53 x_a0] ++ [EoCases.__eo_to_smt.case_54 x_a0, EoCases.__eo_to_smt.case_55 x_a0] from rfl)
    otherwise ⟨hl_53⟩ using hl_52
  group_step with case_54_eo__24eo_5fto_5fsmt_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_52 x_a0, EoCases.__eo_to_smt.case_53 x_a0, EoCases.__eo_to_smt.case_54 x_a0, EoCases.__eo_to_smt.case_55 x_a0] = [EoCases.__eo_to_smt.case_52 x_a0, EoCases.__eo_to_smt.case_53 x_a0] ++ [EoCases.__eo_to_smt.case_54 x_a0] ++ [EoCases.__eo_to_smt.case_55 x_a0] from rfl)
    otherwise ⟨hl_54⟩ using hl_52 hl_53
  group_step with case_55_eo__24eo_5fto_5fsmt_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_52 x_a0, EoCases.__eo_to_smt.case_53 x_a0, EoCases.__eo_to_smt.case_54 x_a0, EoCases.__eo_to_smt.case_55 x_a0] = [EoCases.__eo_to_smt.case_52 x_a0, EoCases.__eo_to_smt.case_53 x_a0, EoCases.__eo_to_smt.case_54 x_a0] ++ [EoCases.__eo_to_smt.case_55 x_a0] ++ [] from rfl)
    otherwise ⟨hl_55⟩ using hl_52 hl_53 hl_54
  group_none hinv4 hG with ⟨hl_52, hl_53, hl_54, hl_55⟩

theorem cases_0_14_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_14_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_to_smt.case_56 x_a0, EoCases.__eo_to_smt.case_57 x_a0, EoCases.__eo_to_smt.case_58 x_a0, EoCases.__eo_to_smt.case_59 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_56 x_a0 = none ∧ EoCases.__eo_to_smt.case_57 x_a0 = none ∧ EoCases.__eo_to_smt.case_58 x_a0 = none ∧ EoCases.__eo_to_smt.case_59 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_14_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  group_step with case_56_eo__24eo_5fto_5fsmt_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_56 x_a0, EoCases.__eo_to_smt.case_57 x_a0, EoCases.__eo_to_smt.case_58 x_a0, EoCases.__eo_to_smt.case_59 x_a0] = [] ++ [EoCases.__eo_to_smt.case_56 x_a0] ++ [EoCases.__eo_to_smt.case_57 x_a0, EoCases.__eo_to_smt.case_58 x_a0, EoCases.__eo_to_smt.case_59 x_a0] from rfl)
    otherwise ⟨hl_56⟩ using
  group_step with case_57_eo__24eo_5fto_5fsmt_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_56 x_a0, EoCases.__eo_to_smt.case_57 x_a0, EoCases.__eo_to_smt.case_58 x_a0, EoCases.__eo_to_smt.case_59 x_a0] = [EoCases.__eo_to_smt.case_56 x_a0] ++ [EoCases.__eo_to_smt.case_57 x_a0] ++ [EoCases.__eo_to_smt.case_58 x_a0, EoCases.__eo_to_smt.case_59 x_a0] from rfl)
    otherwise ⟨hl_57⟩ using hl_56
  group_step with case_58_eo__24eo_5fto_5fsmt_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_56 x_a0, EoCases.__eo_to_smt.case_57 x_a0, EoCases.__eo_to_smt.case_58 x_a0, EoCases.__eo_to_smt.case_59 x_a0] = [EoCases.__eo_to_smt.case_56 x_a0, EoCases.__eo_to_smt.case_57 x_a0] ++ [EoCases.__eo_to_smt.case_58 x_a0] ++ [EoCases.__eo_to_smt.case_59 x_a0] from rfl)
    otherwise ⟨hl_58⟩ using hl_56 hl_57
  group_step with case_59_eo__24eo_5fto_5fsmt_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_56 x_a0, EoCases.__eo_to_smt.case_57 x_a0, EoCases.__eo_to_smt.case_58 x_a0, EoCases.__eo_to_smt.case_59 x_a0] = [EoCases.__eo_to_smt.case_56 x_a0, EoCases.__eo_to_smt.case_57 x_a0, EoCases.__eo_to_smt.case_58 x_a0] ++ [EoCases.__eo_to_smt.case_59 x_a0] ++ [] from rfl)
    otherwise ⟨hl_59⟩ using hl_56 hl_57 hl_58
  group_none hinv4 hG with ⟨hl_56, hl_57, hl_58, hl_59⟩

theorem cases_0_15_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_15_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_to_smt.case_60 x_a0, EoCases.__eo_to_smt.case_61 x_a0, EoCases.__eo_to_smt.case_62 x_a0, EoCases.__eo_to_smt.case_63 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_60 x_a0 = none ∧ EoCases.__eo_to_smt.case_61 x_a0 = none ∧ EoCases.__eo_to_smt.case_62 x_a0 = none ∧ EoCases.__eo_to_smt.case_63 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_15_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  group_step with case_60_eo__24eo_5fto_5fsmt_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_60 x_a0, EoCases.__eo_to_smt.case_61 x_a0, EoCases.__eo_to_smt.case_62 x_a0, EoCases.__eo_to_smt.case_63 x_a0] = [] ++ [EoCases.__eo_to_smt.case_60 x_a0] ++ [EoCases.__eo_to_smt.case_61 x_a0, EoCases.__eo_to_smt.case_62 x_a0, EoCases.__eo_to_smt.case_63 x_a0] from rfl)
    otherwise ⟨hl_60⟩ using
  group_step with case_61_eo__24eo_5fto_5fsmt_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_60 x_a0, EoCases.__eo_to_smt.case_61 x_a0, EoCases.__eo_to_smt.case_62 x_a0, EoCases.__eo_to_smt.case_63 x_a0] = [EoCases.__eo_to_smt.case_60 x_a0] ++ [EoCases.__eo_to_smt.case_61 x_a0] ++ [EoCases.__eo_to_smt.case_62 x_a0, EoCases.__eo_to_smt.case_63 x_a0] from rfl)
    otherwise ⟨hl_61⟩ using hl_60
  group_step with case_62_eo__24eo_5fto_5fsmt_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_60 x_a0, EoCases.__eo_to_smt.case_61 x_a0, EoCases.__eo_to_smt.case_62 x_a0, EoCases.__eo_to_smt.case_63 x_a0] = [EoCases.__eo_to_smt.case_60 x_a0, EoCases.__eo_to_smt.case_61 x_a0] ++ [EoCases.__eo_to_smt.case_62 x_a0] ++ [EoCases.__eo_to_smt.case_63 x_a0] from rfl)
    otherwise ⟨hl_62⟩ using hl_60 hl_61
  group_step with case_63_eo__24eo_5fto_5fsmt_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_60 x_a0, EoCases.__eo_to_smt.case_61 x_a0, EoCases.__eo_to_smt.case_62 x_a0, EoCases.__eo_to_smt.case_63 x_a0] = [EoCases.__eo_to_smt.case_60 x_a0, EoCases.__eo_to_smt.case_61 x_a0, EoCases.__eo_to_smt.case_62 x_a0] ++ [EoCases.__eo_to_smt.case_63 x_a0] ++ [] from rfl)
    otherwise ⟨hl_63⟩ using hl_60 hl_61 hl_62
  group_none hinv4 hG with ⟨hl_60, hl_61, hl_62, hl_63⟩

theorem cases_0_16_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_16_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_to_smt.case_64 x_a0, EoCases.__eo_to_smt.case_65 x_a0, EoCases.__eo_to_smt.case_66 x_a0, EoCases.__eo_to_smt.case_67 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_64 x_a0 = none ∧ EoCases.__eo_to_smt.case_65 x_a0 = none ∧ EoCases.__eo_to_smt.case_66 x_a0 = none ∧ EoCases.__eo_to_smt.case_67 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_16_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  group_step with case_64_eo__24eo_5fto_5fsmt_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_64 x_a0, EoCases.__eo_to_smt.case_65 x_a0, EoCases.__eo_to_smt.case_66 x_a0, EoCases.__eo_to_smt.case_67 x_a0] = [] ++ [EoCases.__eo_to_smt.case_64 x_a0] ++ [EoCases.__eo_to_smt.case_65 x_a0, EoCases.__eo_to_smt.case_66 x_a0, EoCases.__eo_to_smt.case_67 x_a0] from rfl)
    otherwise ⟨hl_64⟩ using
  group_step with case_65_eo__24eo_5fto_5fsmt_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_64 x_a0, EoCases.__eo_to_smt.case_65 x_a0, EoCases.__eo_to_smt.case_66 x_a0, EoCases.__eo_to_smt.case_67 x_a0] = [EoCases.__eo_to_smt.case_64 x_a0] ++ [EoCases.__eo_to_smt.case_65 x_a0] ++ [EoCases.__eo_to_smt.case_66 x_a0, EoCases.__eo_to_smt.case_67 x_a0] from rfl)
    otherwise ⟨hl_65⟩ using hl_64
  group_step with case_66_eo__24eo_5fto_5fsmt_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_64 x_a0, EoCases.__eo_to_smt.case_65 x_a0, EoCases.__eo_to_smt.case_66 x_a0, EoCases.__eo_to_smt.case_67 x_a0] = [EoCases.__eo_to_smt.case_64 x_a0, EoCases.__eo_to_smt.case_65 x_a0] ++ [EoCases.__eo_to_smt.case_66 x_a0] ++ [EoCases.__eo_to_smt.case_67 x_a0] from rfl)
    otherwise ⟨hl_66⟩ using hl_64 hl_65
  group_step with case_67_eo__24eo_5fto_5fsmt_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_64 x_a0, EoCases.__eo_to_smt.case_65 x_a0, EoCases.__eo_to_smt.case_66 x_a0, EoCases.__eo_to_smt.case_67 x_a0] = [EoCases.__eo_to_smt.case_64 x_a0, EoCases.__eo_to_smt.case_65 x_a0, EoCases.__eo_to_smt.case_66 x_a0] ++ [EoCases.__eo_to_smt.case_67 x_a0] ++ [] from rfl)
    otherwise ⟨hl_67⟩ using hl_64 hl_65 hl_66
  group_none hinv4 hG with ⟨hl_64, hl_65, hl_66, hl_67⟩

theorem cases_0_17_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_17_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_to_smt.case_68 x_a0, EoCases.__eo_to_smt.case_69 x_a0, EoCases.__eo_to_smt.case_70 x_a0, EoCases.__eo_to_smt.case_71 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_68 x_a0 = none ∧ EoCases.__eo_to_smt.case_69 x_a0 = none ∧ EoCases.__eo_to_smt.case_70 x_a0 = none ∧ EoCases.__eo_to_smt.case_71 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_17_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  group_step with case_68_eo__24eo_5fto_5fsmt_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_68 x_a0, EoCases.__eo_to_smt.case_69 x_a0, EoCases.__eo_to_smt.case_70 x_a0, EoCases.__eo_to_smt.case_71 x_a0] = [] ++ [EoCases.__eo_to_smt.case_68 x_a0] ++ [EoCases.__eo_to_smt.case_69 x_a0, EoCases.__eo_to_smt.case_70 x_a0, EoCases.__eo_to_smt.case_71 x_a0] from rfl)
    otherwise ⟨hl_68⟩ using
  group_step with case_69_eo__24eo_5fto_5fsmt_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_68 x_a0, EoCases.__eo_to_smt.case_69 x_a0, EoCases.__eo_to_smt.case_70 x_a0, EoCases.__eo_to_smt.case_71 x_a0] = [EoCases.__eo_to_smt.case_68 x_a0] ++ [EoCases.__eo_to_smt.case_69 x_a0] ++ [EoCases.__eo_to_smt.case_70 x_a0, EoCases.__eo_to_smt.case_71 x_a0] from rfl)
    otherwise ⟨hl_69⟩ using hl_68
  group_step with case_70_eo__24eo_5fto_5fsmt_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_68 x_a0, EoCases.__eo_to_smt.case_69 x_a0, EoCases.__eo_to_smt.case_70 x_a0, EoCases.__eo_to_smt.case_71 x_a0] = [EoCases.__eo_to_smt.case_68 x_a0, EoCases.__eo_to_smt.case_69 x_a0] ++ [EoCases.__eo_to_smt.case_70 x_a0] ++ [EoCases.__eo_to_smt.case_71 x_a0] from rfl)
    otherwise ⟨hl_70⟩ using hl_68 hl_69
  group_step with case_71_eo__24eo_5fto_5fsmt_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_68 x_a0, EoCases.__eo_to_smt.case_69 x_a0, EoCases.__eo_to_smt.case_70 x_a0, EoCases.__eo_to_smt.case_71 x_a0] = [EoCases.__eo_to_smt.case_68 x_a0, EoCases.__eo_to_smt.case_69 x_a0, EoCases.__eo_to_smt.case_70 x_a0] ++ [EoCases.__eo_to_smt.case_71 x_a0] ++ [] from rfl)
    otherwise ⟨hl_71⟩ using hl_68 hl_69 hl_70
  group_none hinv4 hG with ⟨hl_68, hl_69, hl_70, hl_71⟩

theorem cases_0_18_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_18_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_to_smt.case_72 x_a0, EoCases.__eo_to_smt.case_73 x_a0, EoCases.__eo_to_smt.case_74 x_a0, EoCases.__eo_to_smt.case_75 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_72 x_a0 = none ∧ EoCases.__eo_to_smt.case_73 x_a0 = none ∧ EoCases.__eo_to_smt.case_74 x_a0 = none ∧ EoCases.__eo_to_smt.case_75 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_18_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  group_step with case_72_eo__24eo_5fto_5fsmt_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_72 x_a0, EoCases.__eo_to_smt.case_73 x_a0, EoCases.__eo_to_smt.case_74 x_a0, EoCases.__eo_to_smt.case_75 x_a0] = [] ++ [EoCases.__eo_to_smt.case_72 x_a0] ++ [EoCases.__eo_to_smt.case_73 x_a0, EoCases.__eo_to_smt.case_74 x_a0, EoCases.__eo_to_smt.case_75 x_a0] from rfl)
    otherwise ⟨hl_72⟩ using
  group_step with case_73_eo__24eo_5fto_5fsmt_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_72 x_a0, EoCases.__eo_to_smt.case_73 x_a0, EoCases.__eo_to_smt.case_74 x_a0, EoCases.__eo_to_smt.case_75 x_a0] = [EoCases.__eo_to_smt.case_72 x_a0] ++ [EoCases.__eo_to_smt.case_73 x_a0] ++ [EoCases.__eo_to_smt.case_74 x_a0, EoCases.__eo_to_smt.case_75 x_a0] from rfl)
    otherwise ⟨hl_73⟩ using hl_72
  group_step with case_74_eo__24eo_5fto_5fsmt_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_72 x_a0, EoCases.__eo_to_smt.case_73 x_a0, EoCases.__eo_to_smt.case_74 x_a0, EoCases.__eo_to_smt.case_75 x_a0] = [EoCases.__eo_to_smt.case_72 x_a0, EoCases.__eo_to_smt.case_73 x_a0] ++ [EoCases.__eo_to_smt.case_74 x_a0] ++ [EoCases.__eo_to_smt.case_75 x_a0] from rfl)
    otherwise ⟨hl_74⟩ using hl_72 hl_73
  group_step with case_75_eo__24eo_5fto_5fsmt_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_72 x_a0, EoCases.__eo_to_smt.case_73 x_a0, EoCases.__eo_to_smt.case_74 x_a0, EoCases.__eo_to_smt.case_75 x_a0] = [EoCases.__eo_to_smt.case_72 x_a0, EoCases.__eo_to_smt.case_73 x_a0, EoCases.__eo_to_smt.case_74 x_a0] ++ [EoCases.__eo_to_smt.case_75 x_a0] ++ [] from rfl)
    otherwise ⟨hl_75⟩ using hl_72 hl_73 hl_74
  group_none hinv4 hG with ⟨hl_72, hl_73, hl_74, hl_75⟩

theorem cases_0_19_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_19_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_to_smt.case_76 x_a0, EoCases.__eo_to_smt.case_77 x_a0, EoCases.__eo_to_smt.case_78 x_a0, EoCases.__eo_to_smt.case_79 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_76 x_a0 = none ∧ EoCases.__eo_to_smt.case_77 x_a0 = none ∧ EoCases.__eo_to_smt.case_78 x_a0 = none ∧ EoCases.__eo_to_smt.case_79 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_19_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  group_step with case_76_eo__24eo_5fto_5fsmt_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_76 x_a0, EoCases.__eo_to_smt.case_77 x_a0, EoCases.__eo_to_smt.case_78 x_a0, EoCases.__eo_to_smt.case_79 x_a0] = [] ++ [EoCases.__eo_to_smt.case_76 x_a0] ++ [EoCases.__eo_to_smt.case_77 x_a0, EoCases.__eo_to_smt.case_78 x_a0, EoCases.__eo_to_smt.case_79 x_a0] from rfl)
    otherwise ⟨hl_76⟩ using
  group_step with case_77_eo__24eo_5fto_5fsmt_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_76 x_a0, EoCases.__eo_to_smt.case_77 x_a0, EoCases.__eo_to_smt.case_78 x_a0, EoCases.__eo_to_smt.case_79 x_a0] = [EoCases.__eo_to_smt.case_76 x_a0] ++ [EoCases.__eo_to_smt.case_77 x_a0] ++ [EoCases.__eo_to_smt.case_78 x_a0, EoCases.__eo_to_smt.case_79 x_a0] from rfl)
    otherwise ⟨hl_77⟩ using hl_76
  group_step with case_78_eo__24eo_5fto_5fsmt_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_76 x_a0, EoCases.__eo_to_smt.case_77 x_a0, EoCases.__eo_to_smt.case_78 x_a0, EoCases.__eo_to_smt.case_79 x_a0] = [EoCases.__eo_to_smt.case_76 x_a0, EoCases.__eo_to_smt.case_77 x_a0] ++ [EoCases.__eo_to_smt.case_78 x_a0] ++ [EoCases.__eo_to_smt.case_79 x_a0] from rfl)
    otherwise ⟨hl_78⟩ using hl_76 hl_77
  group_step with case_79_eo__24eo_5fto_5fsmt_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_76 x_a0, EoCases.__eo_to_smt.case_77 x_a0, EoCases.__eo_to_smt.case_78 x_a0, EoCases.__eo_to_smt.case_79 x_a0] = [EoCases.__eo_to_smt.case_76 x_a0, EoCases.__eo_to_smt.case_77 x_a0, EoCases.__eo_to_smt.case_78 x_a0] ++ [EoCases.__eo_to_smt.case_79 x_a0] ++ [] from rfl)
    otherwise ⟨hl_79⟩ using hl_76 hl_77 hl_78
  group_none hinv4 hG with ⟨hl_76, hl_77, hl_78, hl_79⟩

theorem cases_0_20_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_20_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_to_smt.case_80 x_a0, EoCases.__eo_to_smt.case_81 x_a0, EoCases.__eo_to_smt.case_82 x_a0, EoCases.__eo_to_smt.case_83 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_80 x_a0 = none ∧ EoCases.__eo_to_smt.case_81 x_a0 = none ∧ EoCases.__eo_to_smt.case_82 x_a0 = none ∧ EoCases.__eo_to_smt.case_83 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_20_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  group_step with case_80_eo__24eo_5fto_5fsmt_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_80 x_a0, EoCases.__eo_to_smt.case_81 x_a0, EoCases.__eo_to_smt.case_82 x_a0, EoCases.__eo_to_smt.case_83 x_a0] = [] ++ [EoCases.__eo_to_smt.case_80 x_a0] ++ [EoCases.__eo_to_smt.case_81 x_a0, EoCases.__eo_to_smt.case_82 x_a0, EoCases.__eo_to_smt.case_83 x_a0] from rfl)
    otherwise ⟨hl_80⟩ using
  group_step with case_81_eo__24eo_5fto_5fsmt_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_80 x_a0, EoCases.__eo_to_smt.case_81 x_a0, EoCases.__eo_to_smt.case_82 x_a0, EoCases.__eo_to_smt.case_83 x_a0] = [EoCases.__eo_to_smt.case_80 x_a0] ++ [EoCases.__eo_to_smt.case_81 x_a0] ++ [EoCases.__eo_to_smt.case_82 x_a0, EoCases.__eo_to_smt.case_83 x_a0] from rfl)
    otherwise ⟨hl_81⟩ using hl_80
  group_step with case_82_eo__24eo_5fto_5fsmt_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_80 x_a0, EoCases.__eo_to_smt.case_81 x_a0, EoCases.__eo_to_smt.case_82 x_a0, EoCases.__eo_to_smt.case_83 x_a0] = [EoCases.__eo_to_smt.case_80 x_a0, EoCases.__eo_to_smt.case_81 x_a0] ++ [EoCases.__eo_to_smt.case_82 x_a0] ++ [EoCases.__eo_to_smt.case_83 x_a0] from rfl)
    otherwise ⟨hl_82⟩ using hl_80 hl_81
  group_step with case_83_eo__24eo_5fto_5fsmt_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_80 x_a0, EoCases.__eo_to_smt.case_81 x_a0, EoCases.__eo_to_smt.case_82 x_a0, EoCases.__eo_to_smt.case_83 x_a0] = [EoCases.__eo_to_smt.case_80 x_a0, EoCases.__eo_to_smt.case_81 x_a0, EoCases.__eo_to_smt.case_82 x_a0] ++ [EoCases.__eo_to_smt.case_83 x_a0] ++ [] from rfl)
    otherwise ⟨hl_83⟩ using hl_80 hl_81 hl_82
  group_none hinv4 hG with ⟨hl_80, hl_81, hl_82, hl_83⟩

theorem cases_0_21_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_21_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_to_smt.case_84 x_a0, EoCases.__eo_to_smt.case_85 x_a0, EoCases.__eo_to_smt.case_86 x_a0, EoCases.__eo_to_smt.case_87 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_84 x_a0 = none ∧ EoCases.__eo_to_smt.case_85 x_a0 = none ∧ EoCases.__eo_to_smt.case_86 x_a0 = none ∧ EoCases.__eo_to_smt.case_87 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_21_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  group_step with case_84_eo__24eo_5fto_5fsmt_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_84 x_a0, EoCases.__eo_to_smt.case_85 x_a0, EoCases.__eo_to_smt.case_86 x_a0, EoCases.__eo_to_smt.case_87 x_a0] = [] ++ [EoCases.__eo_to_smt.case_84 x_a0] ++ [EoCases.__eo_to_smt.case_85 x_a0, EoCases.__eo_to_smt.case_86 x_a0, EoCases.__eo_to_smt.case_87 x_a0] from rfl)
    otherwise ⟨hl_84⟩ using
  group_step with case_85_eo__24eo_5fto_5fsmt_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_84 x_a0, EoCases.__eo_to_smt.case_85 x_a0, EoCases.__eo_to_smt.case_86 x_a0, EoCases.__eo_to_smt.case_87 x_a0] = [EoCases.__eo_to_smt.case_84 x_a0] ++ [EoCases.__eo_to_smt.case_85 x_a0] ++ [EoCases.__eo_to_smt.case_86 x_a0, EoCases.__eo_to_smt.case_87 x_a0] from rfl)
    otherwise ⟨hl_85⟩ using hl_84
  group_step with case_86_eo__24eo_5fto_5fsmt_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_84 x_a0, EoCases.__eo_to_smt.case_85 x_a0, EoCases.__eo_to_smt.case_86 x_a0, EoCases.__eo_to_smt.case_87 x_a0] = [EoCases.__eo_to_smt.case_84 x_a0, EoCases.__eo_to_smt.case_85 x_a0] ++ [EoCases.__eo_to_smt.case_86 x_a0] ++ [EoCases.__eo_to_smt.case_87 x_a0] from rfl)
    otherwise ⟨hl_86⟩ using hl_84 hl_85
  group_step with case_87_eo__24eo_5fto_5fsmt_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_84 x_a0, EoCases.__eo_to_smt.case_85 x_a0, EoCases.__eo_to_smt.case_86 x_a0, EoCases.__eo_to_smt.case_87 x_a0] = [EoCases.__eo_to_smt.case_84 x_a0, EoCases.__eo_to_smt.case_85 x_a0, EoCases.__eo_to_smt.case_86 x_a0] ++ [EoCases.__eo_to_smt.case_87 x_a0] ++ [] from rfl)
    otherwise ⟨hl_87⟩ using hl_84 hl_85 hl_86
  group_none hinv4 hG with ⟨hl_84, hl_85, hl_86, hl_87⟩

theorem cases_0_22_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_22_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_to_smt.case_88 x_a0, EoCases.__eo_to_smt.case_89 x_a0, EoCases.__eo_to_smt.case_90 x_a0, EoCases.__eo_to_smt.case_91 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_88 x_a0 = none ∧ EoCases.__eo_to_smt.case_89 x_a0 = none ∧ EoCases.__eo_to_smt.case_90 x_a0 = none ∧ EoCases.__eo_to_smt.case_91 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_22_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  group_step with case_88_eo__24eo_5fto_5fsmt_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_88 x_a0, EoCases.__eo_to_smt.case_89 x_a0, EoCases.__eo_to_smt.case_90 x_a0, EoCases.__eo_to_smt.case_91 x_a0] = [] ++ [EoCases.__eo_to_smt.case_88 x_a0] ++ [EoCases.__eo_to_smt.case_89 x_a0, EoCases.__eo_to_smt.case_90 x_a0, EoCases.__eo_to_smt.case_91 x_a0] from rfl)
    otherwise ⟨hl_88⟩ using
  group_step with case_89_eo__24eo_5fto_5fsmt_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_88 x_a0, EoCases.__eo_to_smt.case_89 x_a0, EoCases.__eo_to_smt.case_90 x_a0, EoCases.__eo_to_smt.case_91 x_a0] = [EoCases.__eo_to_smt.case_88 x_a0] ++ [EoCases.__eo_to_smt.case_89 x_a0] ++ [EoCases.__eo_to_smt.case_90 x_a0, EoCases.__eo_to_smt.case_91 x_a0] from rfl)
    otherwise ⟨hl_89⟩ using hl_88
  group_step with case_90_eo__24eo_5fto_5fsmt_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_88 x_a0, EoCases.__eo_to_smt.case_89 x_a0, EoCases.__eo_to_smt.case_90 x_a0, EoCases.__eo_to_smt.case_91 x_a0] = [EoCases.__eo_to_smt.case_88 x_a0, EoCases.__eo_to_smt.case_89 x_a0] ++ [EoCases.__eo_to_smt.case_90 x_a0] ++ [EoCases.__eo_to_smt.case_91 x_a0] from rfl)
    otherwise ⟨hl_90⟩ using hl_88 hl_89
  group_step with case_91_eo__24eo_5fto_5fsmt_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_88 x_a0, EoCases.__eo_to_smt.case_89 x_a0, EoCases.__eo_to_smt.case_90 x_a0, EoCases.__eo_to_smt.case_91 x_a0] = [EoCases.__eo_to_smt.case_88 x_a0, EoCases.__eo_to_smt.case_89 x_a0, EoCases.__eo_to_smt.case_90 x_a0] ++ [EoCases.__eo_to_smt.case_91 x_a0] ++ [] from rfl)
    otherwise ⟨hl_91⟩ using hl_88 hl_89 hl_90
  group_none hinv4 hG with ⟨hl_88, hl_89, hl_90, hl_91⟩

theorem cases_0_23_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_23_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_to_smt.case_92 x_a0, EoCases.__eo_to_smt.case_93 x_a0, EoCases.__eo_to_smt.case_94 x_a0, EoCases.__eo_to_smt.case_95 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_92 x_a0 = none ∧ EoCases.__eo_to_smt.case_93 x_a0 = none ∧ EoCases.__eo_to_smt.case_94 x_a0 = none ∧ EoCases.__eo_to_smt.case_95 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_23_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  group_step with case_92_eo__24eo_5fto_5fsmt_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_92 x_a0, EoCases.__eo_to_smt.case_93 x_a0, EoCases.__eo_to_smt.case_94 x_a0, EoCases.__eo_to_smt.case_95 x_a0] = [] ++ [EoCases.__eo_to_smt.case_92 x_a0] ++ [EoCases.__eo_to_smt.case_93 x_a0, EoCases.__eo_to_smt.case_94 x_a0, EoCases.__eo_to_smt.case_95 x_a0] from rfl)
    otherwise ⟨hl_92⟩ using
  group_step with case_93_eo__24eo_5fto_5fsmt_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_92 x_a0, EoCases.__eo_to_smt.case_93 x_a0, EoCases.__eo_to_smt.case_94 x_a0, EoCases.__eo_to_smt.case_95 x_a0] = [EoCases.__eo_to_smt.case_92 x_a0] ++ [EoCases.__eo_to_smt.case_93 x_a0] ++ [EoCases.__eo_to_smt.case_94 x_a0, EoCases.__eo_to_smt.case_95 x_a0] from rfl)
    otherwise ⟨hl_93⟩ using hl_92
  group_step with case_94_eo__24eo_5fto_5fsmt_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_92 x_a0, EoCases.__eo_to_smt.case_93 x_a0, EoCases.__eo_to_smt.case_94 x_a0, EoCases.__eo_to_smt.case_95 x_a0] = [EoCases.__eo_to_smt.case_92 x_a0, EoCases.__eo_to_smt.case_93 x_a0] ++ [EoCases.__eo_to_smt.case_94 x_a0] ++ [EoCases.__eo_to_smt.case_95 x_a0] from rfl)
    otherwise ⟨hl_94⟩ using hl_92 hl_93
  group_step with case_95_eo__24eo_5fto_5fsmt_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_92 x_a0, EoCases.__eo_to_smt.case_93 x_a0, EoCases.__eo_to_smt.case_94 x_a0, EoCases.__eo_to_smt.case_95 x_a0] = [EoCases.__eo_to_smt.case_92 x_a0, EoCases.__eo_to_smt.case_93 x_a0, EoCases.__eo_to_smt.case_94 x_a0] ++ [EoCases.__eo_to_smt.case_95 x_a0] ++ [] from rfl)
    otherwise ⟨hl_95⟩ using hl_92 hl_93 hl_94
  group_none hinv4 hG with ⟨hl_92, hl_93, hl_94, hl_95⟩

theorem cases_0_24_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_24_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_to_smt.case_96 x_a0, EoCases.__eo_to_smt.case_97 x_a0, EoCases.__eo_to_smt.case_98 x_a0, EoCases.__eo_to_smt.case_99 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_96 x_a0 = none ∧ EoCases.__eo_to_smt.case_97 x_a0 = none ∧ EoCases.__eo_to_smt.case_98 x_a0 = none ∧ EoCases.__eo_to_smt.case_99 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_24_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  group_step with case_96_eo__24eo_5fto_5fsmt_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_96 x_a0, EoCases.__eo_to_smt.case_97 x_a0, EoCases.__eo_to_smt.case_98 x_a0, EoCases.__eo_to_smt.case_99 x_a0] = [] ++ [EoCases.__eo_to_smt.case_96 x_a0] ++ [EoCases.__eo_to_smt.case_97 x_a0, EoCases.__eo_to_smt.case_98 x_a0, EoCases.__eo_to_smt.case_99 x_a0] from rfl)
    otherwise ⟨hl_96⟩ using
  group_step with case_97_eo__24eo_5fto_5fsmt_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_96 x_a0, EoCases.__eo_to_smt.case_97 x_a0, EoCases.__eo_to_smt.case_98 x_a0, EoCases.__eo_to_smt.case_99 x_a0] = [EoCases.__eo_to_smt.case_96 x_a0] ++ [EoCases.__eo_to_smt.case_97 x_a0] ++ [EoCases.__eo_to_smt.case_98 x_a0, EoCases.__eo_to_smt.case_99 x_a0] from rfl)
    otherwise ⟨hl_97⟩ using hl_96
  group_step with case_98_eo__24eo_5fto_5fsmt_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_96 x_a0, EoCases.__eo_to_smt.case_97 x_a0, EoCases.__eo_to_smt.case_98 x_a0, EoCases.__eo_to_smt.case_99 x_a0] = [EoCases.__eo_to_smt.case_96 x_a0, EoCases.__eo_to_smt.case_97 x_a0] ++ [EoCases.__eo_to_smt.case_98 x_a0] ++ [EoCases.__eo_to_smt.case_99 x_a0] from rfl)
    otherwise ⟨hl_98⟩ using hl_96 hl_97
  group_step with case_99_eo__24eo_5fto_5fsmt_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_96 x_a0, EoCases.__eo_to_smt.case_97 x_a0, EoCases.__eo_to_smt.case_98 x_a0, EoCases.__eo_to_smt.case_99 x_a0] = [EoCases.__eo_to_smt.case_96 x_a0, EoCases.__eo_to_smt.case_97 x_a0, EoCases.__eo_to_smt.case_98 x_a0] ++ [EoCases.__eo_to_smt.case_99 x_a0] ++ [] from rfl)
    otherwise ⟨hl_99⟩ using hl_96 hl_97 hl_98
  group_none hinv4 hG with ⟨hl_96, hl_97, hl_98, hl_99⟩

theorem cases_0_25_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_25_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_to_smt.case_100 x_a0, EoCases.__eo_to_smt.case_101 x_a0, EoCases.__eo_to_smt.case_102 x_a0, EoCases.__eo_to_smt.case_103 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_100 x_a0 = none ∧ EoCases.__eo_to_smt.case_101 x_a0 = none ∧ EoCases.__eo_to_smt.case_102 x_a0 = none ∧ EoCases.__eo_to_smt.case_103 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_25_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  group_step with case_100_eo__24eo_5fto_5fsmt_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_100 x_a0, EoCases.__eo_to_smt.case_101 x_a0, EoCases.__eo_to_smt.case_102 x_a0, EoCases.__eo_to_smt.case_103 x_a0] = [] ++ [EoCases.__eo_to_smt.case_100 x_a0] ++ [EoCases.__eo_to_smt.case_101 x_a0, EoCases.__eo_to_smt.case_102 x_a0, EoCases.__eo_to_smt.case_103 x_a0] from rfl)
    otherwise ⟨hl_100⟩ using
  group_step with case_101_eo__24eo_5fto_5fsmt_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_100 x_a0, EoCases.__eo_to_smt.case_101 x_a0, EoCases.__eo_to_smt.case_102 x_a0, EoCases.__eo_to_smt.case_103 x_a0] = [EoCases.__eo_to_smt.case_100 x_a0] ++ [EoCases.__eo_to_smt.case_101 x_a0] ++ [EoCases.__eo_to_smt.case_102 x_a0, EoCases.__eo_to_smt.case_103 x_a0] from rfl)
    otherwise ⟨hl_101⟩ using hl_100
  group_step with case_102_eo__24eo_5fto_5fsmt_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_100 x_a0, EoCases.__eo_to_smt.case_101 x_a0, EoCases.__eo_to_smt.case_102 x_a0, EoCases.__eo_to_smt.case_103 x_a0] = [EoCases.__eo_to_smt.case_100 x_a0, EoCases.__eo_to_smt.case_101 x_a0] ++ [EoCases.__eo_to_smt.case_102 x_a0] ++ [EoCases.__eo_to_smt.case_103 x_a0] from rfl)
    otherwise ⟨hl_102⟩ using hl_100 hl_101
  group_step with case_103_eo__24eo_5fto_5fsmt_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_100 x_a0, EoCases.__eo_to_smt.case_101 x_a0, EoCases.__eo_to_smt.case_102 x_a0, EoCases.__eo_to_smt.case_103 x_a0] = [EoCases.__eo_to_smt.case_100 x_a0, EoCases.__eo_to_smt.case_101 x_a0, EoCases.__eo_to_smt.case_102 x_a0] ++ [EoCases.__eo_to_smt.case_103 x_a0] ++ [] from rfl)
    otherwise ⟨hl_103⟩ using hl_100 hl_101 hl_102
  group_none hinv4 hG with ⟨hl_100, hl_101, hl_102, hl_103⟩

theorem cases_0_26_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_26_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_to_smt.case_104 x_a0, EoCases.__eo_to_smt.case_105 x_a0, EoCases.__eo_to_smt.case_106 x_a0, EoCases.__eo_to_smt.case_107 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_104 x_a0 = none ∧ EoCases.__eo_to_smt.case_105 x_a0 = none ∧ EoCases.__eo_to_smt.case_106 x_a0 = none ∧ EoCases.__eo_to_smt.case_107 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_26_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  group_step with case_104_eo__24eo_5fto_5fsmt_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_104 x_a0, EoCases.__eo_to_smt.case_105 x_a0, EoCases.__eo_to_smt.case_106 x_a0, EoCases.__eo_to_smt.case_107 x_a0] = [] ++ [EoCases.__eo_to_smt.case_104 x_a0] ++ [EoCases.__eo_to_smt.case_105 x_a0, EoCases.__eo_to_smt.case_106 x_a0, EoCases.__eo_to_smt.case_107 x_a0] from rfl)
    otherwise ⟨hl_104⟩ using
  group_step with case_105_eo__24eo_5fto_5fsmt_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_104 x_a0, EoCases.__eo_to_smt.case_105 x_a0, EoCases.__eo_to_smt.case_106 x_a0, EoCases.__eo_to_smt.case_107 x_a0] = [EoCases.__eo_to_smt.case_104 x_a0] ++ [EoCases.__eo_to_smt.case_105 x_a0] ++ [EoCases.__eo_to_smt.case_106 x_a0, EoCases.__eo_to_smt.case_107 x_a0] from rfl)
    otherwise ⟨hl_105⟩ using hl_104
  group_step with case_106_eo__24eo_5fto_5fsmt_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_104 x_a0, EoCases.__eo_to_smt.case_105 x_a0, EoCases.__eo_to_smt.case_106 x_a0, EoCases.__eo_to_smt.case_107 x_a0] = [EoCases.__eo_to_smt.case_104 x_a0, EoCases.__eo_to_smt.case_105 x_a0] ++ [EoCases.__eo_to_smt.case_106 x_a0] ++ [EoCases.__eo_to_smt.case_107 x_a0] from rfl)
    otherwise ⟨hl_106⟩ using hl_104 hl_105
  group_step with case_107_eo__24eo_5fto_5fsmt_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_104 x_a0, EoCases.__eo_to_smt.case_105 x_a0, EoCases.__eo_to_smt.case_106 x_a0, EoCases.__eo_to_smt.case_107 x_a0] = [EoCases.__eo_to_smt.case_104 x_a0, EoCases.__eo_to_smt.case_105 x_a0, EoCases.__eo_to_smt.case_106 x_a0] ++ [EoCases.__eo_to_smt.case_107 x_a0] ++ [] from rfl)
    otherwise ⟨hl_107⟩ using hl_104 hl_105 hl_106
  group_none hinv4 hG with ⟨hl_104, hl_105, hl_106, hl_107⟩

theorem cases_0_27_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_27_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_to_smt.case_108 x_a0, EoCases.__eo_to_smt.case_109 x_a0, EoCases.__eo_to_smt.case_110 x_a0, EoCases.__eo_to_smt.case_111 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_108 x_a0 = none ∧ EoCases.__eo_to_smt.case_109 x_a0 = none ∧ EoCases.__eo_to_smt.case_110 x_a0 = none ∧ EoCases.__eo_to_smt.case_111 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_27_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  group_step with case_108_eo__24eo_5fto_5fsmt_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_108 x_a0, EoCases.__eo_to_smt.case_109 x_a0, EoCases.__eo_to_smt.case_110 x_a0, EoCases.__eo_to_smt.case_111 x_a0] = [] ++ [EoCases.__eo_to_smt.case_108 x_a0] ++ [EoCases.__eo_to_smt.case_109 x_a0, EoCases.__eo_to_smt.case_110 x_a0, EoCases.__eo_to_smt.case_111 x_a0] from rfl)
    otherwise ⟨hl_108⟩ using
  group_step with case_109_eo__24eo_5fto_5fsmt_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_108 x_a0, EoCases.__eo_to_smt.case_109 x_a0, EoCases.__eo_to_smt.case_110 x_a0, EoCases.__eo_to_smt.case_111 x_a0] = [EoCases.__eo_to_smt.case_108 x_a0] ++ [EoCases.__eo_to_smt.case_109 x_a0] ++ [EoCases.__eo_to_smt.case_110 x_a0, EoCases.__eo_to_smt.case_111 x_a0] from rfl)
    otherwise ⟨hl_109⟩ using hl_108
  group_step with case_110_eo__24eo_5fto_5fsmt_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_108 x_a0, EoCases.__eo_to_smt.case_109 x_a0, EoCases.__eo_to_smt.case_110 x_a0, EoCases.__eo_to_smt.case_111 x_a0] = [EoCases.__eo_to_smt.case_108 x_a0, EoCases.__eo_to_smt.case_109 x_a0] ++ [EoCases.__eo_to_smt.case_110 x_a0] ++ [EoCases.__eo_to_smt.case_111 x_a0] from rfl)
    otherwise ⟨hl_110⟩ using hl_108 hl_109
  group_step with case_111_eo__24eo_5fto_5fsmt_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_108 x_a0, EoCases.__eo_to_smt.case_109 x_a0, EoCases.__eo_to_smt.case_110 x_a0, EoCases.__eo_to_smt.case_111 x_a0] = [EoCases.__eo_to_smt.case_108 x_a0, EoCases.__eo_to_smt.case_109 x_a0, EoCases.__eo_to_smt.case_110 x_a0] ++ [EoCases.__eo_to_smt.case_111 x_a0] ++ [] from rfl)
    otherwise ⟨hl_111⟩ using hl_108 hl_109 hl_110
  group_none hinv4 hG with ⟨hl_108, hl_109, hl_110, hl_111⟩

theorem cases_0_28_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_28_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_to_smt.case_112 x_a0, EoCases.__eo_to_smt.case_113 x_a0, EoCases.__eo_to_smt.case_114 x_a0, EoCases.__eo_to_smt.case_115 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_112 x_a0 = none ∧ EoCases.__eo_to_smt.case_113 x_a0 = none ∧ EoCases.__eo_to_smt.case_114 x_a0 = none ∧ EoCases.__eo_to_smt.case_115 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_28_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  group_step with case_112_eo__24eo_5fto_5fsmt_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_112 x_a0, EoCases.__eo_to_smt.case_113 x_a0, EoCases.__eo_to_smt.case_114 x_a0, EoCases.__eo_to_smt.case_115 x_a0] = [] ++ [EoCases.__eo_to_smt.case_112 x_a0] ++ [EoCases.__eo_to_smt.case_113 x_a0, EoCases.__eo_to_smt.case_114 x_a0, EoCases.__eo_to_smt.case_115 x_a0] from rfl)
    otherwise ⟨hl_112⟩ using
  group_step with case_113_eo__24eo_5fto_5fsmt_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_112 x_a0, EoCases.__eo_to_smt.case_113 x_a0, EoCases.__eo_to_smt.case_114 x_a0, EoCases.__eo_to_smt.case_115 x_a0] = [EoCases.__eo_to_smt.case_112 x_a0] ++ [EoCases.__eo_to_smt.case_113 x_a0] ++ [EoCases.__eo_to_smt.case_114 x_a0, EoCases.__eo_to_smt.case_115 x_a0] from rfl)
    otherwise ⟨hl_113⟩ using hl_112
  group_step with case_114_eo__24eo_5fto_5fsmt_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_112 x_a0, EoCases.__eo_to_smt.case_113 x_a0, EoCases.__eo_to_smt.case_114 x_a0, EoCases.__eo_to_smt.case_115 x_a0] = [EoCases.__eo_to_smt.case_112 x_a0, EoCases.__eo_to_smt.case_113 x_a0] ++ [EoCases.__eo_to_smt.case_114 x_a0] ++ [EoCases.__eo_to_smt.case_115 x_a0] from rfl)
    otherwise ⟨hl_114⟩ using hl_112 hl_113
  group_step with case_115_eo__24eo_5fto_5fsmt_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_112 x_a0, EoCases.__eo_to_smt.case_113 x_a0, EoCases.__eo_to_smt.case_114 x_a0, EoCases.__eo_to_smt.case_115 x_a0] = [EoCases.__eo_to_smt.case_112 x_a0, EoCases.__eo_to_smt.case_113 x_a0, EoCases.__eo_to_smt.case_114 x_a0] ++ [EoCases.__eo_to_smt.case_115 x_a0] ++ [] from rfl)
    otherwise ⟨hl_115⟩ using hl_112 hl_113 hl_114
  group_none hinv4 hG with ⟨hl_112, hl_113, hl_114, hl_115⟩

theorem cases_0_29_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_29_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_to_smt.case_116 x_a0, EoCases.__eo_to_smt.case_117 x_a0, EoCases.__eo_to_smt.case_118 x_a0, EoCases.__eo_to_smt.case_119 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_116 x_a0 = none ∧ EoCases.__eo_to_smt.case_117 x_a0 = none ∧ EoCases.__eo_to_smt.case_118 x_a0 = none ∧ EoCases.__eo_to_smt.case_119 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_29_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  group_step with case_116_eo__24eo_5fto_5fsmt_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_116 x_a0, EoCases.__eo_to_smt.case_117 x_a0, EoCases.__eo_to_smt.case_118 x_a0, EoCases.__eo_to_smt.case_119 x_a0] = [] ++ [EoCases.__eo_to_smt.case_116 x_a0] ++ [EoCases.__eo_to_smt.case_117 x_a0, EoCases.__eo_to_smt.case_118 x_a0, EoCases.__eo_to_smt.case_119 x_a0] from rfl)
    otherwise ⟨hl_116⟩ using
  group_step with case_117_eo__24eo_5fto_5fsmt_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_116 x_a0, EoCases.__eo_to_smt.case_117 x_a0, EoCases.__eo_to_smt.case_118 x_a0, EoCases.__eo_to_smt.case_119 x_a0] = [EoCases.__eo_to_smt.case_116 x_a0] ++ [EoCases.__eo_to_smt.case_117 x_a0] ++ [EoCases.__eo_to_smt.case_118 x_a0, EoCases.__eo_to_smt.case_119 x_a0] from rfl)
    otherwise ⟨hl_117⟩ using hl_116
  group_step with case_118_eo__24eo_5fto_5fsmt_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_116 x_a0, EoCases.__eo_to_smt.case_117 x_a0, EoCases.__eo_to_smt.case_118 x_a0, EoCases.__eo_to_smt.case_119 x_a0] = [EoCases.__eo_to_smt.case_116 x_a0, EoCases.__eo_to_smt.case_117 x_a0] ++ [EoCases.__eo_to_smt.case_118 x_a0] ++ [EoCases.__eo_to_smt.case_119 x_a0] from rfl)
    otherwise ⟨hl_118⟩ using hl_116 hl_117
  group_step with case_119_eo__24eo_5fto_5fsmt_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_116 x_a0, EoCases.__eo_to_smt.case_117 x_a0, EoCases.__eo_to_smt.case_118 x_a0, EoCases.__eo_to_smt.case_119 x_a0] = [EoCases.__eo_to_smt.case_116 x_a0, EoCases.__eo_to_smt.case_117 x_a0, EoCases.__eo_to_smt.case_118 x_a0] ++ [EoCases.__eo_to_smt.case_119 x_a0] ++ [] from rfl)
    otherwise ⟨hl_119⟩ using hl_116 hl_117 hl_118
  group_none hinv4 hG with ⟨hl_116, hl_117, hl_118, hl_119⟩

theorem cases_0_30_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_30_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_to_smt.case_120 x_a0, EoCases.__eo_to_smt.case_121 x_a0, EoCases.__eo_to_smt.case_122 x_a0, EoCases.__eo_to_smt.case_123 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_120 x_a0 = none ∧ EoCases.__eo_to_smt.case_121 x_a0 = none ∧ EoCases.__eo_to_smt.case_122 x_a0 = none ∧ EoCases.__eo_to_smt.case_123 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_30_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  group_step with case_120_eo__24eo_5fto_5fsmt_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_120 x_a0, EoCases.__eo_to_smt.case_121 x_a0, EoCases.__eo_to_smt.case_122 x_a0, EoCases.__eo_to_smt.case_123 x_a0] = [] ++ [EoCases.__eo_to_smt.case_120 x_a0] ++ [EoCases.__eo_to_smt.case_121 x_a0, EoCases.__eo_to_smt.case_122 x_a0, EoCases.__eo_to_smt.case_123 x_a0] from rfl)
    otherwise ⟨hl_120⟩ using
  group_step with case_121_eo__24eo_5fto_5fsmt_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_120 x_a0, EoCases.__eo_to_smt.case_121 x_a0, EoCases.__eo_to_smt.case_122 x_a0, EoCases.__eo_to_smt.case_123 x_a0] = [EoCases.__eo_to_smt.case_120 x_a0] ++ [EoCases.__eo_to_smt.case_121 x_a0] ++ [EoCases.__eo_to_smt.case_122 x_a0, EoCases.__eo_to_smt.case_123 x_a0] from rfl)
    otherwise ⟨hl_121⟩ using hl_120
  group_step with case_122_eo__24eo_5fto_5fsmt_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_120 x_a0, EoCases.__eo_to_smt.case_121 x_a0, EoCases.__eo_to_smt.case_122 x_a0, EoCases.__eo_to_smt.case_123 x_a0] = [EoCases.__eo_to_smt.case_120 x_a0, EoCases.__eo_to_smt.case_121 x_a0] ++ [EoCases.__eo_to_smt.case_122 x_a0] ++ [EoCases.__eo_to_smt.case_123 x_a0] from rfl)
    otherwise ⟨hl_122⟩ using hl_120 hl_121
  group_step with case_123_eo__24eo_5fto_5fsmt_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_120 x_a0, EoCases.__eo_to_smt.case_121 x_a0, EoCases.__eo_to_smt.case_122 x_a0, EoCases.__eo_to_smt.case_123 x_a0] = [EoCases.__eo_to_smt.case_120 x_a0, EoCases.__eo_to_smt.case_121 x_a0, EoCases.__eo_to_smt.case_122 x_a0] ++ [EoCases.__eo_to_smt.case_123 x_a0] ++ [] from rfl)
    otherwise ⟨hl_123⟩ using hl_120 hl_121 hl_122
  group_none hinv4 hG with ⟨hl_120, hl_121, hl_122, hl_123⟩

theorem cases_0_31_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_31_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_to_smt.case_124 x_a0, EoCases.__eo_to_smt.case_125 x_a0, EoCases.__eo_to_smt.case_126 x_a0, EoCases.__eo_to_smt.case_127 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_124 x_a0 = none ∧ EoCases.__eo_to_smt.case_125 x_a0 = none ∧ EoCases.__eo_to_smt.case_126 x_a0 = none ∧ EoCases.__eo_to_smt.case_127 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_31_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  group_step with case_124_eo__24eo_5fto_5fsmt_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_124 x_a0, EoCases.__eo_to_smt.case_125 x_a0, EoCases.__eo_to_smt.case_126 x_a0, EoCases.__eo_to_smt.case_127 x_a0] = [] ++ [EoCases.__eo_to_smt.case_124 x_a0] ++ [EoCases.__eo_to_smt.case_125 x_a0, EoCases.__eo_to_smt.case_126 x_a0, EoCases.__eo_to_smt.case_127 x_a0] from rfl)
    otherwise ⟨hl_124⟩ using
  group_step with case_125_eo__24eo_5fto_5fsmt_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_124 x_a0, EoCases.__eo_to_smt.case_125 x_a0, EoCases.__eo_to_smt.case_126 x_a0, EoCases.__eo_to_smt.case_127 x_a0] = [EoCases.__eo_to_smt.case_124 x_a0] ++ [EoCases.__eo_to_smt.case_125 x_a0] ++ [EoCases.__eo_to_smt.case_126 x_a0, EoCases.__eo_to_smt.case_127 x_a0] from rfl)
    otherwise ⟨hl_125⟩ using hl_124
  group_step with case_126_eo__24eo_5fto_5fsmt_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_124 x_a0, EoCases.__eo_to_smt.case_125 x_a0, EoCases.__eo_to_smt.case_126 x_a0, EoCases.__eo_to_smt.case_127 x_a0] = [EoCases.__eo_to_smt.case_124 x_a0, EoCases.__eo_to_smt.case_125 x_a0] ++ [EoCases.__eo_to_smt.case_126 x_a0] ++ [EoCases.__eo_to_smt.case_127 x_a0] from rfl)
    otherwise ⟨hl_126⟩ using hl_124 hl_125
  group_step with case_127_eo__24eo_5fto_5fsmt_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_124 x_a0, EoCases.__eo_to_smt.case_125 x_a0, EoCases.__eo_to_smt.case_126 x_a0, EoCases.__eo_to_smt.case_127 x_a0] = [EoCases.__eo_to_smt.case_124 x_a0, EoCases.__eo_to_smt.case_125 x_a0, EoCases.__eo_to_smt.case_126 x_a0] ++ [EoCases.__eo_to_smt.case_127 x_a0] ++ [] from rfl)
    otherwise ⟨hl_127⟩ using hl_124 hl_125 hl_126
  group_none hinv4 hG with ⟨hl_124, hl_125, hl_126, hl_127⟩

theorem cases_0_32_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_32_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_to_smt.case_128 x_a0, EoCases.__eo_to_smt.case_129 x_a0, EoCases.__eo_to_smt.case_130 x_a0, EoCases.__eo_to_smt.case_131 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_128 x_a0 = none ∧ EoCases.__eo_to_smt.case_129 x_a0 = none ∧ EoCases.__eo_to_smt.case_130 x_a0 = none ∧ EoCases.__eo_to_smt.case_131 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_32_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  group_step with case_128_eo__24eo_5fto_5fsmt_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_128 x_a0, EoCases.__eo_to_smt.case_129 x_a0, EoCases.__eo_to_smt.case_130 x_a0, EoCases.__eo_to_smt.case_131 x_a0] = [] ++ [EoCases.__eo_to_smt.case_128 x_a0] ++ [EoCases.__eo_to_smt.case_129 x_a0, EoCases.__eo_to_smt.case_130 x_a0, EoCases.__eo_to_smt.case_131 x_a0] from rfl)
    otherwise ⟨hl_128⟩ using
  group_step with case_129_eo__24eo_5fto_5fsmt_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_128 x_a0, EoCases.__eo_to_smt.case_129 x_a0, EoCases.__eo_to_smt.case_130 x_a0, EoCases.__eo_to_smt.case_131 x_a0] = [EoCases.__eo_to_smt.case_128 x_a0] ++ [EoCases.__eo_to_smt.case_129 x_a0] ++ [EoCases.__eo_to_smt.case_130 x_a0, EoCases.__eo_to_smt.case_131 x_a0] from rfl)
    otherwise ⟨hl_129⟩ using hl_128
  group_step with case_130_eo__24eo_5fto_5fsmt_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_128 x_a0, EoCases.__eo_to_smt.case_129 x_a0, EoCases.__eo_to_smt.case_130 x_a0, EoCases.__eo_to_smt.case_131 x_a0] = [EoCases.__eo_to_smt.case_128 x_a0, EoCases.__eo_to_smt.case_129 x_a0] ++ [EoCases.__eo_to_smt.case_130 x_a0] ++ [EoCases.__eo_to_smt.case_131 x_a0] from rfl)
    otherwise ⟨hl_130⟩ using hl_128 hl_129
  group_step with case_131_eo__24eo_5fto_5fsmt_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_128 x_a0, EoCases.__eo_to_smt.case_129 x_a0, EoCases.__eo_to_smt.case_130 x_a0, EoCases.__eo_to_smt.case_131 x_a0] = [EoCases.__eo_to_smt.case_128 x_a0, EoCases.__eo_to_smt.case_129 x_a0, EoCases.__eo_to_smt.case_130 x_a0] ++ [EoCases.__eo_to_smt.case_131 x_a0] ++ [] from rfl)
    otherwise ⟨hl_131⟩ using hl_128 hl_129 hl_130
  group_none hinv4 hG with ⟨hl_128, hl_129, hl_130, hl_131⟩

theorem cases_0_33_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_33_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_to_smt.case_132 x_a0, EoCases.__eo_to_smt.case_133 x_a0, EoCases.__eo_to_smt.case_134 x_a0, EoCases.__eo_to_smt.case_135 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_132 x_a0 = none ∧ EoCases.__eo_to_smt.case_133 x_a0 = none ∧ EoCases.__eo_to_smt.case_134 x_a0 = none ∧ EoCases.__eo_to_smt.case_135 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_33_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  group_step with case_132_eo__24eo_5fto_5fsmt_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_132 x_a0, EoCases.__eo_to_smt.case_133 x_a0, EoCases.__eo_to_smt.case_134 x_a0, EoCases.__eo_to_smt.case_135 x_a0] = [] ++ [EoCases.__eo_to_smt.case_132 x_a0] ++ [EoCases.__eo_to_smt.case_133 x_a0, EoCases.__eo_to_smt.case_134 x_a0, EoCases.__eo_to_smt.case_135 x_a0] from rfl)
    otherwise ⟨hl_132⟩ using
  group_step with case_133_eo__24eo_5fto_5fsmt_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_132 x_a0, EoCases.__eo_to_smt.case_133 x_a0, EoCases.__eo_to_smt.case_134 x_a0, EoCases.__eo_to_smt.case_135 x_a0] = [EoCases.__eo_to_smt.case_132 x_a0] ++ [EoCases.__eo_to_smt.case_133 x_a0] ++ [EoCases.__eo_to_smt.case_134 x_a0, EoCases.__eo_to_smt.case_135 x_a0] from rfl)
    otherwise ⟨hl_133⟩ using hl_132
  group_step with case_134_eo__24eo_5fto_5fsmt_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_132 x_a0, EoCases.__eo_to_smt.case_133 x_a0, EoCases.__eo_to_smt.case_134 x_a0, EoCases.__eo_to_smt.case_135 x_a0] = [EoCases.__eo_to_smt.case_132 x_a0, EoCases.__eo_to_smt.case_133 x_a0] ++ [EoCases.__eo_to_smt.case_134 x_a0] ++ [EoCases.__eo_to_smt.case_135 x_a0] from rfl)
    otherwise ⟨hl_134⟩ using hl_132 hl_133
  group_step with case_135_eo__24eo_5fto_5fsmt_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_132 x_a0, EoCases.__eo_to_smt.case_133 x_a0, EoCases.__eo_to_smt.case_134 x_a0, EoCases.__eo_to_smt.case_135 x_a0] = [EoCases.__eo_to_smt.case_132 x_a0, EoCases.__eo_to_smt.case_133 x_a0, EoCases.__eo_to_smt.case_134 x_a0] ++ [EoCases.__eo_to_smt.case_135 x_a0] ++ [] from rfl)
    otherwise ⟨hl_135⟩ using hl_132 hl_133 hl_134
  group_none hinv4 hG with ⟨hl_132, hl_133, hl_134, hl_135⟩

theorem cases_0_34_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_34_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_to_smt.case_136 x_a0, EoCases.__eo_to_smt.case_137 x_a0, EoCases.__eo_to_smt.case_138 x_a0, EoCases.__eo_to_smt.case_139 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_136 x_a0 = none ∧ EoCases.__eo_to_smt.case_137 x_a0 = none ∧ EoCases.__eo_to_smt.case_138 x_a0 = none ∧ EoCases.__eo_to_smt.case_139 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_34_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  group_step with case_136_eo__24eo_5fto_5fsmt_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_136 x_a0, EoCases.__eo_to_smt.case_137 x_a0, EoCases.__eo_to_smt.case_138 x_a0, EoCases.__eo_to_smt.case_139 x_a0] = [] ++ [EoCases.__eo_to_smt.case_136 x_a0] ++ [EoCases.__eo_to_smt.case_137 x_a0, EoCases.__eo_to_smt.case_138 x_a0, EoCases.__eo_to_smt.case_139 x_a0] from rfl)
    otherwise ⟨hl_136⟩ using
  group_step with case_137_eo__24eo_5fto_5fsmt_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_136 x_a0, EoCases.__eo_to_smt.case_137 x_a0, EoCases.__eo_to_smt.case_138 x_a0, EoCases.__eo_to_smt.case_139 x_a0] = [EoCases.__eo_to_smt.case_136 x_a0] ++ [EoCases.__eo_to_smt.case_137 x_a0] ++ [EoCases.__eo_to_smt.case_138 x_a0, EoCases.__eo_to_smt.case_139 x_a0] from rfl)
    otherwise ⟨hl_137⟩ using hl_136
  group_step with case_138_eo__24eo_5fto_5fsmt_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_136 x_a0, EoCases.__eo_to_smt.case_137 x_a0, EoCases.__eo_to_smt.case_138 x_a0, EoCases.__eo_to_smt.case_139 x_a0] = [EoCases.__eo_to_smt.case_136 x_a0, EoCases.__eo_to_smt.case_137 x_a0] ++ [EoCases.__eo_to_smt.case_138 x_a0] ++ [EoCases.__eo_to_smt.case_139 x_a0] from rfl)
    otherwise ⟨hl_138⟩ using hl_136 hl_137
  group_step with case_139_eo__24eo_5fto_5fsmt_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_136 x_a0, EoCases.__eo_to_smt.case_137 x_a0, EoCases.__eo_to_smt.case_138 x_a0, EoCases.__eo_to_smt.case_139 x_a0] = [EoCases.__eo_to_smt.case_136 x_a0, EoCases.__eo_to_smt.case_137 x_a0, EoCases.__eo_to_smt.case_138 x_a0] ++ [EoCases.__eo_to_smt.case_139 x_a0] ++ [] from rfl)
    otherwise ⟨hl_139⟩ using hl_136 hl_137 hl_138
  group_none hinv4 hG with ⟨hl_136, hl_137, hl_138, hl_139⟩

theorem cases_0_35_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_35_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_to_smt.case_140 x_a0, EoCases.__eo_to_smt.case_141 x_a0, EoCases.__eo_to_smt.case_142 x_a0, EoCases.__eo_to_smt.case_143 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_140 x_a0 = none ∧ EoCases.__eo_to_smt.case_141 x_a0 = none ∧ EoCases.__eo_to_smt.case_142 x_a0 = none ∧ EoCases.__eo_to_smt.case_143 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_35_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  group_step with case_140_eo__24eo_5fto_5fsmt_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_140 x_a0, EoCases.__eo_to_smt.case_141 x_a0, EoCases.__eo_to_smt.case_142 x_a0, EoCases.__eo_to_smt.case_143 x_a0] = [] ++ [EoCases.__eo_to_smt.case_140 x_a0] ++ [EoCases.__eo_to_smt.case_141 x_a0, EoCases.__eo_to_smt.case_142 x_a0, EoCases.__eo_to_smt.case_143 x_a0] from rfl)
    otherwise ⟨hl_140⟩ using
  group_step with case_141_eo__24eo_5fto_5fsmt_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_140 x_a0, EoCases.__eo_to_smt.case_141 x_a0, EoCases.__eo_to_smt.case_142 x_a0, EoCases.__eo_to_smt.case_143 x_a0] = [EoCases.__eo_to_smt.case_140 x_a0] ++ [EoCases.__eo_to_smt.case_141 x_a0] ++ [EoCases.__eo_to_smt.case_142 x_a0, EoCases.__eo_to_smt.case_143 x_a0] from rfl)
    otherwise ⟨hl_141⟩ using hl_140
  group_step with case_142_eo__24eo_5fto_5fsmt_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_140 x_a0, EoCases.__eo_to_smt.case_141 x_a0, EoCases.__eo_to_smt.case_142 x_a0, EoCases.__eo_to_smt.case_143 x_a0] = [EoCases.__eo_to_smt.case_140 x_a0, EoCases.__eo_to_smt.case_141 x_a0] ++ [EoCases.__eo_to_smt.case_142 x_a0] ++ [EoCases.__eo_to_smt.case_143 x_a0] from rfl)
    otherwise ⟨hl_142⟩ using hl_140 hl_141
  group_step with case_143_eo__24eo_5fto_5fsmt_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_140 x_a0, EoCases.__eo_to_smt.case_141 x_a0, EoCases.__eo_to_smt.case_142 x_a0, EoCases.__eo_to_smt.case_143 x_a0] = [EoCases.__eo_to_smt.case_140 x_a0, EoCases.__eo_to_smt.case_141 x_a0, EoCases.__eo_to_smt.case_142 x_a0] ++ [EoCases.__eo_to_smt.case_143 x_a0] ++ [] from rfl)
    otherwise ⟨hl_143⟩ using hl_140 hl_141 hl_142
  group_none hinv4 hG with ⟨hl_140, hl_141, hl_142, hl_143⟩

theorem cases_0_36_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_36_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_to_smt.case_144 x_a0, EoCases.__eo_to_smt.case_145 x_a0, EoCases.__eo_to_smt.case_146 x_a0, EoCases.__eo_to_smt.case_147 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_144 x_a0 = none ∧ EoCases.__eo_to_smt.case_145 x_a0 = none ∧ EoCases.__eo_to_smt.case_146 x_a0 = none ∧ EoCases.__eo_to_smt.case_147 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_36_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  group_step with case_144_eo__24eo_5fto_5fsmt_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_144 x_a0, EoCases.__eo_to_smt.case_145 x_a0, EoCases.__eo_to_smt.case_146 x_a0, EoCases.__eo_to_smt.case_147 x_a0] = [] ++ [EoCases.__eo_to_smt.case_144 x_a0] ++ [EoCases.__eo_to_smt.case_145 x_a0, EoCases.__eo_to_smt.case_146 x_a0, EoCases.__eo_to_smt.case_147 x_a0] from rfl)
    otherwise ⟨hl_144⟩ using
  group_step with case_145_eo__24eo_5fto_5fsmt_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_144 x_a0, EoCases.__eo_to_smt.case_145 x_a0, EoCases.__eo_to_smt.case_146 x_a0, EoCases.__eo_to_smt.case_147 x_a0] = [EoCases.__eo_to_smt.case_144 x_a0] ++ [EoCases.__eo_to_smt.case_145 x_a0] ++ [EoCases.__eo_to_smt.case_146 x_a0, EoCases.__eo_to_smt.case_147 x_a0] from rfl)
    otherwise ⟨hl_145⟩ using hl_144
  group_step with case_146_eo__24eo_5fto_5fsmt_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_144 x_a0, EoCases.__eo_to_smt.case_145 x_a0, EoCases.__eo_to_smt.case_146 x_a0, EoCases.__eo_to_smt.case_147 x_a0] = [EoCases.__eo_to_smt.case_144 x_a0, EoCases.__eo_to_smt.case_145 x_a0] ++ [EoCases.__eo_to_smt.case_146 x_a0] ++ [EoCases.__eo_to_smt.case_147 x_a0] from rfl)
    otherwise ⟨hl_146⟩ using hl_144 hl_145
  group_step with case_147_eo__24eo_5fto_5fsmt_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_144 x_a0, EoCases.__eo_to_smt.case_145 x_a0, EoCases.__eo_to_smt.case_146 x_a0, EoCases.__eo_to_smt.case_147 x_a0] = [EoCases.__eo_to_smt.case_144 x_a0, EoCases.__eo_to_smt.case_145 x_a0, EoCases.__eo_to_smt.case_146 x_a0] ++ [EoCases.__eo_to_smt.case_147 x_a0] ++ [] from rfl)
    otherwise ⟨hl_147⟩ using hl_144 hl_145 hl_146
  group_none hinv4 hG with ⟨hl_144, hl_145, hl_146, hl_147⟩

theorem cases_0_37_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_37_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_to_smt.case_148 x_a0, EoCases.__eo_to_smt.case_149 x_a0, EoCases.__eo_to_smt.case_150 x_a0, EoCases.__eo_to_smt.case_151 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_148 x_a0 = none ∧ EoCases.__eo_to_smt.case_149 x_a0 = none ∧ EoCases.__eo_to_smt.case_150 x_a0 = none ∧ EoCases.__eo_to_smt.case_151 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_37_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  group_step with case_148_eo__24eo_5fto_5fsmt_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_148 x_a0, EoCases.__eo_to_smt.case_149 x_a0, EoCases.__eo_to_smt.case_150 x_a0, EoCases.__eo_to_smt.case_151 x_a0] = [] ++ [EoCases.__eo_to_smt.case_148 x_a0] ++ [EoCases.__eo_to_smt.case_149 x_a0, EoCases.__eo_to_smt.case_150 x_a0, EoCases.__eo_to_smt.case_151 x_a0] from rfl)
    otherwise ⟨hl_148⟩ using
  group_step with case_149_eo__24eo_5fto_5fsmt_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_148 x_a0, EoCases.__eo_to_smt.case_149 x_a0, EoCases.__eo_to_smt.case_150 x_a0, EoCases.__eo_to_smt.case_151 x_a0] = [EoCases.__eo_to_smt.case_148 x_a0] ++ [EoCases.__eo_to_smt.case_149 x_a0] ++ [EoCases.__eo_to_smt.case_150 x_a0, EoCases.__eo_to_smt.case_151 x_a0] from rfl)
    otherwise ⟨hl_149⟩ using hl_148
  group_step with case_150_eo__24eo_5fto_5fsmt_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_148 x_a0, EoCases.__eo_to_smt.case_149 x_a0, EoCases.__eo_to_smt.case_150 x_a0, EoCases.__eo_to_smt.case_151 x_a0] = [EoCases.__eo_to_smt.case_148 x_a0, EoCases.__eo_to_smt.case_149 x_a0] ++ [EoCases.__eo_to_smt.case_150 x_a0] ++ [EoCases.__eo_to_smt.case_151 x_a0] from rfl)
    otherwise ⟨hl_150⟩ using hl_148 hl_149
  group_step with case_151_eo__24eo_5fto_5fsmt_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_148 x_a0, EoCases.__eo_to_smt.case_149 x_a0, EoCases.__eo_to_smt.case_150 x_a0, EoCases.__eo_to_smt.case_151 x_a0] = [EoCases.__eo_to_smt.case_148 x_a0, EoCases.__eo_to_smt.case_149 x_a0, EoCases.__eo_to_smt.case_150 x_a0] ++ [EoCases.__eo_to_smt.case_151 x_a0] ++ [] from rfl)
    otherwise ⟨hl_151⟩ using hl_148 hl_149 hl_150
  group_none hinv4 hG with ⟨hl_148, hl_149, hl_150, hl_151⟩

theorem cases_0_38_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_38_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_to_smt.case_152 x_a0, EoCases.__eo_to_smt.case_153 x_a0, EoCases.__eo_to_smt.case_154 x_a0, EoCases.__eo_to_smt.case_155 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_152 x_a0 = none ∧ EoCases.__eo_to_smt.case_153 x_a0 = none ∧ EoCases.__eo_to_smt.case_154 x_a0 = none ∧ EoCases.__eo_to_smt.case_155 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_38_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  group_step with case_152_eo__24eo_5fto_5fsmt_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_152 x_a0, EoCases.__eo_to_smt.case_153 x_a0, EoCases.__eo_to_smt.case_154 x_a0, EoCases.__eo_to_smt.case_155 x_a0] = [] ++ [EoCases.__eo_to_smt.case_152 x_a0] ++ [EoCases.__eo_to_smt.case_153 x_a0, EoCases.__eo_to_smt.case_154 x_a0, EoCases.__eo_to_smt.case_155 x_a0] from rfl)
    otherwise ⟨hl_152⟩ using
  group_step with case_153_eo__24eo_5fto_5fsmt_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_152 x_a0, EoCases.__eo_to_smt.case_153 x_a0, EoCases.__eo_to_smt.case_154 x_a0, EoCases.__eo_to_smt.case_155 x_a0] = [EoCases.__eo_to_smt.case_152 x_a0] ++ [EoCases.__eo_to_smt.case_153 x_a0] ++ [EoCases.__eo_to_smt.case_154 x_a0, EoCases.__eo_to_smt.case_155 x_a0] from rfl)
    otherwise ⟨hl_153⟩ using hl_152
  group_step with case_154_eo__24eo_5fto_5fsmt_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_152 x_a0, EoCases.__eo_to_smt.case_153 x_a0, EoCases.__eo_to_smt.case_154 x_a0, EoCases.__eo_to_smt.case_155 x_a0] = [EoCases.__eo_to_smt.case_152 x_a0, EoCases.__eo_to_smt.case_153 x_a0] ++ [EoCases.__eo_to_smt.case_154 x_a0] ++ [EoCases.__eo_to_smt.case_155 x_a0] from rfl)
    otherwise ⟨hl_154⟩ using hl_152 hl_153
  group_step with case_155_eo__24eo_5fto_5fsmt_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_152 x_a0, EoCases.__eo_to_smt.case_153 x_a0, EoCases.__eo_to_smt.case_154 x_a0, EoCases.__eo_to_smt.case_155 x_a0] = [EoCases.__eo_to_smt.case_152 x_a0, EoCases.__eo_to_smt.case_153 x_a0, EoCases.__eo_to_smt.case_154 x_a0] ++ [EoCases.__eo_to_smt.case_155 x_a0] ++ [] from rfl)
    otherwise ⟨hl_155⟩ using hl_152 hl_153 hl_154
  group_none hinv4 hG with ⟨hl_152, hl_153, hl_154, hl_155⟩

theorem cases_0_39_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_39_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_to_smt.case_156 x_a0, EoCases.__eo_to_smt.case_157 x_a0, EoCases.__eo_to_smt.case_158 x_a0, EoCases.__eo_to_smt.case_159 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_156 x_a0 = none ∧ EoCases.__eo_to_smt.case_157 x_a0 = none ∧ EoCases.__eo_to_smt.case_158 x_a0 = none ∧ EoCases.__eo_to_smt.case_159 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_39_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  group_step with case_156_eo__24eo_5fto_5fsmt_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_156 x_a0, EoCases.__eo_to_smt.case_157 x_a0, EoCases.__eo_to_smt.case_158 x_a0, EoCases.__eo_to_smt.case_159 x_a0] = [] ++ [EoCases.__eo_to_smt.case_156 x_a0] ++ [EoCases.__eo_to_smt.case_157 x_a0, EoCases.__eo_to_smt.case_158 x_a0, EoCases.__eo_to_smt.case_159 x_a0] from rfl)
    otherwise ⟨hl_156⟩ using
  group_step with case_157_eo__24eo_5fto_5fsmt_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_156 x_a0, EoCases.__eo_to_smt.case_157 x_a0, EoCases.__eo_to_smt.case_158 x_a0, EoCases.__eo_to_smt.case_159 x_a0] = [EoCases.__eo_to_smt.case_156 x_a0] ++ [EoCases.__eo_to_smt.case_157 x_a0] ++ [EoCases.__eo_to_smt.case_158 x_a0, EoCases.__eo_to_smt.case_159 x_a0] from rfl)
    otherwise ⟨hl_157⟩ using hl_156
  group_step with case_158_eo__24eo_5fto_5fsmt_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_156 x_a0, EoCases.__eo_to_smt.case_157 x_a0, EoCases.__eo_to_smt.case_158 x_a0, EoCases.__eo_to_smt.case_159 x_a0] = [EoCases.__eo_to_smt.case_156 x_a0, EoCases.__eo_to_smt.case_157 x_a0] ++ [EoCases.__eo_to_smt.case_158 x_a0] ++ [EoCases.__eo_to_smt.case_159 x_a0] from rfl)
    otherwise ⟨hl_158⟩ using hl_156 hl_157
  group_step with case_159_eo__24eo_5fto_5fsmt_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_156 x_a0, EoCases.__eo_to_smt.case_157 x_a0, EoCases.__eo_to_smt.case_158 x_a0, EoCases.__eo_to_smt.case_159 x_a0] = [EoCases.__eo_to_smt.case_156 x_a0, EoCases.__eo_to_smt.case_157 x_a0, EoCases.__eo_to_smt.case_158 x_a0] ++ [EoCases.__eo_to_smt.case_159 x_a0] ++ [] from rfl)
    otherwise ⟨hl_159⟩ using hl_156 hl_157 hl_158
  group_none hinv4 hG with ⟨hl_156, hl_157, hl_158, hl_159⟩

theorem cases_0_40_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_40_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_to_smt.case_160 x_a0, EoCases.__eo_to_smt.case_161 x_a0, EoCases.__eo_to_smt.case_162 x_a0, EoCases.__eo_to_smt.case_163 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_160 x_a0 = none ∧ EoCases.__eo_to_smt.case_161 x_a0 = none ∧ EoCases.__eo_to_smt.case_162 x_a0 = none ∧ EoCases.__eo_to_smt.case_163 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_40_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  group_step with case_160_eo__24eo_5fto_5fsmt_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_160 x_a0, EoCases.__eo_to_smt.case_161 x_a0, EoCases.__eo_to_smt.case_162 x_a0, EoCases.__eo_to_smt.case_163 x_a0] = [] ++ [EoCases.__eo_to_smt.case_160 x_a0] ++ [EoCases.__eo_to_smt.case_161 x_a0, EoCases.__eo_to_smt.case_162 x_a0, EoCases.__eo_to_smt.case_163 x_a0] from rfl)
    otherwise ⟨hl_160⟩ using
  group_step with case_161_eo__24eo_5fto_5fsmt_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_160 x_a0, EoCases.__eo_to_smt.case_161 x_a0, EoCases.__eo_to_smt.case_162 x_a0, EoCases.__eo_to_smt.case_163 x_a0] = [EoCases.__eo_to_smt.case_160 x_a0] ++ [EoCases.__eo_to_smt.case_161 x_a0] ++ [EoCases.__eo_to_smt.case_162 x_a0, EoCases.__eo_to_smt.case_163 x_a0] from rfl)
    otherwise ⟨hl_161⟩ using hl_160
  group_step with case_162_eo__24eo_5fto_5fsmt_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_160 x_a0, EoCases.__eo_to_smt.case_161 x_a0, EoCases.__eo_to_smt.case_162 x_a0, EoCases.__eo_to_smt.case_163 x_a0] = [EoCases.__eo_to_smt.case_160 x_a0, EoCases.__eo_to_smt.case_161 x_a0] ++ [EoCases.__eo_to_smt.case_162 x_a0] ++ [EoCases.__eo_to_smt.case_163 x_a0] from rfl)
    otherwise ⟨hl_162⟩ using hl_160 hl_161
  group_step with case_163_eo__24eo_5fto_5fsmt_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_160 x_a0, EoCases.__eo_to_smt.case_161 x_a0, EoCases.__eo_to_smt.case_162 x_a0, EoCases.__eo_to_smt.case_163 x_a0] = [EoCases.__eo_to_smt.case_160 x_a0, EoCases.__eo_to_smt.case_161 x_a0, EoCases.__eo_to_smt.case_162 x_a0] ++ [EoCases.__eo_to_smt.case_163 x_a0] ++ [] from rfl)
    otherwise ⟨hl_163⟩ using hl_160 hl_161 hl_162
  group_none hinv4 hG with ⟨hl_160, hl_161, hl_162, hl_163⟩

theorem cases_0_41_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_41_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_to_smt.case_164 x_a0, EoCases.__eo_to_smt.case_165 x_a0, EoCases.__eo_to_smt.case_166 x_a0, EoCases.__eo_to_smt.case_167 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_164 x_a0 = none ∧ EoCases.__eo_to_smt.case_165 x_a0 = none ∧ EoCases.__eo_to_smt.case_166 x_a0 = none ∧ EoCases.__eo_to_smt.case_167 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_41_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  group_step with case_164_eo__24eo_5fto_5fsmt_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_164 x_a0, EoCases.__eo_to_smt.case_165 x_a0, EoCases.__eo_to_smt.case_166 x_a0, EoCases.__eo_to_smt.case_167 x_a0] = [] ++ [EoCases.__eo_to_smt.case_164 x_a0] ++ [EoCases.__eo_to_smt.case_165 x_a0, EoCases.__eo_to_smt.case_166 x_a0, EoCases.__eo_to_smt.case_167 x_a0] from rfl)
    otherwise ⟨hl_164⟩ using
  group_step with case_165_eo__24eo_5fto_5fsmt_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_164 x_a0, EoCases.__eo_to_smt.case_165 x_a0, EoCases.__eo_to_smt.case_166 x_a0, EoCases.__eo_to_smt.case_167 x_a0] = [EoCases.__eo_to_smt.case_164 x_a0] ++ [EoCases.__eo_to_smt.case_165 x_a0] ++ [EoCases.__eo_to_smt.case_166 x_a0, EoCases.__eo_to_smt.case_167 x_a0] from rfl)
    otherwise ⟨hl_165⟩ using hl_164
  group_step with case_166_eo__24eo_5fto_5fsmt_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_164 x_a0, EoCases.__eo_to_smt.case_165 x_a0, EoCases.__eo_to_smt.case_166 x_a0, EoCases.__eo_to_smt.case_167 x_a0] = [EoCases.__eo_to_smt.case_164 x_a0, EoCases.__eo_to_smt.case_165 x_a0] ++ [EoCases.__eo_to_smt.case_166 x_a0] ++ [EoCases.__eo_to_smt.case_167 x_a0] from rfl)
    otherwise ⟨hl_166⟩ using hl_164 hl_165
  group_step with case_167_eo__24eo_5fto_5fsmt_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_164 x_a0, EoCases.__eo_to_smt.case_165 x_a0, EoCases.__eo_to_smt.case_166 x_a0, EoCases.__eo_to_smt.case_167 x_a0] = [EoCases.__eo_to_smt.case_164 x_a0, EoCases.__eo_to_smt.case_165 x_a0, EoCases.__eo_to_smt.case_166 x_a0] ++ [EoCases.__eo_to_smt.case_167 x_a0] ++ [] from rfl)
    otherwise ⟨hl_167⟩ using hl_164 hl_165 hl_166
  group_none hinv4 hG with ⟨hl_164, hl_165, hl_166, hl_167⟩

theorem cases_0_42_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_42_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_to_smt.case_168 x_a0, EoCases.__eo_to_smt.case_169 x_a0, EoCases.__eo_to_smt.case_170 x_a0, EoCases.__eo_to_smt.case_171 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_168 x_a0 = none ∧ EoCases.__eo_to_smt.case_169 x_a0 = none ∧ EoCases.__eo_to_smt.case_170 x_a0 = none ∧ EoCases.__eo_to_smt.case_171 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_42_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  group_step with case_168_eo__24eo_5fto_5fsmt_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_168 x_a0, EoCases.__eo_to_smt.case_169 x_a0, EoCases.__eo_to_smt.case_170 x_a0, EoCases.__eo_to_smt.case_171 x_a0] = [] ++ [EoCases.__eo_to_smt.case_168 x_a0] ++ [EoCases.__eo_to_smt.case_169 x_a0, EoCases.__eo_to_smt.case_170 x_a0, EoCases.__eo_to_smt.case_171 x_a0] from rfl)
    otherwise ⟨hl_168⟩ using
  group_step with case_169_eo__24eo_5fto_5fsmt_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_168 x_a0, EoCases.__eo_to_smt.case_169 x_a0, EoCases.__eo_to_smt.case_170 x_a0, EoCases.__eo_to_smt.case_171 x_a0] = [EoCases.__eo_to_smt.case_168 x_a0] ++ [EoCases.__eo_to_smt.case_169 x_a0] ++ [EoCases.__eo_to_smt.case_170 x_a0, EoCases.__eo_to_smt.case_171 x_a0] from rfl)
    otherwise ⟨hl_169⟩ using hl_168
  group_step with case_170_eo__24eo_5fto_5fsmt_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_168 x_a0, EoCases.__eo_to_smt.case_169 x_a0, EoCases.__eo_to_smt.case_170 x_a0, EoCases.__eo_to_smt.case_171 x_a0] = [EoCases.__eo_to_smt.case_168 x_a0, EoCases.__eo_to_smt.case_169 x_a0] ++ [EoCases.__eo_to_smt.case_170 x_a0] ++ [EoCases.__eo_to_smt.case_171 x_a0] from rfl)
    otherwise ⟨hl_170⟩ using hl_168 hl_169
  group_step with case_171_eo__24eo_5fto_5fsmt_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_168 x_a0, EoCases.__eo_to_smt.case_169 x_a0, EoCases.__eo_to_smt.case_170 x_a0, EoCases.__eo_to_smt.case_171 x_a0] = [EoCases.__eo_to_smt.case_168 x_a0, EoCases.__eo_to_smt.case_169 x_a0, EoCases.__eo_to_smt.case_170 x_a0] ++ [EoCases.__eo_to_smt.case_171 x_a0] ++ [] from rfl)
    otherwise ⟨hl_171⟩ using hl_168 hl_169 hl_170
  group_none hinv4 hG with ⟨hl_168, hl_169, hl_170, hl_171⟩

theorem cases_0_43_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_43_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_to_smt.case_172 x_a0, EoCases.__eo_to_smt.case_173 x_a0, EoCases.__eo_to_smt.case_174 x_a0, EoCases.__eo_to_smt.case_175 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_172 x_a0 = none ∧ EoCases.__eo_to_smt.case_173 x_a0 = none ∧ EoCases.__eo_to_smt.case_174 x_a0 = none ∧ EoCases.__eo_to_smt.case_175 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_43_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  group_step with case_172_eo__24eo_5fto_5fsmt_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_172 x_a0, EoCases.__eo_to_smt.case_173 x_a0, EoCases.__eo_to_smt.case_174 x_a0, EoCases.__eo_to_smt.case_175 x_a0] = [] ++ [EoCases.__eo_to_smt.case_172 x_a0] ++ [EoCases.__eo_to_smt.case_173 x_a0, EoCases.__eo_to_smt.case_174 x_a0, EoCases.__eo_to_smt.case_175 x_a0] from rfl)
    otherwise ⟨hl_172⟩ using
  group_step with case_173_eo__24eo_5fto_5fsmt_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_172 x_a0, EoCases.__eo_to_smt.case_173 x_a0, EoCases.__eo_to_smt.case_174 x_a0, EoCases.__eo_to_smt.case_175 x_a0] = [EoCases.__eo_to_smt.case_172 x_a0] ++ [EoCases.__eo_to_smt.case_173 x_a0] ++ [EoCases.__eo_to_smt.case_174 x_a0, EoCases.__eo_to_smt.case_175 x_a0] from rfl)
    otherwise ⟨hl_173⟩ using hl_172
  group_step with case_174_eo__24eo_5fto_5fsmt_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_172 x_a0, EoCases.__eo_to_smt.case_173 x_a0, EoCases.__eo_to_smt.case_174 x_a0, EoCases.__eo_to_smt.case_175 x_a0] = [EoCases.__eo_to_smt.case_172 x_a0, EoCases.__eo_to_smt.case_173 x_a0] ++ [EoCases.__eo_to_smt.case_174 x_a0] ++ [EoCases.__eo_to_smt.case_175 x_a0] from rfl)
    otherwise ⟨hl_174⟩ using hl_172 hl_173
  group_step with case_175_eo__24eo_5fto_5fsmt_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_172 x_a0, EoCases.__eo_to_smt.case_173 x_a0, EoCases.__eo_to_smt.case_174 x_a0, EoCases.__eo_to_smt.case_175 x_a0] = [EoCases.__eo_to_smt.case_172 x_a0, EoCases.__eo_to_smt.case_173 x_a0, EoCases.__eo_to_smt.case_174 x_a0] ++ [EoCases.__eo_to_smt.case_175 x_a0] ++ [] from rfl)
    otherwise ⟨hl_175⟩ using hl_172 hl_173 hl_174
  group_none hinv4 hG with ⟨hl_172, hl_173, hl_174, hl_175⟩

theorem cases_0_44_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_44_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_to_smt.case_176 x_a0, EoCases.__eo_to_smt.case_177 x_a0, EoCases.__eo_to_smt.case_178 x_a0, EoCases.__eo_to_smt.case_179 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_176 x_a0 = none ∧ EoCases.__eo_to_smt.case_177 x_a0 = none ∧ EoCases.__eo_to_smt.case_178 x_a0 = none ∧ EoCases.__eo_to_smt.case_179 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_44_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  group_step with case_176_eo__24eo_5fto_5fsmt_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_176 x_a0, EoCases.__eo_to_smt.case_177 x_a0, EoCases.__eo_to_smt.case_178 x_a0, EoCases.__eo_to_smt.case_179 x_a0] = [] ++ [EoCases.__eo_to_smt.case_176 x_a0] ++ [EoCases.__eo_to_smt.case_177 x_a0, EoCases.__eo_to_smt.case_178 x_a0, EoCases.__eo_to_smt.case_179 x_a0] from rfl)
    otherwise ⟨hl_176⟩ using
  group_step with case_177_eo__24eo_5fto_5fsmt_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_176 x_a0, EoCases.__eo_to_smt.case_177 x_a0, EoCases.__eo_to_smt.case_178 x_a0, EoCases.__eo_to_smt.case_179 x_a0] = [EoCases.__eo_to_smt.case_176 x_a0] ++ [EoCases.__eo_to_smt.case_177 x_a0] ++ [EoCases.__eo_to_smt.case_178 x_a0, EoCases.__eo_to_smt.case_179 x_a0] from rfl)
    otherwise ⟨hl_177⟩ using hl_176
  group_step with case_178_eo__24eo_5fto_5fsmt_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_176 x_a0, EoCases.__eo_to_smt.case_177 x_a0, EoCases.__eo_to_smt.case_178 x_a0, EoCases.__eo_to_smt.case_179 x_a0] = [EoCases.__eo_to_smt.case_176 x_a0, EoCases.__eo_to_smt.case_177 x_a0] ++ [EoCases.__eo_to_smt.case_178 x_a0] ++ [EoCases.__eo_to_smt.case_179 x_a0] from rfl)
    otherwise ⟨hl_178⟩ using hl_176 hl_177
  group_step with case_179_eo__24eo_5fto_5fsmt_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_176 x_a0, EoCases.__eo_to_smt.case_177 x_a0, EoCases.__eo_to_smt.case_178 x_a0, EoCases.__eo_to_smt.case_179 x_a0] = [EoCases.__eo_to_smt.case_176 x_a0, EoCases.__eo_to_smt.case_177 x_a0, EoCases.__eo_to_smt.case_178 x_a0] ++ [EoCases.__eo_to_smt.case_179 x_a0] ++ [] from rfl)
    otherwise ⟨hl_179⟩ using hl_176 hl_177 hl_178
  group_none hinv4 hG with ⟨hl_176, hl_177, hl_178, hl_179⟩

theorem cases_0_45_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_45_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_to_smt.case_180 x_a0, EoCases.__eo_to_smt.case_181 x_a0, EoCases.__eo_to_smt.case_182 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_180 x_a0 = none ∧ EoCases.__eo_to_smt.case_181 x_a0 = none ∧ EoCases.__eo_to_smt.case_182 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_45_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  group_step with case_180_eo__24eo_5fto_5fsmt_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_180 x_a0, EoCases.__eo_to_smt.case_181 x_a0, EoCases.__eo_to_smt.case_182 x_a0] = [] ++ [EoCases.__eo_to_smt.case_180 x_a0] ++ [EoCases.__eo_to_smt.case_181 x_a0, EoCases.__eo_to_smt.case_182 x_a0] from rfl)
    otherwise ⟨hl_180⟩ using
  group_step with case_181_eo__24eo_5fto_5fsmt_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_180 x_a0, EoCases.__eo_to_smt.case_181 x_a0, EoCases.__eo_to_smt.case_182 x_a0] = [EoCases.__eo_to_smt.case_180 x_a0] ++ [EoCases.__eo_to_smt.case_181 x_a0] ++ [EoCases.__eo_to_smt.case_182 x_a0] from rfl)
    otherwise ⟨hl_181⟩ using hl_180
  group_step with case_182_eo__24eo_5fto_5fsmt_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_180 x_a0, EoCases.__eo_to_smt.case_181 x_a0, EoCases.__eo_to_smt.case_182 x_a0] = [EoCases.__eo_to_smt.case_180 x_a0, EoCases.__eo_to_smt.case_181 x_a0] ++ [EoCases.__eo_to_smt.case_182 x_a0] ++ [] from rfl)
    otherwise ⟨hl_182⟩ using hl_180 hl_181
  group_none hinv3 hG with ⟨hl_180, hl_181, hl_182⟩

theorem cases_1_0_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_1_0_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_to_smt.case_0 x_a0, EoCases.__eo_to_smt.case_1 x_a0, EoCases.__eo_to_smt.case_2 x_a0, EoCases.__eo_to_smt.case_3 x_a0, EoCases.__eo_to_smt.case_4 x_a0, EoCases.__eo_to_smt.case_5 x_a0, EoCases.__eo_to_smt.case_6 x_a0, EoCases.__eo_to_smt.case_7 x_a0, EoCases.__eo_to_smt.case_8 x_a0, EoCases.__eo_to_smt.case_9 x_a0, EoCases.__eo_to_smt.case_10 x_a0, EoCases.__eo_to_smt.case_11 x_a0, EoCases.__eo_to_smt.case_12 x_a0, EoCases.__eo_to_smt.case_13 x_a0, EoCases.__eo_to_smt.case_14 x_a0, EoCases.__eo_to_smt.case_15 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_0 x_a0 = none ∧ EoCases.__eo_to_smt.case_1 x_a0 = none ∧ EoCases.__eo_to_smt.case_2 x_a0 = none ∧ EoCases.__eo_to_smt.case_3 x_a0 = none ∧ EoCases.__eo_to_smt.case_4 x_a0 = none ∧ EoCases.__eo_to_smt.case_5 x_a0 = none ∧ EoCases.__eo_to_smt.case_6 x_a0 = none ∧ EoCases.__eo_to_smt.case_7 x_a0 = none ∧ EoCases.__eo_to_smt.case_8 x_a0 = none ∧ EoCases.__eo_to_smt.case_9 x_a0 = none ∧ EoCases.__eo_to_smt.case_10 x_a0 = none ∧ EoCases.__eo_to_smt.case_11 x_a0 = none ∧ EoCases.__eo_to_smt.case_12 x_a0 = none ∧ EoCases.__eo_to_smt.case_13 x_a0 = none ∧ EoCases.__eo_to_smt.case_14 x_a0 = none ∧ EoCases.__eo_to_smt.case_15 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_1_0_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  group_step with cases_0_0_eo__24eo_5fto_5fsmt_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_0 x_a0, EoCases.__eo_to_smt.case_1 x_a0, EoCases.__eo_to_smt.case_2 x_a0, EoCases.__eo_to_smt.case_3 x_a0, EoCases.__eo_to_smt.case_4 x_a0, EoCases.__eo_to_smt.case_5 x_a0, EoCases.__eo_to_smt.case_6 x_a0, EoCases.__eo_to_smt.case_7 x_a0, EoCases.__eo_to_smt.case_8 x_a0, EoCases.__eo_to_smt.case_9 x_a0, EoCases.__eo_to_smt.case_10 x_a0, EoCases.__eo_to_smt.case_11 x_a0, EoCases.__eo_to_smt.case_12 x_a0, EoCases.__eo_to_smt.case_13 x_a0, EoCases.__eo_to_smt.case_14 x_a0, EoCases.__eo_to_smt.case_15 x_a0] = [] ++ [EoCases.__eo_to_smt.case_0 x_a0, EoCases.__eo_to_smt.case_1 x_a0, EoCases.__eo_to_smt.case_2 x_a0, EoCases.__eo_to_smt.case_3 x_a0] ++ [EoCases.__eo_to_smt.case_4 x_a0, EoCases.__eo_to_smt.case_5 x_a0, EoCases.__eo_to_smt.case_6 x_a0, EoCases.__eo_to_smt.case_7 x_a0, EoCases.__eo_to_smt.case_8 x_a0, EoCases.__eo_to_smt.case_9 x_a0, EoCases.__eo_to_smt.case_10 x_a0, EoCases.__eo_to_smt.case_11 x_a0, EoCases.__eo_to_smt.case_12 x_a0, EoCases.__eo_to_smt.case_13 x_a0, EoCases.__eo_to_smt.case_14 x_a0, EoCases.__eo_to_smt.case_15 x_a0] from rfl)
    otherwise ⟨hl_0, hl_1, hl_2, hl_3⟩ using
  group_step with cases_0_1_eo__24eo_5fto_5fsmt_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_0 x_a0, EoCases.__eo_to_smt.case_1 x_a0, EoCases.__eo_to_smt.case_2 x_a0, EoCases.__eo_to_smt.case_3 x_a0, EoCases.__eo_to_smt.case_4 x_a0, EoCases.__eo_to_smt.case_5 x_a0, EoCases.__eo_to_smt.case_6 x_a0, EoCases.__eo_to_smt.case_7 x_a0, EoCases.__eo_to_smt.case_8 x_a0, EoCases.__eo_to_smt.case_9 x_a0, EoCases.__eo_to_smt.case_10 x_a0, EoCases.__eo_to_smt.case_11 x_a0, EoCases.__eo_to_smt.case_12 x_a0, EoCases.__eo_to_smt.case_13 x_a0, EoCases.__eo_to_smt.case_14 x_a0, EoCases.__eo_to_smt.case_15 x_a0] = [EoCases.__eo_to_smt.case_0 x_a0, EoCases.__eo_to_smt.case_1 x_a0, EoCases.__eo_to_smt.case_2 x_a0, EoCases.__eo_to_smt.case_3 x_a0] ++ [EoCases.__eo_to_smt.case_4 x_a0, EoCases.__eo_to_smt.case_5 x_a0, EoCases.__eo_to_smt.case_6 x_a0, EoCases.__eo_to_smt.case_7 x_a0] ++ [EoCases.__eo_to_smt.case_8 x_a0, EoCases.__eo_to_smt.case_9 x_a0, EoCases.__eo_to_smt.case_10 x_a0, EoCases.__eo_to_smt.case_11 x_a0, EoCases.__eo_to_smt.case_12 x_a0, EoCases.__eo_to_smt.case_13 x_a0, EoCases.__eo_to_smt.case_14 x_a0, EoCases.__eo_to_smt.case_15 x_a0] from rfl)
    otherwise ⟨hl_4, hl_5, hl_6, hl_7⟩ using hl_0 hl_1 hl_2 hl_3
  group_step with cases_0_2_eo__24eo_5fto_5fsmt_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_0 x_a0, EoCases.__eo_to_smt.case_1 x_a0, EoCases.__eo_to_smt.case_2 x_a0, EoCases.__eo_to_smt.case_3 x_a0, EoCases.__eo_to_smt.case_4 x_a0, EoCases.__eo_to_smt.case_5 x_a0, EoCases.__eo_to_smt.case_6 x_a0, EoCases.__eo_to_smt.case_7 x_a0, EoCases.__eo_to_smt.case_8 x_a0, EoCases.__eo_to_smt.case_9 x_a0, EoCases.__eo_to_smt.case_10 x_a0, EoCases.__eo_to_smt.case_11 x_a0, EoCases.__eo_to_smt.case_12 x_a0, EoCases.__eo_to_smt.case_13 x_a0, EoCases.__eo_to_smt.case_14 x_a0, EoCases.__eo_to_smt.case_15 x_a0] = [EoCases.__eo_to_smt.case_0 x_a0, EoCases.__eo_to_smt.case_1 x_a0, EoCases.__eo_to_smt.case_2 x_a0, EoCases.__eo_to_smt.case_3 x_a0, EoCases.__eo_to_smt.case_4 x_a0, EoCases.__eo_to_smt.case_5 x_a0, EoCases.__eo_to_smt.case_6 x_a0, EoCases.__eo_to_smt.case_7 x_a0] ++ [EoCases.__eo_to_smt.case_8 x_a0, EoCases.__eo_to_smt.case_9 x_a0, EoCases.__eo_to_smt.case_10 x_a0, EoCases.__eo_to_smt.case_11 x_a0] ++ [EoCases.__eo_to_smt.case_12 x_a0, EoCases.__eo_to_smt.case_13 x_a0, EoCases.__eo_to_smt.case_14 x_a0, EoCases.__eo_to_smt.case_15 x_a0] from rfl)
    otherwise ⟨hl_8, hl_9, hl_10, hl_11⟩ using hl_0 hl_1 hl_2 hl_3 hl_4 hl_5 hl_6 hl_7
  group_step with cases_0_3_eo__24eo_5fto_5fsmt_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_0 x_a0, EoCases.__eo_to_smt.case_1 x_a0, EoCases.__eo_to_smt.case_2 x_a0, EoCases.__eo_to_smt.case_3 x_a0, EoCases.__eo_to_smt.case_4 x_a0, EoCases.__eo_to_smt.case_5 x_a0, EoCases.__eo_to_smt.case_6 x_a0, EoCases.__eo_to_smt.case_7 x_a0, EoCases.__eo_to_smt.case_8 x_a0, EoCases.__eo_to_smt.case_9 x_a0, EoCases.__eo_to_smt.case_10 x_a0, EoCases.__eo_to_smt.case_11 x_a0, EoCases.__eo_to_smt.case_12 x_a0, EoCases.__eo_to_smt.case_13 x_a0, EoCases.__eo_to_smt.case_14 x_a0, EoCases.__eo_to_smt.case_15 x_a0] = [EoCases.__eo_to_smt.case_0 x_a0, EoCases.__eo_to_smt.case_1 x_a0, EoCases.__eo_to_smt.case_2 x_a0, EoCases.__eo_to_smt.case_3 x_a0, EoCases.__eo_to_smt.case_4 x_a0, EoCases.__eo_to_smt.case_5 x_a0, EoCases.__eo_to_smt.case_6 x_a0, EoCases.__eo_to_smt.case_7 x_a0, EoCases.__eo_to_smt.case_8 x_a0, EoCases.__eo_to_smt.case_9 x_a0, EoCases.__eo_to_smt.case_10 x_a0, EoCases.__eo_to_smt.case_11 x_a0] ++ [EoCases.__eo_to_smt.case_12 x_a0, EoCases.__eo_to_smt.case_13 x_a0, EoCases.__eo_to_smt.case_14 x_a0, EoCases.__eo_to_smt.case_15 x_a0] ++ [] from rfl)
    otherwise ⟨hl_12, hl_13, hl_14, hl_15⟩ using hl_0 hl_1 hl_2 hl_3 hl_4 hl_5 hl_6 hl_7 hl_8 hl_9 hl_10 hl_11
  group_none hinv4 hG with ⟨hl_0, hl_1, hl_2, hl_3, hl_4, hl_5, hl_6, hl_7, hl_8, hl_9, hl_10, hl_11, hl_12, hl_13, hl_14, hl_15⟩

theorem cases_1_1_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_1_1_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_to_smt.case_16 x_a0, EoCases.__eo_to_smt.case_17 x_a0, EoCases.__eo_to_smt.case_18 x_a0, EoCases.__eo_to_smt.case_19 x_a0, EoCases.__eo_to_smt.case_20 x_a0, EoCases.__eo_to_smt.case_21 x_a0, EoCases.__eo_to_smt.case_22 x_a0, EoCases.__eo_to_smt.case_23 x_a0, EoCases.__eo_to_smt.case_24 x_a0, EoCases.__eo_to_smt.case_25 x_a0, EoCases.__eo_to_smt.case_26 x_a0, EoCases.__eo_to_smt.case_27 x_a0, EoCases.__eo_to_smt.case_28 x_a0, EoCases.__eo_to_smt.case_29 x_a0, EoCases.__eo_to_smt.case_30 x_a0, EoCases.__eo_to_smt.case_31 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_16 x_a0 = none ∧ EoCases.__eo_to_smt.case_17 x_a0 = none ∧ EoCases.__eo_to_smt.case_18 x_a0 = none ∧ EoCases.__eo_to_smt.case_19 x_a0 = none ∧ EoCases.__eo_to_smt.case_20 x_a0 = none ∧ EoCases.__eo_to_smt.case_21 x_a0 = none ∧ EoCases.__eo_to_smt.case_22 x_a0 = none ∧ EoCases.__eo_to_smt.case_23 x_a0 = none ∧ EoCases.__eo_to_smt.case_24 x_a0 = none ∧ EoCases.__eo_to_smt.case_25 x_a0 = none ∧ EoCases.__eo_to_smt.case_26 x_a0 = none ∧ EoCases.__eo_to_smt.case_27 x_a0 = none ∧ EoCases.__eo_to_smt.case_28 x_a0 = none ∧ EoCases.__eo_to_smt.case_29 x_a0 = none ∧ EoCases.__eo_to_smt.case_30 x_a0 = none ∧ EoCases.__eo_to_smt.case_31 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_1_1_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  group_step with cases_0_4_eo__24eo_5fto_5fsmt_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_16 x_a0, EoCases.__eo_to_smt.case_17 x_a0, EoCases.__eo_to_smt.case_18 x_a0, EoCases.__eo_to_smt.case_19 x_a0, EoCases.__eo_to_smt.case_20 x_a0, EoCases.__eo_to_smt.case_21 x_a0, EoCases.__eo_to_smt.case_22 x_a0, EoCases.__eo_to_smt.case_23 x_a0, EoCases.__eo_to_smt.case_24 x_a0, EoCases.__eo_to_smt.case_25 x_a0, EoCases.__eo_to_smt.case_26 x_a0, EoCases.__eo_to_smt.case_27 x_a0, EoCases.__eo_to_smt.case_28 x_a0, EoCases.__eo_to_smt.case_29 x_a0, EoCases.__eo_to_smt.case_30 x_a0, EoCases.__eo_to_smt.case_31 x_a0] = [] ++ [EoCases.__eo_to_smt.case_16 x_a0, EoCases.__eo_to_smt.case_17 x_a0, EoCases.__eo_to_smt.case_18 x_a0, EoCases.__eo_to_smt.case_19 x_a0] ++ [EoCases.__eo_to_smt.case_20 x_a0, EoCases.__eo_to_smt.case_21 x_a0, EoCases.__eo_to_smt.case_22 x_a0, EoCases.__eo_to_smt.case_23 x_a0, EoCases.__eo_to_smt.case_24 x_a0, EoCases.__eo_to_smt.case_25 x_a0, EoCases.__eo_to_smt.case_26 x_a0, EoCases.__eo_to_smt.case_27 x_a0, EoCases.__eo_to_smt.case_28 x_a0, EoCases.__eo_to_smt.case_29 x_a0, EoCases.__eo_to_smt.case_30 x_a0, EoCases.__eo_to_smt.case_31 x_a0] from rfl)
    otherwise ⟨hl_16, hl_17, hl_18, hl_19⟩ using
  group_step with cases_0_5_eo__24eo_5fto_5fsmt_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_16 x_a0, EoCases.__eo_to_smt.case_17 x_a0, EoCases.__eo_to_smt.case_18 x_a0, EoCases.__eo_to_smt.case_19 x_a0, EoCases.__eo_to_smt.case_20 x_a0, EoCases.__eo_to_smt.case_21 x_a0, EoCases.__eo_to_smt.case_22 x_a0, EoCases.__eo_to_smt.case_23 x_a0, EoCases.__eo_to_smt.case_24 x_a0, EoCases.__eo_to_smt.case_25 x_a0, EoCases.__eo_to_smt.case_26 x_a0, EoCases.__eo_to_smt.case_27 x_a0, EoCases.__eo_to_smt.case_28 x_a0, EoCases.__eo_to_smt.case_29 x_a0, EoCases.__eo_to_smt.case_30 x_a0, EoCases.__eo_to_smt.case_31 x_a0] = [EoCases.__eo_to_smt.case_16 x_a0, EoCases.__eo_to_smt.case_17 x_a0, EoCases.__eo_to_smt.case_18 x_a0, EoCases.__eo_to_smt.case_19 x_a0] ++ [EoCases.__eo_to_smt.case_20 x_a0, EoCases.__eo_to_smt.case_21 x_a0, EoCases.__eo_to_smt.case_22 x_a0, EoCases.__eo_to_smt.case_23 x_a0] ++ [EoCases.__eo_to_smt.case_24 x_a0, EoCases.__eo_to_smt.case_25 x_a0, EoCases.__eo_to_smt.case_26 x_a0, EoCases.__eo_to_smt.case_27 x_a0, EoCases.__eo_to_smt.case_28 x_a0, EoCases.__eo_to_smt.case_29 x_a0, EoCases.__eo_to_smt.case_30 x_a0, EoCases.__eo_to_smt.case_31 x_a0] from rfl)
    otherwise ⟨hl_20, hl_21, hl_22, hl_23⟩ using hl_16 hl_17 hl_18 hl_19
  group_step with cases_0_6_eo__24eo_5fto_5fsmt_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_16 x_a0, EoCases.__eo_to_smt.case_17 x_a0, EoCases.__eo_to_smt.case_18 x_a0, EoCases.__eo_to_smt.case_19 x_a0, EoCases.__eo_to_smt.case_20 x_a0, EoCases.__eo_to_smt.case_21 x_a0, EoCases.__eo_to_smt.case_22 x_a0, EoCases.__eo_to_smt.case_23 x_a0, EoCases.__eo_to_smt.case_24 x_a0, EoCases.__eo_to_smt.case_25 x_a0, EoCases.__eo_to_smt.case_26 x_a0, EoCases.__eo_to_smt.case_27 x_a0, EoCases.__eo_to_smt.case_28 x_a0, EoCases.__eo_to_smt.case_29 x_a0, EoCases.__eo_to_smt.case_30 x_a0, EoCases.__eo_to_smt.case_31 x_a0] = [EoCases.__eo_to_smt.case_16 x_a0, EoCases.__eo_to_smt.case_17 x_a0, EoCases.__eo_to_smt.case_18 x_a0, EoCases.__eo_to_smt.case_19 x_a0, EoCases.__eo_to_smt.case_20 x_a0, EoCases.__eo_to_smt.case_21 x_a0, EoCases.__eo_to_smt.case_22 x_a0, EoCases.__eo_to_smt.case_23 x_a0] ++ [EoCases.__eo_to_smt.case_24 x_a0, EoCases.__eo_to_smt.case_25 x_a0, EoCases.__eo_to_smt.case_26 x_a0, EoCases.__eo_to_smt.case_27 x_a0] ++ [EoCases.__eo_to_smt.case_28 x_a0, EoCases.__eo_to_smt.case_29 x_a0, EoCases.__eo_to_smt.case_30 x_a0, EoCases.__eo_to_smt.case_31 x_a0] from rfl)
    otherwise ⟨hl_24, hl_25, hl_26, hl_27⟩ using hl_16 hl_17 hl_18 hl_19 hl_20 hl_21 hl_22 hl_23
  group_step with cases_0_7_eo__24eo_5fto_5fsmt_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_16 x_a0, EoCases.__eo_to_smt.case_17 x_a0, EoCases.__eo_to_smt.case_18 x_a0, EoCases.__eo_to_smt.case_19 x_a0, EoCases.__eo_to_smt.case_20 x_a0, EoCases.__eo_to_smt.case_21 x_a0, EoCases.__eo_to_smt.case_22 x_a0, EoCases.__eo_to_smt.case_23 x_a0, EoCases.__eo_to_smt.case_24 x_a0, EoCases.__eo_to_smt.case_25 x_a0, EoCases.__eo_to_smt.case_26 x_a0, EoCases.__eo_to_smt.case_27 x_a0, EoCases.__eo_to_smt.case_28 x_a0, EoCases.__eo_to_smt.case_29 x_a0, EoCases.__eo_to_smt.case_30 x_a0, EoCases.__eo_to_smt.case_31 x_a0] = [EoCases.__eo_to_smt.case_16 x_a0, EoCases.__eo_to_smt.case_17 x_a0, EoCases.__eo_to_smt.case_18 x_a0, EoCases.__eo_to_smt.case_19 x_a0, EoCases.__eo_to_smt.case_20 x_a0, EoCases.__eo_to_smt.case_21 x_a0, EoCases.__eo_to_smt.case_22 x_a0, EoCases.__eo_to_smt.case_23 x_a0, EoCases.__eo_to_smt.case_24 x_a0, EoCases.__eo_to_smt.case_25 x_a0, EoCases.__eo_to_smt.case_26 x_a0, EoCases.__eo_to_smt.case_27 x_a0] ++ [EoCases.__eo_to_smt.case_28 x_a0, EoCases.__eo_to_smt.case_29 x_a0, EoCases.__eo_to_smt.case_30 x_a0, EoCases.__eo_to_smt.case_31 x_a0] ++ [] from rfl)
    otherwise ⟨hl_28, hl_29, hl_30, hl_31⟩ using hl_16 hl_17 hl_18 hl_19 hl_20 hl_21 hl_22 hl_23 hl_24 hl_25 hl_26 hl_27
  group_none hinv4 hG with ⟨hl_16, hl_17, hl_18, hl_19, hl_20, hl_21, hl_22, hl_23, hl_24, hl_25, hl_26, hl_27, hl_28, hl_29, hl_30, hl_31⟩

theorem cases_1_2_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_1_2_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_to_smt.case_32 x_a0, EoCases.__eo_to_smt.case_33 x_a0, EoCases.__eo_to_smt.case_34 x_a0, EoCases.__eo_to_smt.case_35 x_a0, EoCases.__eo_to_smt.case_36 x_a0, EoCases.__eo_to_smt.case_37 x_a0, EoCases.__eo_to_smt.case_38 x_a0, EoCases.__eo_to_smt.case_39 x_a0, EoCases.__eo_to_smt.case_40 x_a0, EoCases.__eo_to_smt.case_41 x_a0, EoCases.__eo_to_smt.case_42 x_a0, EoCases.__eo_to_smt.case_43 x_a0, EoCases.__eo_to_smt.case_44 x_a0, EoCases.__eo_to_smt.case_45 x_a0, EoCases.__eo_to_smt.case_46 x_a0, EoCases.__eo_to_smt.case_47 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_32 x_a0 = none ∧ EoCases.__eo_to_smt.case_33 x_a0 = none ∧ EoCases.__eo_to_smt.case_34 x_a0 = none ∧ EoCases.__eo_to_smt.case_35 x_a0 = none ∧ EoCases.__eo_to_smt.case_36 x_a0 = none ∧ EoCases.__eo_to_smt.case_37 x_a0 = none ∧ EoCases.__eo_to_smt.case_38 x_a0 = none ∧ EoCases.__eo_to_smt.case_39 x_a0 = none ∧ EoCases.__eo_to_smt.case_40 x_a0 = none ∧ EoCases.__eo_to_smt.case_41 x_a0 = none ∧ EoCases.__eo_to_smt.case_42 x_a0 = none ∧ EoCases.__eo_to_smt.case_43 x_a0 = none ∧ EoCases.__eo_to_smt.case_44 x_a0 = none ∧ EoCases.__eo_to_smt.case_45 x_a0 = none ∧ EoCases.__eo_to_smt.case_46 x_a0 = none ∧ EoCases.__eo_to_smt.case_47 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_1_2_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  group_step with cases_0_8_eo__24eo_5fto_5fsmt_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_32 x_a0, EoCases.__eo_to_smt.case_33 x_a0, EoCases.__eo_to_smt.case_34 x_a0, EoCases.__eo_to_smt.case_35 x_a0, EoCases.__eo_to_smt.case_36 x_a0, EoCases.__eo_to_smt.case_37 x_a0, EoCases.__eo_to_smt.case_38 x_a0, EoCases.__eo_to_smt.case_39 x_a0, EoCases.__eo_to_smt.case_40 x_a0, EoCases.__eo_to_smt.case_41 x_a0, EoCases.__eo_to_smt.case_42 x_a0, EoCases.__eo_to_smt.case_43 x_a0, EoCases.__eo_to_smt.case_44 x_a0, EoCases.__eo_to_smt.case_45 x_a0, EoCases.__eo_to_smt.case_46 x_a0, EoCases.__eo_to_smt.case_47 x_a0] = [] ++ [EoCases.__eo_to_smt.case_32 x_a0, EoCases.__eo_to_smt.case_33 x_a0, EoCases.__eo_to_smt.case_34 x_a0, EoCases.__eo_to_smt.case_35 x_a0] ++ [EoCases.__eo_to_smt.case_36 x_a0, EoCases.__eo_to_smt.case_37 x_a0, EoCases.__eo_to_smt.case_38 x_a0, EoCases.__eo_to_smt.case_39 x_a0, EoCases.__eo_to_smt.case_40 x_a0, EoCases.__eo_to_smt.case_41 x_a0, EoCases.__eo_to_smt.case_42 x_a0, EoCases.__eo_to_smt.case_43 x_a0, EoCases.__eo_to_smt.case_44 x_a0, EoCases.__eo_to_smt.case_45 x_a0, EoCases.__eo_to_smt.case_46 x_a0, EoCases.__eo_to_smt.case_47 x_a0] from rfl)
    otherwise ⟨hl_32, hl_33, hl_34, hl_35⟩ using
  group_step with cases_0_9_eo__24eo_5fto_5fsmt_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_32 x_a0, EoCases.__eo_to_smt.case_33 x_a0, EoCases.__eo_to_smt.case_34 x_a0, EoCases.__eo_to_smt.case_35 x_a0, EoCases.__eo_to_smt.case_36 x_a0, EoCases.__eo_to_smt.case_37 x_a0, EoCases.__eo_to_smt.case_38 x_a0, EoCases.__eo_to_smt.case_39 x_a0, EoCases.__eo_to_smt.case_40 x_a0, EoCases.__eo_to_smt.case_41 x_a0, EoCases.__eo_to_smt.case_42 x_a0, EoCases.__eo_to_smt.case_43 x_a0, EoCases.__eo_to_smt.case_44 x_a0, EoCases.__eo_to_smt.case_45 x_a0, EoCases.__eo_to_smt.case_46 x_a0, EoCases.__eo_to_smt.case_47 x_a0] = [EoCases.__eo_to_smt.case_32 x_a0, EoCases.__eo_to_smt.case_33 x_a0, EoCases.__eo_to_smt.case_34 x_a0, EoCases.__eo_to_smt.case_35 x_a0] ++ [EoCases.__eo_to_smt.case_36 x_a0, EoCases.__eo_to_smt.case_37 x_a0, EoCases.__eo_to_smt.case_38 x_a0, EoCases.__eo_to_smt.case_39 x_a0] ++ [EoCases.__eo_to_smt.case_40 x_a0, EoCases.__eo_to_smt.case_41 x_a0, EoCases.__eo_to_smt.case_42 x_a0, EoCases.__eo_to_smt.case_43 x_a0, EoCases.__eo_to_smt.case_44 x_a0, EoCases.__eo_to_smt.case_45 x_a0, EoCases.__eo_to_smt.case_46 x_a0, EoCases.__eo_to_smt.case_47 x_a0] from rfl)
    otherwise ⟨hl_36, hl_37, hl_38, hl_39⟩ using hl_32 hl_33 hl_34 hl_35
  group_step with cases_0_10_eo__24eo_5fto_5fsmt_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_32 x_a0, EoCases.__eo_to_smt.case_33 x_a0, EoCases.__eo_to_smt.case_34 x_a0, EoCases.__eo_to_smt.case_35 x_a0, EoCases.__eo_to_smt.case_36 x_a0, EoCases.__eo_to_smt.case_37 x_a0, EoCases.__eo_to_smt.case_38 x_a0, EoCases.__eo_to_smt.case_39 x_a0, EoCases.__eo_to_smt.case_40 x_a0, EoCases.__eo_to_smt.case_41 x_a0, EoCases.__eo_to_smt.case_42 x_a0, EoCases.__eo_to_smt.case_43 x_a0, EoCases.__eo_to_smt.case_44 x_a0, EoCases.__eo_to_smt.case_45 x_a0, EoCases.__eo_to_smt.case_46 x_a0, EoCases.__eo_to_smt.case_47 x_a0] = [EoCases.__eo_to_smt.case_32 x_a0, EoCases.__eo_to_smt.case_33 x_a0, EoCases.__eo_to_smt.case_34 x_a0, EoCases.__eo_to_smt.case_35 x_a0, EoCases.__eo_to_smt.case_36 x_a0, EoCases.__eo_to_smt.case_37 x_a0, EoCases.__eo_to_smt.case_38 x_a0, EoCases.__eo_to_smt.case_39 x_a0] ++ [EoCases.__eo_to_smt.case_40 x_a0, EoCases.__eo_to_smt.case_41 x_a0, EoCases.__eo_to_smt.case_42 x_a0, EoCases.__eo_to_smt.case_43 x_a0] ++ [EoCases.__eo_to_smt.case_44 x_a0, EoCases.__eo_to_smt.case_45 x_a0, EoCases.__eo_to_smt.case_46 x_a0, EoCases.__eo_to_smt.case_47 x_a0] from rfl)
    otherwise ⟨hl_40, hl_41, hl_42, hl_43⟩ using hl_32 hl_33 hl_34 hl_35 hl_36 hl_37 hl_38 hl_39
  group_step with cases_0_11_eo__24eo_5fto_5fsmt_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_32 x_a0, EoCases.__eo_to_smt.case_33 x_a0, EoCases.__eo_to_smt.case_34 x_a0, EoCases.__eo_to_smt.case_35 x_a0, EoCases.__eo_to_smt.case_36 x_a0, EoCases.__eo_to_smt.case_37 x_a0, EoCases.__eo_to_smt.case_38 x_a0, EoCases.__eo_to_smt.case_39 x_a0, EoCases.__eo_to_smt.case_40 x_a0, EoCases.__eo_to_smt.case_41 x_a0, EoCases.__eo_to_smt.case_42 x_a0, EoCases.__eo_to_smt.case_43 x_a0, EoCases.__eo_to_smt.case_44 x_a0, EoCases.__eo_to_smt.case_45 x_a0, EoCases.__eo_to_smt.case_46 x_a0, EoCases.__eo_to_smt.case_47 x_a0] = [EoCases.__eo_to_smt.case_32 x_a0, EoCases.__eo_to_smt.case_33 x_a0, EoCases.__eo_to_smt.case_34 x_a0, EoCases.__eo_to_smt.case_35 x_a0, EoCases.__eo_to_smt.case_36 x_a0, EoCases.__eo_to_smt.case_37 x_a0, EoCases.__eo_to_smt.case_38 x_a0, EoCases.__eo_to_smt.case_39 x_a0, EoCases.__eo_to_smt.case_40 x_a0, EoCases.__eo_to_smt.case_41 x_a0, EoCases.__eo_to_smt.case_42 x_a0, EoCases.__eo_to_smt.case_43 x_a0] ++ [EoCases.__eo_to_smt.case_44 x_a0, EoCases.__eo_to_smt.case_45 x_a0, EoCases.__eo_to_smt.case_46 x_a0, EoCases.__eo_to_smt.case_47 x_a0] ++ [] from rfl)
    otherwise ⟨hl_44, hl_45, hl_46, hl_47⟩ using hl_32 hl_33 hl_34 hl_35 hl_36 hl_37 hl_38 hl_39 hl_40 hl_41 hl_42 hl_43
  group_none hinv4 hG with ⟨hl_32, hl_33, hl_34, hl_35, hl_36, hl_37, hl_38, hl_39, hl_40, hl_41, hl_42, hl_43, hl_44, hl_45, hl_46, hl_47⟩

theorem cases_1_3_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_1_3_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_to_smt.case_48 x_a0, EoCases.__eo_to_smt.case_49 x_a0, EoCases.__eo_to_smt.case_50 x_a0, EoCases.__eo_to_smt.case_51 x_a0, EoCases.__eo_to_smt.case_52 x_a0, EoCases.__eo_to_smt.case_53 x_a0, EoCases.__eo_to_smt.case_54 x_a0, EoCases.__eo_to_smt.case_55 x_a0, EoCases.__eo_to_smt.case_56 x_a0, EoCases.__eo_to_smt.case_57 x_a0, EoCases.__eo_to_smt.case_58 x_a0, EoCases.__eo_to_smt.case_59 x_a0, EoCases.__eo_to_smt.case_60 x_a0, EoCases.__eo_to_smt.case_61 x_a0, EoCases.__eo_to_smt.case_62 x_a0, EoCases.__eo_to_smt.case_63 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_48 x_a0 = none ∧ EoCases.__eo_to_smt.case_49 x_a0 = none ∧ EoCases.__eo_to_smt.case_50 x_a0 = none ∧ EoCases.__eo_to_smt.case_51 x_a0 = none ∧ EoCases.__eo_to_smt.case_52 x_a0 = none ∧ EoCases.__eo_to_smt.case_53 x_a0 = none ∧ EoCases.__eo_to_smt.case_54 x_a0 = none ∧ EoCases.__eo_to_smt.case_55 x_a0 = none ∧ EoCases.__eo_to_smt.case_56 x_a0 = none ∧ EoCases.__eo_to_smt.case_57 x_a0 = none ∧ EoCases.__eo_to_smt.case_58 x_a0 = none ∧ EoCases.__eo_to_smt.case_59 x_a0 = none ∧ EoCases.__eo_to_smt.case_60 x_a0 = none ∧ EoCases.__eo_to_smt.case_61 x_a0 = none ∧ EoCases.__eo_to_smt.case_62 x_a0 = none ∧ EoCases.__eo_to_smt.case_63 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_1_3_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  group_step with cases_0_12_eo__24eo_5fto_5fsmt_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_48 x_a0, EoCases.__eo_to_smt.case_49 x_a0, EoCases.__eo_to_smt.case_50 x_a0, EoCases.__eo_to_smt.case_51 x_a0, EoCases.__eo_to_smt.case_52 x_a0, EoCases.__eo_to_smt.case_53 x_a0, EoCases.__eo_to_smt.case_54 x_a0, EoCases.__eo_to_smt.case_55 x_a0, EoCases.__eo_to_smt.case_56 x_a0, EoCases.__eo_to_smt.case_57 x_a0, EoCases.__eo_to_smt.case_58 x_a0, EoCases.__eo_to_smt.case_59 x_a0, EoCases.__eo_to_smt.case_60 x_a0, EoCases.__eo_to_smt.case_61 x_a0, EoCases.__eo_to_smt.case_62 x_a0, EoCases.__eo_to_smt.case_63 x_a0] = [] ++ [EoCases.__eo_to_smt.case_48 x_a0, EoCases.__eo_to_smt.case_49 x_a0, EoCases.__eo_to_smt.case_50 x_a0, EoCases.__eo_to_smt.case_51 x_a0] ++ [EoCases.__eo_to_smt.case_52 x_a0, EoCases.__eo_to_smt.case_53 x_a0, EoCases.__eo_to_smt.case_54 x_a0, EoCases.__eo_to_smt.case_55 x_a0, EoCases.__eo_to_smt.case_56 x_a0, EoCases.__eo_to_smt.case_57 x_a0, EoCases.__eo_to_smt.case_58 x_a0, EoCases.__eo_to_smt.case_59 x_a0, EoCases.__eo_to_smt.case_60 x_a0, EoCases.__eo_to_smt.case_61 x_a0, EoCases.__eo_to_smt.case_62 x_a0, EoCases.__eo_to_smt.case_63 x_a0] from rfl)
    otherwise ⟨hl_48, hl_49, hl_50, hl_51⟩ using
  group_step with cases_0_13_eo__24eo_5fto_5fsmt_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_48 x_a0, EoCases.__eo_to_smt.case_49 x_a0, EoCases.__eo_to_smt.case_50 x_a0, EoCases.__eo_to_smt.case_51 x_a0, EoCases.__eo_to_smt.case_52 x_a0, EoCases.__eo_to_smt.case_53 x_a0, EoCases.__eo_to_smt.case_54 x_a0, EoCases.__eo_to_smt.case_55 x_a0, EoCases.__eo_to_smt.case_56 x_a0, EoCases.__eo_to_smt.case_57 x_a0, EoCases.__eo_to_smt.case_58 x_a0, EoCases.__eo_to_smt.case_59 x_a0, EoCases.__eo_to_smt.case_60 x_a0, EoCases.__eo_to_smt.case_61 x_a0, EoCases.__eo_to_smt.case_62 x_a0, EoCases.__eo_to_smt.case_63 x_a0] = [EoCases.__eo_to_smt.case_48 x_a0, EoCases.__eo_to_smt.case_49 x_a0, EoCases.__eo_to_smt.case_50 x_a0, EoCases.__eo_to_smt.case_51 x_a0] ++ [EoCases.__eo_to_smt.case_52 x_a0, EoCases.__eo_to_smt.case_53 x_a0, EoCases.__eo_to_smt.case_54 x_a0, EoCases.__eo_to_smt.case_55 x_a0] ++ [EoCases.__eo_to_smt.case_56 x_a0, EoCases.__eo_to_smt.case_57 x_a0, EoCases.__eo_to_smt.case_58 x_a0, EoCases.__eo_to_smt.case_59 x_a0, EoCases.__eo_to_smt.case_60 x_a0, EoCases.__eo_to_smt.case_61 x_a0, EoCases.__eo_to_smt.case_62 x_a0, EoCases.__eo_to_smt.case_63 x_a0] from rfl)
    otherwise ⟨hl_52, hl_53, hl_54, hl_55⟩ using hl_48 hl_49 hl_50 hl_51
  group_step with cases_0_14_eo__24eo_5fto_5fsmt_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_48 x_a0, EoCases.__eo_to_smt.case_49 x_a0, EoCases.__eo_to_smt.case_50 x_a0, EoCases.__eo_to_smt.case_51 x_a0, EoCases.__eo_to_smt.case_52 x_a0, EoCases.__eo_to_smt.case_53 x_a0, EoCases.__eo_to_smt.case_54 x_a0, EoCases.__eo_to_smt.case_55 x_a0, EoCases.__eo_to_smt.case_56 x_a0, EoCases.__eo_to_smt.case_57 x_a0, EoCases.__eo_to_smt.case_58 x_a0, EoCases.__eo_to_smt.case_59 x_a0, EoCases.__eo_to_smt.case_60 x_a0, EoCases.__eo_to_smt.case_61 x_a0, EoCases.__eo_to_smt.case_62 x_a0, EoCases.__eo_to_smt.case_63 x_a0] = [EoCases.__eo_to_smt.case_48 x_a0, EoCases.__eo_to_smt.case_49 x_a0, EoCases.__eo_to_smt.case_50 x_a0, EoCases.__eo_to_smt.case_51 x_a0, EoCases.__eo_to_smt.case_52 x_a0, EoCases.__eo_to_smt.case_53 x_a0, EoCases.__eo_to_smt.case_54 x_a0, EoCases.__eo_to_smt.case_55 x_a0] ++ [EoCases.__eo_to_smt.case_56 x_a0, EoCases.__eo_to_smt.case_57 x_a0, EoCases.__eo_to_smt.case_58 x_a0, EoCases.__eo_to_smt.case_59 x_a0] ++ [EoCases.__eo_to_smt.case_60 x_a0, EoCases.__eo_to_smt.case_61 x_a0, EoCases.__eo_to_smt.case_62 x_a0, EoCases.__eo_to_smt.case_63 x_a0] from rfl)
    otherwise ⟨hl_56, hl_57, hl_58, hl_59⟩ using hl_48 hl_49 hl_50 hl_51 hl_52 hl_53 hl_54 hl_55
  group_step with cases_0_15_eo__24eo_5fto_5fsmt_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_48 x_a0, EoCases.__eo_to_smt.case_49 x_a0, EoCases.__eo_to_smt.case_50 x_a0, EoCases.__eo_to_smt.case_51 x_a0, EoCases.__eo_to_smt.case_52 x_a0, EoCases.__eo_to_smt.case_53 x_a0, EoCases.__eo_to_smt.case_54 x_a0, EoCases.__eo_to_smt.case_55 x_a0, EoCases.__eo_to_smt.case_56 x_a0, EoCases.__eo_to_smt.case_57 x_a0, EoCases.__eo_to_smt.case_58 x_a0, EoCases.__eo_to_smt.case_59 x_a0, EoCases.__eo_to_smt.case_60 x_a0, EoCases.__eo_to_smt.case_61 x_a0, EoCases.__eo_to_smt.case_62 x_a0, EoCases.__eo_to_smt.case_63 x_a0] = [EoCases.__eo_to_smt.case_48 x_a0, EoCases.__eo_to_smt.case_49 x_a0, EoCases.__eo_to_smt.case_50 x_a0, EoCases.__eo_to_smt.case_51 x_a0, EoCases.__eo_to_smt.case_52 x_a0, EoCases.__eo_to_smt.case_53 x_a0, EoCases.__eo_to_smt.case_54 x_a0, EoCases.__eo_to_smt.case_55 x_a0, EoCases.__eo_to_smt.case_56 x_a0, EoCases.__eo_to_smt.case_57 x_a0, EoCases.__eo_to_smt.case_58 x_a0, EoCases.__eo_to_smt.case_59 x_a0] ++ [EoCases.__eo_to_smt.case_60 x_a0, EoCases.__eo_to_smt.case_61 x_a0, EoCases.__eo_to_smt.case_62 x_a0, EoCases.__eo_to_smt.case_63 x_a0] ++ [] from rfl)
    otherwise ⟨hl_60, hl_61, hl_62, hl_63⟩ using hl_48 hl_49 hl_50 hl_51 hl_52 hl_53 hl_54 hl_55 hl_56 hl_57 hl_58 hl_59
  group_none hinv4 hG with ⟨hl_48, hl_49, hl_50, hl_51, hl_52, hl_53, hl_54, hl_55, hl_56, hl_57, hl_58, hl_59, hl_60, hl_61, hl_62, hl_63⟩

theorem cases_1_4_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_1_4_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_to_smt.case_64 x_a0, EoCases.__eo_to_smt.case_65 x_a0, EoCases.__eo_to_smt.case_66 x_a0, EoCases.__eo_to_smt.case_67 x_a0, EoCases.__eo_to_smt.case_68 x_a0, EoCases.__eo_to_smt.case_69 x_a0, EoCases.__eo_to_smt.case_70 x_a0, EoCases.__eo_to_smt.case_71 x_a0, EoCases.__eo_to_smt.case_72 x_a0, EoCases.__eo_to_smt.case_73 x_a0, EoCases.__eo_to_smt.case_74 x_a0, EoCases.__eo_to_smt.case_75 x_a0, EoCases.__eo_to_smt.case_76 x_a0, EoCases.__eo_to_smt.case_77 x_a0, EoCases.__eo_to_smt.case_78 x_a0, EoCases.__eo_to_smt.case_79 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_64 x_a0 = none ∧ EoCases.__eo_to_smt.case_65 x_a0 = none ∧ EoCases.__eo_to_smt.case_66 x_a0 = none ∧ EoCases.__eo_to_smt.case_67 x_a0 = none ∧ EoCases.__eo_to_smt.case_68 x_a0 = none ∧ EoCases.__eo_to_smt.case_69 x_a0 = none ∧ EoCases.__eo_to_smt.case_70 x_a0 = none ∧ EoCases.__eo_to_smt.case_71 x_a0 = none ∧ EoCases.__eo_to_smt.case_72 x_a0 = none ∧ EoCases.__eo_to_smt.case_73 x_a0 = none ∧ EoCases.__eo_to_smt.case_74 x_a0 = none ∧ EoCases.__eo_to_smt.case_75 x_a0 = none ∧ EoCases.__eo_to_smt.case_76 x_a0 = none ∧ EoCases.__eo_to_smt.case_77 x_a0 = none ∧ EoCases.__eo_to_smt.case_78 x_a0 = none ∧ EoCases.__eo_to_smt.case_79 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_1_4_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  group_step with cases_0_16_eo__24eo_5fto_5fsmt_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_64 x_a0, EoCases.__eo_to_smt.case_65 x_a0, EoCases.__eo_to_smt.case_66 x_a0, EoCases.__eo_to_smt.case_67 x_a0, EoCases.__eo_to_smt.case_68 x_a0, EoCases.__eo_to_smt.case_69 x_a0, EoCases.__eo_to_smt.case_70 x_a0, EoCases.__eo_to_smt.case_71 x_a0, EoCases.__eo_to_smt.case_72 x_a0, EoCases.__eo_to_smt.case_73 x_a0, EoCases.__eo_to_smt.case_74 x_a0, EoCases.__eo_to_smt.case_75 x_a0, EoCases.__eo_to_smt.case_76 x_a0, EoCases.__eo_to_smt.case_77 x_a0, EoCases.__eo_to_smt.case_78 x_a0, EoCases.__eo_to_smt.case_79 x_a0] = [] ++ [EoCases.__eo_to_smt.case_64 x_a0, EoCases.__eo_to_smt.case_65 x_a0, EoCases.__eo_to_smt.case_66 x_a0, EoCases.__eo_to_smt.case_67 x_a0] ++ [EoCases.__eo_to_smt.case_68 x_a0, EoCases.__eo_to_smt.case_69 x_a0, EoCases.__eo_to_smt.case_70 x_a0, EoCases.__eo_to_smt.case_71 x_a0, EoCases.__eo_to_smt.case_72 x_a0, EoCases.__eo_to_smt.case_73 x_a0, EoCases.__eo_to_smt.case_74 x_a0, EoCases.__eo_to_smt.case_75 x_a0, EoCases.__eo_to_smt.case_76 x_a0, EoCases.__eo_to_smt.case_77 x_a0, EoCases.__eo_to_smt.case_78 x_a0, EoCases.__eo_to_smt.case_79 x_a0] from rfl)
    otherwise ⟨hl_64, hl_65, hl_66, hl_67⟩ using
  group_step with cases_0_17_eo__24eo_5fto_5fsmt_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_64 x_a0, EoCases.__eo_to_smt.case_65 x_a0, EoCases.__eo_to_smt.case_66 x_a0, EoCases.__eo_to_smt.case_67 x_a0, EoCases.__eo_to_smt.case_68 x_a0, EoCases.__eo_to_smt.case_69 x_a0, EoCases.__eo_to_smt.case_70 x_a0, EoCases.__eo_to_smt.case_71 x_a0, EoCases.__eo_to_smt.case_72 x_a0, EoCases.__eo_to_smt.case_73 x_a0, EoCases.__eo_to_smt.case_74 x_a0, EoCases.__eo_to_smt.case_75 x_a0, EoCases.__eo_to_smt.case_76 x_a0, EoCases.__eo_to_smt.case_77 x_a0, EoCases.__eo_to_smt.case_78 x_a0, EoCases.__eo_to_smt.case_79 x_a0] = [EoCases.__eo_to_smt.case_64 x_a0, EoCases.__eo_to_smt.case_65 x_a0, EoCases.__eo_to_smt.case_66 x_a0, EoCases.__eo_to_smt.case_67 x_a0] ++ [EoCases.__eo_to_smt.case_68 x_a0, EoCases.__eo_to_smt.case_69 x_a0, EoCases.__eo_to_smt.case_70 x_a0, EoCases.__eo_to_smt.case_71 x_a0] ++ [EoCases.__eo_to_smt.case_72 x_a0, EoCases.__eo_to_smt.case_73 x_a0, EoCases.__eo_to_smt.case_74 x_a0, EoCases.__eo_to_smt.case_75 x_a0, EoCases.__eo_to_smt.case_76 x_a0, EoCases.__eo_to_smt.case_77 x_a0, EoCases.__eo_to_smt.case_78 x_a0, EoCases.__eo_to_smt.case_79 x_a0] from rfl)
    otherwise ⟨hl_68, hl_69, hl_70, hl_71⟩ using hl_64 hl_65 hl_66 hl_67
  group_step with cases_0_18_eo__24eo_5fto_5fsmt_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_64 x_a0, EoCases.__eo_to_smt.case_65 x_a0, EoCases.__eo_to_smt.case_66 x_a0, EoCases.__eo_to_smt.case_67 x_a0, EoCases.__eo_to_smt.case_68 x_a0, EoCases.__eo_to_smt.case_69 x_a0, EoCases.__eo_to_smt.case_70 x_a0, EoCases.__eo_to_smt.case_71 x_a0, EoCases.__eo_to_smt.case_72 x_a0, EoCases.__eo_to_smt.case_73 x_a0, EoCases.__eo_to_smt.case_74 x_a0, EoCases.__eo_to_smt.case_75 x_a0, EoCases.__eo_to_smt.case_76 x_a0, EoCases.__eo_to_smt.case_77 x_a0, EoCases.__eo_to_smt.case_78 x_a0, EoCases.__eo_to_smt.case_79 x_a0] = [EoCases.__eo_to_smt.case_64 x_a0, EoCases.__eo_to_smt.case_65 x_a0, EoCases.__eo_to_smt.case_66 x_a0, EoCases.__eo_to_smt.case_67 x_a0, EoCases.__eo_to_smt.case_68 x_a0, EoCases.__eo_to_smt.case_69 x_a0, EoCases.__eo_to_smt.case_70 x_a0, EoCases.__eo_to_smt.case_71 x_a0] ++ [EoCases.__eo_to_smt.case_72 x_a0, EoCases.__eo_to_smt.case_73 x_a0, EoCases.__eo_to_smt.case_74 x_a0, EoCases.__eo_to_smt.case_75 x_a0] ++ [EoCases.__eo_to_smt.case_76 x_a0, EoCases.__eo_to_smt.case_77 x_a0, EoCases.__eo_to_smt.case_78 x_a0, EoCases.__eo_to_smt.case_79 x_a0] from rfl)
    otherwise ⟨hl_72, hl_73, hl_74, hl_75⟩ using hl_64 hl_65 hl_66 hl_67 hl_68 hl_69 hl_70 hl_71
  group_step with cases_0_19_eo__24eo_5fto_5fsmt_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_64 x_a0, EoCases.__eo_to_smt.case_65 x_a0, EoCases.__eo_to_smt.case_66 x_a0, EoCases.__eo_to_smt.case_67 x_a0, EoCases.__eo_to_smt.case_68 x_a0, EoCases.__eo_to_smt.case_69 x_a0, EoCases.__eo_to_smt.case_70 x_a0, EoCases.__eo_to_smt.case_71 x_a0, EoCases.__eo_to_smt.case_72 x_a0, EoCases.__eo_to_smt.case_73 x_a0, EoCases.__eo_to_smt.case_74 x_a0, EoCases.__eo_to_smt.case_75 x_a0, EoCases.__eo_to_smt.case_76 x_a0, EoCases.__eo_to_smt.case_77 x_a0, EoCases.__eo_to_smt.case_78 x_a0, EoCases.__eo_to_smt.case_79 x_a0] = [EoCases.__eo_to_smt.case_64 x_a0, EoCases.__eo_to_smt.case_65 x_a0, EoCases.__eo_to_smt.case_66 x_a0, EoCases.__eo_to_smt.case_67 x_a0, EoCases.__eo_to_smt.case_68 x_a0, EoCases.__eo_to_smt.case_69 x_a0, EoCases.__eo_to_smt.case_70 x_a0, EoCases.__eo_to_smt.case_71 x_a0, EoCases.__eo_to_smt.case_72 x_a0, EoCases.__eo_to_smt.case_73 x_a0, EoCases.__eo_to_smt.case_74 x_a0, EoCases.__eo_to_smt.case_75 x_a0] ++ [EoCases.__eo_to_smt.case_76 x_a0, EoCases.__eo_to_smt.case_77 x_a0, EoCases.__eo_to_smt.case_78 x_a0, EoCases.__eo_to_smt.case_79 x_a0] ++ [] from rfl)
    otherwise ⟨hl_76, hl_77, hl_78, hl_79⟩ using hl_64 hl_65 hl_66 hl_67 hl_68 hl_69 hl_70 hl_71 hl_72 hl_73 hl_74 hl_75
  group_none hinv4 hG with ⟨hl_64, hl_65, hl_66, hl_67, hl_68, hl_69, hl_70, hl_71, hl_72, hl_73, hl_74, hl_75, hl_76, hl_77, hl_78, hl_79⟩

theorem cases_1_5_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_1_5_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_to_smt.case_80 x_a0, EoCases.__eo_to_smt.case_81 x_a0, EoCases.__eo_to_smt.case_82 x_a0, EoCases.__eo_to_smt.case_83 x_a0, EoCases.__eo_to_smt.case_84 x_a0, EoCases.__eo_to_smt.case_85 x_a0, EoCases.__eo_to_smt.case_86 x_a0, EoCases.__eo_to_smt.case_87 x_a0, EoCases.__eo_to_smt.case_88 x_a0, EoCases.__eo_to_smt.case_89 x_a0, EoCases.__eo_to_smt.case_90 x_a0, EoCases.__eo_to_smt.case_91 x_a0, EoCases.__eo_to_smt.case_92 x_a0, EoCases.__eo_to_smt.case_93 x_a0, EoCases.__eo_to_smt.case_94 x_a0, EoCases.__eo_to_smt.case_95 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_80 x_a0 = none ∧ EoCases.__eo_to_smt.case_81 x_a0 = none ∧ EoCases.__eo_to_smt.case_82 x_a0 = none ∧ EoCases.__eo_to_smt.case_83 x_a0 = none ∧ EoCases.__eo_to_smt.case_84 x_a0 = none ∧ EoCases.__eo_to_smt.case_85 x_a0 = none ∧ EoCases.__eo_to_smt.case_86 x_a0 = none ∧ EoCases.__eo_to_smt.case_87 x_a0 = none ∧ EoCases.__eo_to_smt.case_88 x_a0 = none ∧ EoCases.__eo_to_smt.case_89 x_a0 = none ∧ EoCases.__eo_to_smt.case_90 x_a0 = none ∧ EoCases.__eo_to_smt.case_91 x_a0 = none ∧ EoCases.__eo_to_smt.case_92 x_a0 = none ∧ EoCases.__eo_to_smt.case_93 x_a0 = none ∧ EoCases.__eo_to_smt.case_94 x_a0 = none ∧ EoCases.__eo_to_smt.case_95 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_1_5_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  group_step with cases_0_20_eo__24eo_5fto_5fsmt_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_80 x_a0, EoCases.__eo_to_smt.case_81 x_a0, EoCases.__eo_to_smt.case_82 x_a0, EoCases.__eo_to_smt.case_83 x_a0, EoCases.__eo_to_smt.case_84 x_a0, EoCases.__eo_to_smt.case_85 x_a0, EoCases.__eo_to_smt.case_86 x_a0, EoCases.__eo_to_smt.case_87 x_a0, EoCases.__eo_to_smt.case_88 x_a0, EoCases.__eo_to_smt.case_89 x_a0, EoCases.__eo_to_smt.case_90 x_a0, EoCases.__eo_to_smt.case_91 x_a0, EoCases.__eo_to_smt.case_92 x_a0, EoCases.__eo_to_smt.case_93 x_a0, EoCases.__eo_to_smt.case_94 x_a0, EoCases.__eo_to_smt.case_95 x_a0] = [] ++ [EoCases.__eo_to_smt.case_80 x_a0, EoCases.__eo_to_smt.case_81 x_a0, EoCases.__eo_to_smt.case_82 x_a0, EoCases.__eo_to_smt.case_83 x_a0] ++ [EoCases.__eo_to_smt.case_84 x_a0, EoCases.__eo_to_smt.case_85 x_a0, EoCases.__eo_to_smt.case_86 x_a0, EoCases.__eo_to_smt.case_87 x_a0, EoCases.__eo_to_smt.case_88 x_a0, EoCases.__eo_to_smt.case_89 x_a0, EoCases.__eo_to_smt.case_90 x_a0, EoCases.__eo_to_smt.case_91 x_a0, EoCases.__eo_to_smt.case_92 x_a0, EoCases.__eo_to_smt.case_93 x_a0, EoCases.__eo_to_smt.case_94 x_a0, EoCases.__eo_to_smt.case_95 x_a0] from rfl)
    otherwise ⟨hl_80, hl_81, hl_82, hl_83⟩ using
  group_step with cases_0_21_eo__24eo_5fto_5fsmt_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_80 x_a0, EoCases.__eo_to_smt.case_81 x_a0, EoCases.__eo_to_smt.case_82 x_a0, EoCases.__eo_to_smt.case_83 x_a0, EoCases.__eo_to_smt.case_84 x_a0, EoCases.__eo_to_smt.case_85 x_a0, EoCases.__eo_to_smt.case_86 x_a0, EoCases.__eo_to_smt.case_87 x_a0, EoCases.__eo_to_smt.case_88 x_a0, EoCases.__eo_to_smt.case_89 x_a0, EoCases.__eo_to_smt.case_90 x_a0, EoCases.__eo_to_smt.case_91 x_a0, EoCases.__eo_to_smt.case_92 x_a0, EoCases.__eo_to_smt.case_93 x_a0, EoCases.__eo_to_smt.case_94 x_a0, EoCases.__eo_to_smt.case_95 x_a0] = [EoCases.__eo_to_smt.case_80 x_a0, EoCases.__eo_to_smt.case_81 x_a0, EoCases.__eo_to_smt.case_82 x_a0, EoCases.__eo_to_smt.case_83 x_a0] ++ [EoCases.__eo_to_smt.case_84 x_a0, EoCases.__eo_to_smt.case_85 x_a0, EoCases.__eo_to_smt.case_86 x_a0, EoCases.__eo_to_smt.case_87 x_a0] ++ [EoCases.__eo_to_smt.case_88 x_a0, EoCases.__eo_to_smt.case_89 x_a0, EoCases.__eo_to_smt.case_90 x_a0, EoCases.__eo_to_smt.case_91 x_a0, EoCases.__eo_to_smt.case_92 x_a0, EoCases.__eo_to_smt.case_93 x_a0, EoCases.__eo_to_smt.case_94 x_a0, EoCases.__eo_to_smt.case_95 x_a0] from rfl)
    otherwise ⟨hl_84, hl_85, hl_86, hl_87⟩ using hl_80 hl_81 hl_82 hl_83
  group_step with cases_0_22_eo__24eo_5fto_5fsmt_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_80 x_a0, EoCases.__eo_to_smt.case_81 x_a0, EoCases.__eo_to_smt.case_82 x_a0, EoCases.__eo_to_smt.case_83 x_a0, EoCases.__eo_to_smt.case_84 x_a0, EoCases.__eo_to_smt.case_85 x_a0, EoCases.__eo_to_smt.case_86 x_a0, EoCases.__eo_to_smt.case_87 x_a0, EoCases.__eo_to_smt.case_88 x_a0, EoCases.__eo_to_smt.case_89 x_a0, EoCases.__eo_to_smt.case_90 x_a0, EoCases.__eo_to_smt.case_91 x_a0, EoCases.__eo_to_smt.case_92 x_a0, EoCases.__eo_to_smt.case_93 x_a0, EoCases.__eo_to_smt.case_94 x_a0, EoCases.__eo_to_smt.case_95 x_a0] = [EoCases.__eo_to_smt.case_80 x_a0, EoCases.__eo_to_smt.case_81 x_a0, EoCases.__eo_to_smt.case_82 x_a0, EoCases.__eo_to_smt.case_83 x_a0, EoCases.__eo_to_smt.case_84 x_a0, EoCases.__eo_to_smt.case_85 x_a0, EoCases.__eo_to_smt.case_86 x_a0, EoCases.__eo_to_smt.case_87 x_a0] ++ [EoCases.__eo_to_smt.case_88 x_a0, EoCases.__eo_to_smt.case_89 x_a0, EoCases.__eo_to_smt.case_90 x_a0, EoCases.__eo_to_smt.case_91 x_a0] ++ [EoCases.__eo_to_smt.case_92 x_a0, EoCases.__eo_to_smt.case_93 x_a0, EoCases.__eo_to_smt.case_94 x_a0, EoCases.__eo_to_smt.case_95 x_a0] from rfl)
    otherwise ⟨hl_88, hl_89, hl_90, hl_91⟩ using hl_80 hl_81 hl_82 hl_83 hl_84 hl_85 hl_86 hl_87
  group_step with cases_0_23_eo__24eo_5fto_5fsmt_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_80 x_a0, EoCases.__eo_to_smt.case_81 x_a0, EoCases.__eo_to_smt.case_82 x_a0, EoCases.__eo_to_smt.case_83 x_a0, EoCases.__eo_to_smt.case_84 x_a0, EoCases.__eo_to_smt.case_85 x_a0, EoCases.__eo_to_smt.case_86 x_a0, EoCases.__eo_to_smt.case_87 x_a0, EoCases.__eo_to_smt.case_88 x_a0, EoCases.__eo_to_smt.case_89 x_a0, EoCases.__eo_to_smt.case_90 x_a0, EoCases.__eo_to_smt.case_91 x_a0, EoCases.__eo_to_smt.case_92 x_a0, EoCases.__eo_to_smt.case_93 x_a0, EoCases.__eo_to_smt.case_94 x_a0, EoCases.__eo_to_smt.case_95 x_a0] = [EoCases.__eo_to_smt.case_80 x_a0, EoCases.__eo_to_smt.case_81 x_a0, EoCases.__eo_to_smt.case_82 x_a0, EoCases.__eo_to_smt.case_83 x_a0, EoCases.__eo_to_smt.case_84 x_a0, EoCases.__eo_to_smt.case_85 x_a0, EoCases.__eo_to_smt.case_86 x_a0, EoCases.__eo_to_smt.case_87 x_a0, EoCases.__eo_to_smt.case_88 x_a0, EoCases.__eo_to_smt.case_89 x_a0, EoCases.__eo_to_smt.case_90 x_a0, EoCases.__eo_to_smt.case_91 x_a0] ++ [EoCases.__eo_to_smt.case_92 x_a0, EoCases.__eo_to_smt.case_93 x_a0, EoCases.__eo_to_smt.case_94 x_a0, EoCases.__eo_to_smt.case_95 x_a0] ++ [] from rfl)
    otherwise ⟨hl_92, hl_93, hl_94, hl_95⟩ using hl_80 hl_81 hl_82 hl_83 hl_84 hl_85 hl_86 hl_87 hl_88 hl_89 hl_90 hl_91
  group_none hinv4 hG with ⟨hl_80, hl_81, hl_82, hl_83, hl_84, hl_85, hl_86, hl_87, hl_88, hl_89, hl_90, hl_91, hl_92, hl_93, hl_94, hl_95⟩

theorem cases_1_6_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_1_6_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_to_smt.case_96 x_a0, EoCases.__eo_to_smt.case_97 x_a0, EoCases.__eo_to_smt.case_98 x_a0, EoCases.__eo_to_smt.case_99 x_a0, EoCases.__eo_to_smt.case_100 x_a0, EoCases.__eo_to_smt.case_101 x_a0, EoCases.__eo_to_smt.case_102 x_a0, EoCases.__eo_to_smt.case_103 x_a0, EoCases.__eo_to_smt.case_104 x_a0, EoCases.__eo_to_smt.case_105 x_a0, EoCases.__eo_to_smt.case_106 x_a0, EoCases.__eo_to_smt.case_107 x_a0, EoCases.__eo_to_smt.case_108 x_a0, EoCases.__eo_to_smt.case_109 x_a0, EoCases.__eo_to_smt.case_110 x_a0, EoCases.__eo_to_smt.case_111 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_96 x_a0 = none ∧ EoCases.__eo_to_smt.case_97 x_a0 = none ∧ EoCases.__eo_to_smt.case_98 x_a0 = none ∧ EoCases.__eo_to_smt.case_99 x_a0 = none ∧ EoCases.__eo_to_smt.case_100 x_a0 = none ∧ EoCases.__eo_to_smt.case_101 x_a0 = none ∧ EoCases.__eo_to_smt.case_102 x_a0 = none ∧ EoCases.__eo_to_smt.case_103 x_a0 = none ∧ EoCases.__eo_to_smt.case_104 x_a0 = none ∧ EoCases.__eo_to_smt.case_105 x_a0 = none ∧ EoCases.__eo_to_smt.case_106 x_a0 = none ∧ EoCases.__eo_to_smt.case_107 x_a0 = none ∧ EoCases.__eo_to_smt.case_108 x_a0 = none ∧ EoCases.__eo_to_smt.case_109 x_a0 = none ∧ EoCases.__eo_to_smt.case_110 x_a0 = none ∧ EoCases.__eo_to_smt.case_111 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_1_6_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  group_step with cases_0_24_eo__24eo_5fto_5fsmt_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_96 x_a0, EoCases.__eo_to_smt.case_97 x_a0, EoCases.__eo_to_smt.case_98 x_a0, EoCases.__eo_to_smt.case_99 x_a0, EoCases.__eo_to_smt.case_100 x_a0, EoCases.__eo_to_smt.case_101 x_a0, EoCases.__eo_to_smt.case_102 x_a0, EoCases.__eo_to_smt.case_103 x_a0, EoCases.__eo_to_smt.case_104 x_a0, EoCases.__eo_to_smt.case_105 x_a0, EoCases.__eo_to_smt.case_106 x_a0, EoCases.__eo_to_smt.case_107 x_a0, EoCases.__eo_to_smt.case_108 x_a0, EoCases.__eo_to_smt.case_109 x_a0, EoCases.__eo_to_smt.case_110 x_a0, EoCases.__eo_to_smt.case_111 x_a0] = [] ++ [EoCases.__eo_to_smt.case_96 x_a0, EoCases.__eo_to_smt.case_97 x_a0, EoCases.__eo_to_smt.case_98 x_a0, EoCases.__eo_to_smt.case_99 x_a0] ++ [EoCases.__eo_to_smt.case_100 x_a0, EoCases.__eo_to_smt.case_101 x_a0, EoCases.__eo_to_smt.case_102 x_a0, EoCases.__eo_to_smt.case_103 x_a0, EoCases.__eo_to_smt.case_104 x_a0, EoCases.__eo_to_smt.case_105 x_a0, EoCases.__eo_to_smt.case_106 x_a0, EoCases.__eo_to_smt.case_107 x_a0, EoCases.__eo_to_smt.case_108 x_a0, EoCases.__eo_to_smt.case_109 x_a0, EoCases.__eo_to_smt.case_110 x_a0, EoCases.__eo_to_smt.case_111 x_a0] from rfl)
    otherwise ⟨hl_96, hl_97, hl_98, hl_99⟩ using
  group_step with cases_0_25_eo__24eo_5fto_5fsmt_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_96 x_a0, EoCases.__eo_to_smt.case_97 x_a0, EoCases.__eo_to_smt.case_98 x_a0, EoCases.__eo_to_smt.case_99 x_a0, EoCases.__eo_to_smt.case_100 x_a0, EoCases.__eo_to_smt.case_101 x_a0, EoCases.__eo_to_smt.case_102 x_a0, EoCases.__eo_to_smt.case_103 x_a0, EoCases.__eo_to_smt.case_104 x_a0, EoCases.__eo_to_smt.case_105 x_a0, EoCases.__eo_to_smt.case_106 x_a0, EoCases.__eo_to_smt.case_107 x_a0, EoCases.__eo_to_smt.case_108 x_a0, EoCases.__eo_to_smt.case_109 x_a0, EoCases.__eo_to_smt.case_110 x_a0, EoCases.__eo_to_smt.case_111 x_a0] = [EoCases.__eo_to_smt.case_96 x_a0, EoCases.__eo_to_smt.case_97 x_a0, EoCases.__eo_to_smt.case_98 x_a0, EoCases.__eo_to_smt.case_99 x_a0] ++ [EoCases.__eo_to_smt.case_100 x_a0, EoCases.__eo_to_smt.case_101 x_a0, EoCases.__eo_to_smt.case_102 x_a0, EoCases.__eo_to_smt.case_103 x_a0] ++ [EoCases.__eo_to_smt.case_104 x_a0, EoCases.__eo_to_smt.case_105 x_a0, EoCases.__eo_to_smt.case_106 x_a0, EoCases.__eo_to_smt.case_107 x_a0, EoCases.__eo_to_smt.case_108 x_a0, EoCases.__eo_to_smt.case_109 x_a0, EoCases.__eo_to_smt.case_110 x_a0, EoCases.__eo_to_smt.case_111 x_a0] from rfl)
    otherwise ⟨hl_100, hl_101, hl_102, hl_103⟩ using hl_96 hl_97 hl_98 hl_99
  group_step with cases_0_26_eo__24eo_5fto_5fsmt_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_96 x_a0, EoCases.__eo_to_smt.case_97 x_a0, EoCases.__eo_to_smt.case_98 x_a0, EoCases.__eo_to_smt.case_99 x_a0, EoCases.__eo_to_smt.case_100 x_a0, EoCases.__eo_to_smt.case_101 x_a0, EoCases.__eo_to_smt.case_102 x_a0, EoCases.__eo_to_smt.case_103 x_a0, EoCases.__eo_to_smt.case_104 x_a0, EoCases.__eo_to_smt.case_105 x_a0, EoCases.__eo_to_smt.case_106 x_a0, EoCases.__eo_to_smt.case_107 x_a0, EoCases.__eo_to_smt.case_108 x_a0, EoCases.__eo_to_smt.case_109 x_a0, EoCases.__eo_to_smt.case_110 x_a0, EoCases.__eo_to_smt.case_111 x_a0] = [EoCases.__eo_to_smt.case_96 x_a0, EoCases.__eo_to_smt.case_97 x_a0, EoCases.__eo_to_smt.case_98 x_a0, EoCases.__eo_to_smt.case_99 x_a0, EoCases.__eo_to_smt.case_100 x_a0, EoCases.__eo_to_smt.case_101 x_a0, EoCases.__eo_to_smt.case_102 x_a0, EoCases.__eo_to_smt.case_103 x_a0] ++ [EoCases.__eo_to_smt.case_104 x_a0, EoCases.__eo_to_smt.case_105 x_a0, EoCases.__eo_to_smt.case_106 x_a0, EoCases.__eo_to_smt.case_107 x_a0] ++ [EoCases.__eo_to_smt.case_108 x_a0, EoCases.__eo_to_smt.case_109 x_a0, EoCases.__eo_to_smt.case_110 x_a0, EoCases.__eo_to_smt.case_111 x_a0] from rfl)
    otherwise ⟨hl_104, hl_105, hl_106, hl_107⟩ using hl_96 hl_97 hl_98 hl_99 hl_100 hl_101 hl_102 hl_103
  group_step with cases_0_27_eo__24eo_5fto_5fsmt_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_96 x_a0, EoCases.__eo_to_smt.case_97 x_a0, EoCases.__eo_to_smt.case_98 x_a0, EoCases.__eo_to_smt.case_99 x_a0, EoCases.__eo_to_smt.case_100 x_a0, EoCases.__eo_to_smt.case_101 x_a0, EoCases.__eo_to_smt.case_102 x_a0, EoCases.__eo_to_smt.case_103 x_a0, EoCases.__eo_to_smt.case_104 x_a0, EoCases.__eo_to_smt.case_105 x_a0, EoCases.__eo_to_smt.case_106 x_a0, EoCases.__eo_to_smt.case_107 x_a0, EoCases.__eo_to_smt.case_108 x_a0, EoCases.__eo_to_smt.case_109 x_a0, EoCases.__eo_to_smt.case_110 x_a0, EoCases.__eo_to_smt.case_111 x_a0] = [EoCases.__eo_to_smt.case_96 x_a0, EoCases.__eo_to_smt.case_97 x_a0, EoCases.__eo_to_smt.case_98 x_a0, EoCases.__eo_to_smt.case_99 x_a0, EoCases.__eo_to_smt.case_100 x_a0, EoCases.__eo_to_smt.case_101 x_a0, EoCases.__eo_to_smt.case_102 x_a0, EoCases.__eo_to_smt.case_103 x_a0, EoCases.__eo_to_smt.case_104 x_a0, EoCases.__eo_to_smt.case_105 x_a0, EoCases.__eo_to_smt.case_106 x_a0, EoCases.__eo_to_smt.case_107 x_a0] ++ [EoCases.__eo_to_smt.case_108 x_a0, EoCases.__eo_to_smt.case_109 x_a0, EoCases.__eo_to_smt.case_110 x_a0, EoCases.__eo_to_smt.case_111 x_a0] ++ [] from rfl)
    otherwise ⟨hl_108, hl_109, hl_110, hl_111⟩ using hl_96 hl_97 hl_98 hl_99 hl_100 hl_101 hl_102 hl_103 hl_104 hl_105 hl_106 hl_107
  group_none hinv4 hG with ⟨hl_96, hl_97, hl_98, hl_99, hl_100, hl_101, hl_102, hl_103, hl_104, hl_105, hl_106, hl_107, hl_108, hl_109, hl_110, hl_111⟩

theorem cases_1_7_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_1_7_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_to_smt.case_112 x_a0, EoCases.__eo_to_smt.case_113 x_a0, EoCases.__eo_to_smt.case_114 x_a0, EoCases.__eo_to_smt.case_115 x_a0, EoCases.__eo_to_smt.case_116 x_a0, EoCases.__eo_to_smt.case_117 x_a0, EoCases.__eo_to_smt.case_118 x_a0, EoCases.__eo_to_smt.case_119 x_a0, EoCases.__eo_to_smt.case_120 x_a0, EoCases.__eo_to_smt.case_121 x_a0, EoCases.__eo_to_smt.case_122 x_a0, EoCases.__eo_to_smt.case_123 x_a0, EoCases.__eo_to_smt.case_124 x_a0, EoCases.__eo_to_smt.case_125 x_a0, EoCases.__eo_to_smt.case_126 x_a0, EoCases.__eo_to_smt.case_127 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_112 x_a0 = none ∧ EoCases.__eo_to_smt.case_113 x_a0 = none ∧ EoCases.__eo_to_smt.case_114 x_a0 = none ∧ EoCases.__eo_to_smt.case_115 x_a0 = none ∧ EoCases.__eo_to_smt.case_116 x_a0 = none ∧ EoCases.__eo_to_smt.case_117 x_a0 = none ∧ EoCases.__eo_to_smt.case_118 x_a0 = none ∧ EoCases.__eo_to_smt.case_119 x_a0 = none ∧ EoCases.__eo_to_smt.case_120 x_a0 = none ∧ EoCases.__eo_to_smt.case_121 x_a0 = none ∧ EoCases.__eo_to_smt.case_122 x_a0 = none ∧ EoCases.__eo_to_smt.case_123 x_a0 = none ∧ EoCases.__eo_to_smt.case_124 x_a0 = none ∧ EoCases.__eo_to_smt.case_125 x_a0 = none ∧ EoCases.__eo_to_smt.case_126 x_a0 = none ∧ EoCases.__eo_to_smt.case_127 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_1_7_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  group_step with cases_0_28_eo__24eo_5fto_5fsmt_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_112 x_a0, EoCases.__eo_to_smt.case_113 x_a0, EoCases.__eo_to_smt.case_114 x_a0, EoCases.__eo_to_smt.case_115 x_a0, EoCases.__eo_to_smt.case_116 x_a0, EoCases.__eo_to_smt.case_117 x_a0, EoCases.__eo_to_smt.case_118 x_a0, EoCases.__eo_to_smt.case_119 x_a0, EoCases.__eo_to_smt.case_120 x_a0, EoCases.__eo_to_smt.case_121 x_a0, EoCases.__eo_to_smt.case_122 x_a0, EoCases.__eo_to_smt.case_123 x_a0, EoCases.__eo_to_smt.case_124 x_a0, EoCases.__eo_to_smt.case_125 x_a0, EoCases.__eo_to_smt.case_126 x_a0, EoCases.__eo_to_smt.case_127 x_a0] = [] ++ [EoCases.__eo_to_smt.case_112 x_a0, EoCases.__eo_to_smt.case_113 x_a0, EoCases.__eo_to_smt.case_114 x_a0, EoCases.__eo_to_smt.case_115 x_a0] ++ [EoCases.__eo_to_smt.case_116 x_a0, EoCases.__eo_to_smt.case_117 x_a0, EoCases.__eo_to_smt.case_118 x_a0, EoCases.__eo_to_smt.case_119 x_a0, EoCases.__eo_to_smt.case_120 x_a0, EoCases.__eo_to_smt.case_121 x_a0, EoCases.__eo_to_smt.case_122 x_a0, EoCases.__eo_to_smt.case_123 x_a0, EoCases.__eo_to_smt.case_124 x_a0, EoCases.__eo_to_smt.case_125 x_a0, EoCases.__eo_to_smt.case_126 x_a0, EoCases.__eo_to_smt.case_127 x_a0] from rfl)
    otherwise ⟨hl_112, hl_113, hl_114, hl_115⟩ using
  group_step with cases_0_29_eo__24eo_5fto_5fsmt_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_112 x_a0, EoCases.__eo_to_smt.case_113 x_a0, EoCases.__eo_to_smt.case_114 x_a0, EoCases.__eo_to_smt.case_115 x_a0, EoCases.__eo_to_smt.case_116 x_a0, EoCases.__eo_to_smt.case_117 x_a0, EoCases.__eo_to_smt.case_118 x_a0, EoCases.__eo_to_smt.case_119 x_a0, EoCases.__eo_to_smt.case_120 x_a0, EoCases.__eo_to_smt.case_121 x_a0, EoCases.__eo_to_smt.case_122 x_a0, EoCases.__eo_to_smt.case_123 x_a0, EoCases.__eo_to_smt.case_124 x_a0, EoCases.__eo_to_smt.case_125 x_a0, EoCases.__eo_to_smt.case_126 x_a0, EoCases.__eo_to_smt.case_127 x_a0] = [EoCases.__eo_to_smt.case_112 x_a0, EoCases.__eo_to_smt.case_113 x_a0, EoCases.__eo_to_smt.case_114 x_a0, EoCases.__eo_to_smt.case_115 x_a0] ++ [EoCases.__eo_to_smt.case_116 x_a0, EoCases.__eo_to_smt.case_117 x_a0, EoCases.__eo_to_smt.case_118 x_a0, EoCases.__eo_to_smt.case_119 x_a0] ++ [EoCases.__eo_to_smt.case_120 x_a0, EoCases.__eo_to_smt.case_121 x_a0, EoCases.__eo_to_smt.case_122 x_a0, EoCases.__eo_to_smt.case_123 x_a0, EoCases.__eo_to_smt.case_124 x_a0, EoCases.__eo_to_smt.case_125 x_a0, EoCases.__eo_to_smt.case_126 x_a0, EoCases.__eo_to_smt.case_127 x_a0] from rfl)
    otherwise ⟨hl_116, hl_117, hl_118, hl_119⟩ using hl_112 hl_113 hl_114 hl_115
  group_step with cases_0_30_eo__24eo_5fto_5fsmt_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_112 x_a0, EoCases.__eo_to_smt.case_113 x_a0, EoCases.__eo_to_smt.case_114 x_a0, EoCases.__eo_to_smt.case_115 x_a0, EoCases.__eo_to_smt.case_116 x_a0, EoCases.__eo_to_smt.case_117 x_a0, EoCases.__eo_to_smt.case_118 x_a0, EoCases.__eo_to_smt.case_119 x_a0, EoCases.__eo_to_smt.case_120 x_a0, EoCases.__eo_to_smt.case_121 x_a0, EoCases.__eo_to_smt.case_122 x_a0, EoCases.__eo_to_smt.case_123 x_a0, EoCases.__eo_to_smt.case_124 x_a0, EoCases.__eo_to_smt.case_125 x_a0, EoCases.__eo_to_smt.case_126 x_a0, EoCases.__eo_to_smt.case_127 x_a0] = [EoCases.__eo_to_smt.case_112 x_a0, EoCases.__eo_to_smt.case_113 x_a0, EoCases.__eo_to_smt.case_114 x_a0, EoCases.__eo_to_smt.case_115 x_a0, EoCases.__eo_to_smt.case_116 x_a0, EoCases.__eo_to_smt.case_117 x_a0, EoCases.__eo_to_smt.case_118 x_a0, EoCases.__eo_to_smt.case_119 x_a0] ++ [EoCases.__eo_to_smt.case_120 x_a0, EoCases.__eo_to_smt.case_121 x_a0, EoCases.__eo_to_smt.case_122 x_a0, EoCases.__eo_to_smt.case_123 x_a0] ++ [EoCases.__eo_to_smt.case_124 x_a0, EoCases.__eo_to_smt.case_125 x_a0, EoCases.__eo_to_smt.case_126 x_a0, EoCases.__eo_to_smt.case_127 x_a0] from rfl)
    otherwise ⟨hl_120, hl_121, hl_122, hl_123⟩ using hl_112 hl_113 hl_114 hl_115 hl_116 hl_117 hl_118 hl_119
  group_step with cases_0_31_eo__24eo_5fto_5fsmt_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_112 x_a0, EoCases.__eo_to_smt.case_113 x_a0, EoCases.__eo_to_smt.case_114 x_a0, EoCases.__eo_to_smt.case_115 x_a0, EoCases.__eo_to_smt.case_116 x_a0, EoCases.__eo_to_smt.case_117 x_a0, EoCases.__eo_to_smt.case_118 x_a0, EoCases.__eo_to_smt.case_119 x_a0, EoCases.__eo_to_smt.case_120 x_a0, EoCases.__eo_to_smt.case_121 x_a0, EoCases.__eo_to_smt.case_122 x_a0, EoCases.__eo_to_smt.case_123 x_a0, EoCases.__eo_to_smt.case_124 x_a0, EoCases.__eo_to_smt.case_125 x_a0, EoCases.__eo_to_smt.case_126 x_a0, EoCases.__eo_to_smt.case_127 x_a0] = [EoCases.__eo_to_smt.case_112 x_a0, EoCases.__eo_to_smt.case_113 x_a0, EoCases.__eo_to_smt.case_114 x_a0, EoCases.__eo_to_smt.case_115 x_a0, EoCases.__eo_to_smt.case_116 x_a0, EoCases.__eo_to_smt.case_117 x_a0, EoCases.__eo_to_smt.case_118 x_a0, EoCases.__eo_to_smt.case_119 x_a0, EoCases.__eo_to_smt.case_120 x_a0, EoCases.__eo_to_smt.case_121 x_a0, EoCases.__eo_to_smt.case_122 x_a0, EoCases.__eo_to_smt.case_123 x_a0] ++ [EoCases.__eo_to_smt.case_124 x_a0, EoCases.__eo_to_smt.case_125 x_a0, EoCases.__eo_to_smt.case_126 x_a0, EoCases.__eo_to_smt.case_127 x_a0] ++ [] from rfl)
    otherwise ⟨hl_124, hl_125, hl_126, hl_127⟩ using hl_112 hl_113 hl_114 hl_115 hl_116 hl_117 hl_118 hl_119 hl_120 hl_121 hl_122 hl_123
  group_none hinv4 hG with ⟨hl_112, hl_113, hl_114, hl_115, hl_116, hl_117, hl_118, hl_119, hl_120, hl_121, hl_122, hl_123, hl_124, hl_125, hl_126, hl_127⟩

theorem cases_1_8_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_1_8_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_to_smt.case_128 x_a0, EoCases.__eo_to_smt.case_129 x_a0, EoCases.__eo_to_smt.case_130 x_a0, EoCases.__eo_to_smt.case_131 x_a0, EoCases.__eo_to_smt.case_132 x_a0, EoCases.__eo_to_smt.case_133 x_a0, EoCases.__eo_to_smt.case_134 x_a0, EoCases.__eo_to_smt.case_135 x_a0, EoCases.__eo_to_smt.case_136 x_a0, EoCases.__eo_to_smt.case_137 x_a0, EoCases.__eo_to_smt.case_138 x_a0, EoCases.__eo_to_smt.case_139 x_a0, EoCases.__eo_to_smt.case_140 x_a0, EoCases.__eo_to_smt.case_141 x_a0, EoCases.__eo_to_smt.case_142 x_a0, EoCases.__eo_to_smt.case_143 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_128 x_a0 = none ∧ EoCases.__eo_to_smt.case_129 x_a0 = none ∧ EoCases.__eo_to_smt.case_130 x_a0 = none ∧ EoCases.__eo_to_smt.case_131 x_a0 = none ∧ EoCases.__eo_to_smt.case_132 x_a0 = none ∧ EoCases.__eo_to_smt.case_133 x_a0 = none ∧ EoCases.__eo_to_smt.case_134 x_a0 = none ∧ EoCases.__eo_to_smt.case_135 x_a0 = none ∧ EoCases.__eo_to_smt.case_136 x_a0 = none ∧ EoCases.__eo_to_smt.case_137 x_a0 = none ∧ EoCases.__eo_to_smt.case_138 x_a0 = none ∧ EoCases.__eo_to_smt.case_139 x_a0 = none ∧ EoCases.__eo_to_smt.case_140 x_a0 = none ∧ EoCases.__eo_to_smt.case_141 x_a0 = none ∧ EoCases.__eo_to_smt.case_142 x_a0 = none ∧ EoCases.__eo_to_smt.case_143 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_1_8_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  group_step with cases_0_32_eo__24eo_5fto_5fsmt_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_128 x_a0, EoCases.__eo_to_smt.case_129 x_a0, EoCases.__eo_to_smt.case_130 x_a0, EoCases.__eo_to_smt.case_131 x_a0, EoCases.__eo_to_smt.case_132 x_a0, EoCases.__eo_to_smt.case_133 x_a0, EoCases.__eo_to_smt.case_134 x_a0, EoCases.__eo_to_smt.case_135 x_a0, EoCases.__eo_to_smt.case_136 x_a0, EoCases.__eo_to_smt.case_137 x_a0, EoCases.__eo_to_smt.case_138 x_a0, EoCases.__eo_to_smt.case_139 x_a0, EoCases.__eo_to_smt.case_140 x_a0, EoCases.__eo_to_smt.case_141 x_a0, EoCases.__eo_to_smt.case_142 x_a0, EoCases.__eo_to_smt.case_143 x_a0] = [] ++ [EoCases.__eo_to_smt.case_128 x_a0, EoCases.__eo_to_smt.case_129 x_a0, EoCases.__eo_to_smt.case_130 x_a0, EoCases.__eo_to_smt.case_131 x_a0] ++ [EoCases.__eo_to_smt.case_132 x_a0, EoCases.__eo_to_smt.case_133 x_a0, EoCases.__eo_to_smt.case_134 x_a0, EoCases.__eo_to_smt.case_135 x_a0, EoCases.__eo_to_smt.case_136 x_a0, EoCases.__eo_to_smt.case_137 x_a0, EoCases.__eo_to_smt.case_138 x_a0, EoCases.__eo_to_smt.case_139 x_a0, EoCases.__eo_to_smt.case_140 x_a0, EoCases.__eo_to_smt.case_141 x_a0, EoCases.__eo_to_smt.case_142 x_a0, EoCases.__eo_to_smt.case_143 x_a0] from rfl)
    otherwise ⟨hl_128, hl_129, hl_130, hl_131⟩ using
  group_step with cases_0_33_eo__24eo_5fto_5fsmt_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_128 x_a0, EoCases.__eo_to_smt.case_129 x_a0, EoCases.__eo_to_smt.case_130 x_a0, EoCases.__eo_to_smt.case_131 x_a0, EoCases.__eo_to_smt.case_132 x_a0, EoCases.__eo_to_smt.case_133 x_a0, EoCases.__eo_to_smt.case_134 x_a0, EoCases.__eo_to_smt.case_135 x_a0, EoCases.__eo_to_smt.case_136 x_a0, EoCases.__eo_to_smt.case_137 x_a0, EoCases.__eo_to_smt.case_138 x_a0, EoCases.__eo_to_smt.case_139 x_a0, EoCases.__eo_to_smt.case_140 x_a0, EoCases.__eo_to_smt.case_141 x_a0, EoCases.__eo_to_smt.case_142 x_a0, EoCases.__eo_to_smt.case_143 x_a0] = [EoCases.__eo_to_smt.case_128 x_a0, EoCases.__eo_to_smt.case_129 x_a0, EoCases.__eo_to_smt.case_130 x_a0, EoCases.__eo_to_smt.case_131 x_a0] ++ [EoCases.__eo_to_smt.case_132 x_a0, EoCases.__eo_to_smt.case_133 x_a0, EoCases.__eo_to_smt.case_134 x_a0, EoCases.__eo_to_smt.case_135 x_a0] ++ [EoCases.__eo_to_smt.case_136 x_a0, EoCases.__eo_to_smt.case_137 x_a0, EoCases.__eo_to_smt.case_138 x_a0, EoCases.__eo_to_smt.case_139 x_a0, EoCases.__eo_to_smt.case_140 x_a0, EoCases.__eo_to_smt.case_141 x_a0, EoCases.__eo_to_smt.case_142 x_a0, EoCases.__eo_to_smt.case_143 x_a0] from rfl)
    otherwise ⟨hl_132, hl_133, hl_134, hl_135⟩ using hl_128 hl_129 hl_130 hl_131
  group_step with cases_0_34_eo__24eo_5fto_5fsmt_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_128 x_a0, EoCases.__eo_to_smt.case_129 x_a0, EoCases.__eo_to_smt.case_130 x_a0, EoCases.__eo_to_smt.case_131 x_a0, EoCases.__eo_to_smt.case_132 x_a0, EoCases.__eo_to_smt.case_133 x_a0, EoCases.__eo_to_smt.case_134 x_a0, EoCases.__eo_to_smt.case_135 x_a0, EoCases.__eo_to_smt.case_136 x_a0, EoCases.__eo_to_smt.case_137 x_a0, EoCases.__eo_to_smt.case_138 x_a0, EoCases.__eo_to_smt.case_139 x_a0, EoCases.__eo_to_smt.case_140 x_a0, EoCases.__eo_to_smt.case_141 x_a0, EoCases.__eo_to_smt.case_142 x_a0, EoCases.__eo_to_smt.case_143 x_a0] = [EoCases.__eo_to_smt.case_128 x_a0, EoCases.__eo_to_smt.case_129 x_a0, EoCases.__eo_to_smt.case_130 x_a0, EoCases.__eo_to_smt.case_131 x_a0, EoCases.__eo_to_smt.case_132 x_a0, EoCases.__eo_to_smt.case_133 x_a0, EoCases.__eo_to_smt.case_134 x_a0, EoCases.__eo_to_smt.case_135 x_a0] ++ [EoCases.__eo_to_smt.case_136 x_a0, EoCases.__eo_to_smt.case_137 x_a0, EoCases.__eo_to_smt.case_138 x_a0, EoCases.__eo_to_smt.case_139 x_a0] ++ [EoCases.__eo_to_smt.case_140 x_a0, EoCases.__eo_to_smt.case_141 x_a0, EoCases.__eo_to_smt.case_142 x_a0, EoCases.__eo_to_smt.case_143 x_a0] from rfl)
    otherwise ⟨hl_136, hl_137, hl_138, hl_139⟩ using hl_128 hl_129 hl_130 hl_131 hl_132 hl_133 hl_134 hl_135
  group_step with cases_0_35_eo__24eo_5fto_5fsmt_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_128 x_a0, EoCases.__eo_to_smt.case_129 x_a0, EoCases.__eo_to_smt.case_130 x_a0, EoCases.__eo_to_smt.case_131 x_a0, EoCases.__eo_to_smt.case_132 x_a0, EoCases.__eo_to_smt.case_133 x_a0, EoCases.__eo_to_smt.case_134 x_a0, EoCases.__eo_to_smt.case_135 x_a0, EoCases.__eo_to_smt.case_136 x_a0, EoCases.__eo_to_smt.case_137 x_a0, EoCases.__eo_to_smt.case_138 x_a0, EoCases.__eo_to_smt.case_139 x_a0, EoCases.__eo_to_smt.case_140 x_a0, EoCases.__eo_to_smt.case_141 x_a0, EoCases.__eo_to_smt.case_142 x_a0, EoCases.__eo_to_smt.case_143 x_a0] = [EoCases.__eo_to_smt.case_128 x_a0, EoCases.__eo_to_smt.case_129 x_a0, EoCases.__eo_to_smt.case_130 x_a0, EoCases.__eo_to_smt.case_131 x_a0, EoCases.__eo_to_smt.case_132 x_a0, EoCases.__eo_to_smt.case_133 x_a0, EoCases.__eo_to_smt.case_134 x_a0, EoCases.__eo_to_smt.case_135 x_a0, EoCases.__eo_to_smt.case_136 x_a0, EoCases.__eo_to_smt.case_137 x_a0, EoCases.__eo_to_smt.case_138 x_a0, EoCases.__eo_to_smt.case_139 x_a0] ++ [EoCases.__eo_to_smt.case_140 x_a0, EoCases.__eo_to_smt.case_141 x_a0, EoCases.__eo_to_smt.case_142 x_a0, EoCases.__eo_to_smt.case_143 x_a0] ++ [] from rfl)
    otherwise ⟨hl_140, hl_141, hl_142, hl_143⟩ using hl_128 hl_129 hl_130 hl_131 hl_132 hl_133 hl_134 hl_135 hl_136 hl_137 hl_138 hl_139
  group_none hinv4 hG with ⟨hl_128, hl_129, hl_130, hl_131, hl_132, hl_133, hl_134, hl_135, hl_136, hl_137, hl_138, hl_139, hl_140, hl_141, hl_142, hl_143⟩

theorem cases_1_9_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_1_9_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_to_smt.case_144 x_a0, EoCases.__eo_to_smt.case_145 x_a0, EoCases.__eo_to_smt.case_146 x_a0, EoCases.__eo_to_smt.case_147 x_a0, EoCases.__eo_to_smt.case_148 x_a0, EoCases.__eo_to_smt.case_149 x_a0, EoCases.__eo_to_smt.case_150 x_a0, EoCases.__eo_to_smt.case_151 x_a0, EoCases.__eo_to_smt.case_152 x_a0, EoCases.__eo_to_smt.case_153 x_a0, EoCases.__eo_to_smt.case_154 x_a0, EoCases.__eo_to_smt.case_155 x_a0, EoCases.__eo_to_smt.case_156 x_a0, EoCases.__eo_to_smt.case_157 x_a0, EoCases.__eo_to_smt.case_158 x_a0, EoCases.__eo_to_smt.case_159 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_144 x_a0 = none ∧ EoCases.__eo_to_smt.case_145 x_a0 = none ∧ EoCases.__eo_to_smt.case_146 x_a0 = none ∧ EoCases.__eo_to_smt.case_147 x_a0 = none ∧ EoCases.__eo_to_smt.case_148 x_a0 = none ∧ EoCases.__eo_to_smt.case_149 x_a0 = none ∧ EoCases.__eo_to_smt.case_150 x_a0 = none ∧ EoCases.__eo_to_smt.case_151 x_a0 = none ∧ EoCases.__eo_to_smt.case_152 x_a0 = none ∧ EoCases.__eo_to_smt.case_153 x_a0 = none ∧ EoCases.__eo_to_smt.case_154 x_a0 = none ∧ EoCases.__eo_to_smt.case_155 x_a0 = none ∧ EoCases.__eo_to_smt.case_156 x_a0 = none ∧ EoCases.__eo_to_smt.case_157 x_a0 = none ∧ EoCases.__eo_to_smt.case_158 x_a0 = none ∧ EoCases.__eo_to_smt.case_159 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_1_9_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  group_step with cases_0_36_eo__24eo_5fto_5fsmt_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_144 x_a0, EoCases.__eo_to_smt.case_145 x_a0, EoCases.__eo_to_smt.case_146 x_a0, EoCases.__eo_to_smt.case_147 x_a0, EoCases.__eo_to_smt.case_148 x_a0, EoCases.__eo_to_smt.case_149 x_a0, EoCases.__eo_to_smt.case_150 x_a0, EoCases.__eo_to_smt.case_151 x_a0, EoCases.__eo_to_smt.case_152 x_a0, EoCases.__eo_to_smt.case_153 x_a0, EoCases.__eo_to_smt.case_154 x_a0, EoCases.__eo_to_smt.case_155 x_a0, EoCases.__eo_to_smt.case_156 x_a0, EoCases.__eo_to_smt.case_157 x_a0, EoCases.__eo_to_smt.case_158 x_a0, EoCases.__eo_to_smt.case_159 x_a0] = [] ++ [EoCases.__eo_to_smt.case_144 x_a0, EoCases.__eo_to_smt.case_145 x_a0, EoCases.__eo_to_smt.case_146 x_a0, EoCases.__eo_to_smt.case_147 x_a0] ++ [EoCases.__eo_to_smt.case_148 x_a0, EoCases.__eo_to_smt.case_149 x_a0, EoCases.__eo_to_smt.case_150 x_a0, EoCases.__eo_to_smt.case_151 x_a0, EoCases.__eo_to_smt.case_152 x_a0, EoCases.__eo_to_smt.case_153 x_a0, EoCases.__eo_to_smt.case_154 x_a0, EoCases.__eo_to_smt.case_155 x_a0, EoCases.__eo_to_smt.case_156 x_a0, EoCases.__eo_to_smt.case_157 x_a0, EoCases.__eo_to_smt.case_158 x_a0, EoCases.__eo_to_smt.case_159 x_a0] from rfl)
    otherwise ⟨hl_144, hl_145, hl_146, hl_147⟩ using
  group_step with cases_0_37_eo__24eo_5fto_5fsmt_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_144 x_a0, EoCases.__eo_to_smt.case_145 x_a0, EoCases.__eo_to_smt.case_146 x_a0, EoCases.__eo_to_smt.case_147 x_a0, EoCases.__eo_to_smt.case_148 x_a0, EoCases.__eo_to_smt.case_149 x_a0, EoCases.__eo_to_smt.case_150 x_a0, EoCases.__eo_to_smt.case_151 x_a0, EoCases.__eo_to_smt.case_152 x_a0, EoCases.__eo_to_smt.case_153 x_a0, EoCases.__eo_to_smt.case_154 x_a0, EoCases.__eo_to_smt.case_155 x_a0, EoCases.__eo_to_smt.case_156 x_a0, EoCases.__eo_to_smt.case_157 x_a0, EoCases.__eo_to_smt.case_158 x_a0, EoCases.__eo_to_smt.case_159 x_a0] = [EoCases.__eo_to_smt.case_144 x_a0, EoCases.__eo_to_smt.case_145 x_a0, EoCases.__eo_to_smt.case_146 x_a0, EoCases.__eo_to_smt.case_147 x_a0] ++ [EoCases.__eo_to_smt.case_148 x_a0, EoCases.__eo_to_smt.case_149 x_a0, EoCases.__eo_to_smt.case_150 x_a0, EoCases.__eo_to_smt.case_151 x_a0] ++ [EoCases.__eo_to_smt.case_152 x_a0, EoCases.__eo_to_smt.case_153 x_a0, EoCases.__eo_to_smt.case_154 x_a0, EoCases.__eo_to_smt.case_155 x_a0, EoCases.__eo_to_smt.case_156 x_a0, EoCases.__eo_to_smt.case_157 x_a0, EoCases.__eo_to_smt.case_158 x_a0, EoCases.__eo_to_smt.case_159 x_a0] from rfl)
    otherwise ⟨hl_148, hl_149, hl_150, hl_151⟩ using hl_144 hl_145 hl_146 hl_147
  group_step with cases_0_38_eo__24eo_5fto_5fsmt_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_144 x_a0, EoCases.__eo_to_smt.case_145 x_a0, EoCases.__eo_to_smt.case_146 x_a0, EoCases.__eo_to_smt.case_147 x_a0, EoCases.__eo_to_smt.case_148 x_a0, EoCases.__eo_to_smt.case_149 x_a0, EoCases.__eo_to_smt.case_150 x_a0, EoCases.__eo_to_smt.case_151 x_a0, EoCases.__eo_to_smt.case_152 x_a0, EoCases.__eo_to_smt.case_153 x_a0, EoCases.__eo_to_smt.case_154 x_a0, EoCases.__eo_to_smt.case_155 x_a0, EoCases.__eo_to_smt.case_156 x_a0, EoCases.__eo_to_smt.case_157 x_a0, EoCases.__eo_to_smt.case_158 x_a0, EoCases.__eo_to_smt.case_159 x_a0] = [EoCases.__eo_to_smt.case_144 x_a0, EoCases.__eo_to_smt.case_145 x_a0, EoCases.__eo_to_smt.case_146 x_a0, EoCases.__eo_to_smt.case_147 x_a0, EoCases.__eo_to_smt.case_148 x_a0, EoCases.__eo_to_smt.case_149 x_a0, EoCases.__eo_to_smt.case_150 x_a0, EoCases.__eo_to_smt.case_151 x_a0] ++ [EoCases.__eo_to_smt.case_152 x_a0, EoCases.__eo_to_smt.case_153 x_a0, EoCases.__eo_to_smt.case_154 x_a0, EoCases.__eo_to_smt.case_155 x_a0] ++ [EoCases.__eo_to_smt.case_156 x_a0, EoCases.__eo_to_smt.case_157 x_a0, EoCases.__eo_to_smt.case_158 x_a0, EoCases.__eo_to_smt.case_159 x_a0] from rfl)
    otherwise ⟨hl_152, hl_153, hl_154, hl_155⟩ using hl_144 hl_145 hl_146 hl_147 hl_148 hl_149 hl_150 hl_151
  group_step with cases_0_39_eo__24eo_5fto_5fsmt_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_144 x_a0, EoCases.__eo_to_smt.case_145 x_a0, EoCases.__eo_to_smt.case_146 x_a0, EoCases.__eo_to_smt.case_147 x_a0, EoCases.__eo_to_smt.case_148 x_a0, EoCases.__eo_to_smt.case_149 x_a0, EoCases.__eo_to_smt.case_150 x_a0, EoCases.__eo_to_smt.case_151 x_a0, EoCases.__eo_to_smt.case_152 x_a0, EoCases.__eo_to_smt.case_153 x_a0, EoCases.__eo_to_smt.case_154 x_a0, EoCases.__eo_to_smt.case_155 x_a0, EoCases.__eo_to_smt.case_156 x_a0, EoCases.__eo_to_smt.case_157 x_a0, EoCases.__eo_to_smt.case_158 x_a0, EoCases.__eo_to_smt.case_159 x_a0] = [EoCases.__eo_to_smt.case_144 x_a0, EoCases.__eo_to_smt.case_145 x_a0, EoCases.__eo_to_smt.case_146 x_a0, EoCases.__eo_to_smt.case_147 x_a0, EoCases.__eo_to_smt.case_148 x_a0, EoCases.__eo_to_smt.case_149 x_a0, EoCases.__eo_to_smt.case_150 x_a0, EoCases.__eo_to_smt.case_151 x_a0, EoCases.__eo_to_smt.case_152 x_a0, EoCases.__eo_to_smt.case_153 x_a0, EoCases.__eo_to_smt.case_154 x_a0, EoCases.__eo_to_smt.case_155 x_a0] ++ [EoCases.__eo_to_smt.case_156 x_a0, EoCases.__eo_to_smt.case_157 x_a0, EoCases.__eo_to_smt.case_158 x_a0, EoCases.__eo_to_smt.case_159 x_a0] ++ [] from rfl)
    otherwise ⟨hl_156, hl_157, hl_158, hl_159⟩ using hl_144 hl_145 hl_146 hl_147 hl_148 hl_149 hl_150 hl_151 hl_152 hl_153 hl_154 hl_155
  group_none hinv4 hG with ⟨hl_144, hl_145, hl_146, hl_147, hl_148, hl_149, hl_150, hl_151, hl_152, hl_153, hl_154, hl_155, hl_156, hl_157, hl_158, hl_159⟩

theorem cases_1_10_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_1_10_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_to_smt.case_160 x_a0, EoCases.__eo_to_smt.case_161 x_a0, EoCases.__eo_to_smt.case_162 x_a0, EoCases.__eo_to_smt.case_163 x_a0, EoCases.__eo_to_smt.case_164 x_a0, EoCases.__eo_to_smt.case_165 x_a0, EoCases.__eo_to_smt.case_166 x_a0, EoCases.__eo_to_smt.case_167 x_a0, EoCases.__eo_to_smt.case_168 x_a0, EoCases.__eo_to_smt.case_169 x_a0, EoCases.__eo_to_smt.case_170 x_a0, EoCases.__eo_to_smt.case_171 x_a0, EoCases.__eo_to_smt.case_172 x_a0, EoCases.__eo_to_smt.case_173 x_a0, EoCases.__eo_to_smt.case_174 x_a0, EoCases.__eo_to_smt.case_175 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_160 x_a0 = none ∧ EoCases.__eo_to_smt.case_161 x_a0 = none ∧ EoCases.__eo_to_smt.case_162 x_a0 = none ∧ EoCases.__eo_to_smt.case_163 x_a0 = none ∧ EoCases.__eo_to_smt.case_164 x_a0 = none ∧ EoCases.__eo_to_smt.case_165 x_a0 = none ∧ EoCases.__eo_to_smt.case_166 x_a0 = none ∧ EoCases.__eo_to_smt.case_167 x_a0 = none ∧ EoCases.__eo_to_smt.case_168 x_a0 = none ∧ EoCases.__eo_to_smt.case_169 x_a0 = none ∧ EoCases.__eo_to_smt.case_170 x_a0 = none ∧ EoCases.__eo_to_smt.case_171 x_a0 = none ∧ EoCases.__eo_to_smt.case_172 x_a0 = none ∧ EoCases.__eo_to_smt.case_173 x_a0 = none ∧ EoCases.__eo_to_smt.case_174 x_a0 = none ∧ EoCases.__eo_to_smt.case_175 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_1_10_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  group_step with cases_0_40_eo__24eo_5fto_5fsmt_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_160 x_a0, EoCases.__eo_to_smt.case_161 x_a0, EoCases.__eo_to_smt.case_162 x_a0, EoCases.__eo_to_smt.case_163 x_a0, EoCases.__eo_to_smt.case_164 x_a0, EoCases.__eo_to_smt.case_165 x_a0, EoCases.__eo_to_smt.case_166 x_a0, EoCases.__eo_to_smt.case_167 x_a0, EoCases.__eo_to_smt.case_168 x_a0, EoCases.__eo_to_smt.case_169 x_a0, EoCases.__eo_to_smt.case_170 x_a0, EoCases.__eo_to_smt.case_171 x_a0, EoCases.__eo_to_smt.case_172 x_a0, EoCases.__eo_to_smt.case_173 x_a0, EoCases.__eo_to_smt.case_174 x_a0, EoCases.__eo_to_smt.case_175 x_a0] = [] ++ [EoCases.__eo_to_smt.case_160 x_a0, EoCases.__eo_to_smt.case_161 x_a0, EoCases.__eo_to_smt.case_162 x_a0, EoCases.__eo_to_smt.case_163 x_a0] ++ [EoCases.__eo_to_smt.case_164 x_a0, EoCases.__eo_to_smt.case_165 x_a0, EoCases.__eo_to_smt.case_166 x_a0, EoCases.__eo_to_smt.case_167 x_a0, EoCases.__eo_to_smt.case_168 x_a0, EoCases.__eo_to_smt.case_169 x_a0, EoCases.__eo_to_smt.case_170 x_a0, EoCases.__eo_to_smt.case_171 x_a0, EoCases.__eo_to_smt.case_172 x_a0, EoCases.__eo_to_smt.case_173 x_a0, EoCases.__eo_to_smt.case_174 x_a0, EoCases.__eo_to_smt.case_175 x_a0] from rfl)
    otherwise ⟨hl_160, hl_161, hl_162, hl_163⟩ using
  group_step with cases_0_41_eo__24eo_5fto_5fsmt_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_160 x_a0, EoCases.__eo_to_smt.case_161 x_a0, EoCases.__eo_to_smt.case_162 x_a0, EoCases.__eo_to_smt.case_163 x_a0, EoCases.__eo_to_smt.case_164 x_a0, EoCases.__eo_to_smt.case_165 x_a0, EoCases.__eo_to_smt.case_166 x_a0, EoCases.__eo_to_smt.case_167 x_a0, EoCases.__eo_to_smt.case_168 x_a0, EoCases.__eo_to_smt.case_169 x_a0, EoCases.__eo_to_smt.case_170 x_a0, EoCases.__eo_to_smt.case_171 x_a0, EoCases.__eo_to_smt.case_172 x_a0, EoCases.__eo_to_smt.case_173 x_a0, EoCases.__eo_to_smt.case_174 x_a0, EoCases.__eo_to_smt.case_175 x_a0] = [EoCases.__eo_to_smt.case_160 x_a0, EoCases.__eo_to_smt.case_161 x_a0, EoCases.__eo_to_smt.case_162 x_a0, EoCases.__eo_to_smt.case_163 x_a0] ++ [EoCases.__eo_to_smt.case_164 x_a0, EoCases.__eo_to_smt.case_165 x_a0, EoCases.__eo_to_smt.case_166 x_a0, EoCases.__eo_to_smt.case_167 x_a0] ++ [EoCases.__eo_to_smt.case_168 x_a0, EoCases.__eo_to_smt.case_169 x_a0, EoCases.__eo_to_smt.case_170 x_a0, EoCases.__eo_to_smt.case_171 x_a0, EoCases.__eo_to_smt.case_172 x_a0, EoCases.__eo_to_smt.case_173 x_a0, EoCases.__eo_to_smt.case_174 x_a0, EoCases.__eo_to_smt.case_175 x_a0] from rfl)
    otherwise ⟨hl_164, hl_165, hl_166, hl_167⟩ using hl_160 hl_161 hl_162 hl_163
  group_step with cases_0_42_eo__24eo_5fto_5fsmt_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_160 x_a0, EoCases.__eo_to_smt.case_161 x_a0, EoCases.__eo_to_smt.case_162 x_a0, EoCases.__eo_to_smt.case_163 x_a0, EoCases.__eo_to_smt.case_164 x_a0, EoCases.__eo_to_smt.case_165 x_a0, EoCases.__eo_to_smt.case_166 x_a0, EoCases.__eo_to_smt.case_167 x_a0, EoCases.__eo_to_smt.case_168 x_a0, EoCases.__eo_to_smt.case_169 x_a0, EoCases.__eo_to_smt.case_170 x_a0, EoCases.__eo_to_smt.case_171 x_a0, EoCases.__eo_to_smt.case_172 x_a0, EoCases.__eo_to_smt.case_173 x_a0, EoCases.__eo_to_smt.case_174 x_a0, EoCases.__eo_to_smt.case_175 x_a0] = [EoCases.__eo_to_smt.case_160 x_a0, EoCases.__eo_to_smt.case_161 x_a0, EoCases.__eo_to_smt.case_162 x_a0, EoCases.__eo_to_smt.case_163 x_a0, EoCases.__eo_to_smt.case_164 x_a0, EoCases.__eo_to_smt.case_165 x_a0, EoCases.__eo_to_smt.case_166 x_a0, EoCases.__eo_to_smt.case_167 x_a0] ++ [EoCases.__eo_to_smt.case_168 x_a0, EoCases.__eo_to_smt.case_169 x_a0, EoCases.__eo_to_smt.case_170 x_a0, EoCases.__eo_to_smt.case_171 x_a0] ++ [EoCases.__eo_to_smt.case_172 x_a0, EoCases.__eo_to_smt.case_173 x_a0, EoCases.__eo_to_smt.case_174 x_a0, EoCases.__eo_to_smt.case_175 x_a0] from rfl)
    otherwise ⟨hl_168, hl_169, hl_170, hl_171⟩ using hl_160 hl_161 hl_162 hl_163 hl_164 hl_165 hl_166 hl_167
  group_step with cases_0_43_eo__24eo_5fto_5fsmt_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_160 x_a0, EoCases.__eo_to_smt.case_161 x_a0, EoCases.__eo_to_smt.case_162 x_a0, EoCases.__eo_to_smt.case_163 x_a0, EoCases.__eo_to_smt.case_164 x_a0, EoCases.__eo_to_smt.case_165 x_a0, EoCases.__eo_to_smt.case_166 x_a0, EoCases.__eo_to_smt.case_167 x_a0, EoCases.__eo_to_smt.case_168 x_a0, EoCases.__eo_to_smt.case_169 x_a0, EoCases.__eo_to_smt.case_170 x_a0, EoCases.__eo_to_smt.case_171 x_a0, EoCases.__eo_to_smt.case_172 x_a0, EoCases.__eo_to_smt.case_173 x_a0, EoCases.__eo_to_smt.case_174 x_a0, EoCases.__eo_to_smt.case_175 x_a0] = [EoCases.__eo_to_smt.case_160 x_a0, EoCases.__eo_to_smt.case_161 x_a0, EoCases.__eo_to_smt.case_162 x_a0, EoCases.__eo_to_smt.case_163 x_a0, EoCases.__eo_to_smt.case_164 x_a0, EoCases.__eo_to_smt.case_165 x_a0, EoCases.__eo_to_smt.case_166 x_a0, EoCases.__eo_to_smt.case_167 x_a0, EoCases.__eo_to_smt.case_168 x_a0, EoCases.__eo_to_smt.case_169 x_a0, EoCases.__eo_to_smt.case_170 x_a0, EoCases.__eo_to_smt.case_171 x_a0] ++ [EoCases.__eo_to_smt.case_172 x_a0, EoCases.__eo_to_smt.case_173 x_a0, EoCases.__eo_to_smt.case_174 x_a0, EoCases.__eo_to_smt.case_175 x_a0] ++ [] from rfl)
    otherwise ⟨hl_172, hl_173, hl_174, hl_175⟩ using hl_160 hl_161 hl_162 hl_163 hl_164 hl_165 hl_166 hl_167 hl_168 hl_169 hl_170 hl_171
  group_none hinv4 hG with ⟨hl_160, hl_161, hl_162, hl_163, hl_164, hl_165, hl_166, hl_167, hl_168, hl_169, hl_170, hl_171, hl_172, hl_173, hl_174, hl_175⟩

theorem cases_1_11_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_1_11_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_to_smt.case_176 x_a0, EoCases.__eo_to_smt.case_177 x_a0, EoCases.__eo_to_smt.case_178 x_a0, EoCases.__eo_to_smt.case_179 x_a0, EoCases.__eo_to_smt.case_180 x_a0, EoCases.__eo_to_smt.case_181 x_a0, EoCases.__eo_to_smt.case_182 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_176 x_a0 = none ∧ EoCases.__eo_to_smt.case_177 x_a0 = none ∧ EoCases.__eo_to_smt.case_178 x_a0 = none ∧ EoCases.__eo_to_smt.case_179 x_a0 = none ∧ EoCases.__eo_to_smt.case_180 x_a0 = none ∧ EoCases.__eo_to_smt.case_181 x_a0 = none ∧ EoCases.__eo_to_smt.case_182 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_1_11_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  group_step with cases_0_44_eo__24eo_5fto_5fsmt_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_176 x_a0, EoCases.__eo_to_smt.case_177 x_a0, EoCases.__eo_to_smt.case_178 x_a0, EoCases.__eo_to_smt.case_179 x_a0, EoCases.__eo_to_smt.case_180 x_a0, EoCases.__eo_to_smt.case_181 x_a0, EoCases.__eo_to_smt.case_182 x_a0] = [] ++ [EoCases.__eo_to_smt.case_176 x_a0, EoCases.__eo_to_smt.case_177 x_a0, EoCases.__eo_to_smt.case_178 x_a0, EoCases.__eo_to_smt.case_179 x_a0] ++ [EoCases.__eo_to_smt.case_180 x_a0, EoCases.__eo_to_smt.case_181 x_a0, EoCases.__eo_to_smt.case_182 x_a0] from rfl)
    otherwise ⟨hl_176, hl_177, hl_178, hl_179⟩ using
  group_step with cases_0_45_eo__24eo_5fto_5fsmt_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_176 x_a0, EoCases.__eo_to_smt.case_177 x_a0, EoCases.__eo_to_smt.case_178 x_a0, EoCases.__eo_to_smt.case_179 x_a0, EoCases.__eo_to_smt.case_180 x_a0, EoCases.__eo_to_smt.case_181 x_a0, EoCases.__eo_to_smt.case_182 x_a0] = [EoCases.__eo_to_smt.case_176 x_a0, EoCases.__eo_to_smt.case_177 x_a0, EoCases.__eo_to_smt.case_178 x_a0, EoCases.__eo_to_smt.case_179 x_a0] ++ [EoCases.__eo_to_smt.case_180 x_a0, EoCases.__eo_to_smt.case_181 x_a0, EoCases.__eo_to_smt.case_182 x_a0] ++ [] from rfl)
    otherwise ⟨hl_180, hl_181, hl_182⟩ using hl_176 hl_177 hl_178 hl_179
  group_none hinv2 hG with ⟨hl_176, hl_177, hl_178, hl_179, hl_180, hl_181, hl_182⟩

theorem cases_2_0_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_2_0_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_to_smt.case_0 x_a0, EoCases.__eo_to_smt.case_1 x_a0, EoCases.__eo_to_smt.case_2 x_a0, EoCases.__eo_to_smt.case_3 x_a0, EoCases.__eo_to_smt.case_4 x_a0, EoCases.__eo_to_smt.case_5 x_a0, EoCases.__eo_to_smt.case_6 x_a0, EoCases.__eo_to_smt.case_7 x_a0, EoCases.__eo_to_smt.case_8 x_a0, EoCases.__eo_to_smt.case_9 x_a0, EoCases.__eo_to_smt.case_10 x_a0, EoCases.__eo_to_smt.case_11 x_a0, EoCases.__eo_to_smt.case_12 x_a0, EoCases.__eo_to_smt.case_13 x_a0, EoCases.__eo_to_smt.case_14 x_a0, EoCases.__eo_to_smt.case_15 x_a0, EoCases.__eo_to_smt.case_16 x_a0, EoCases.__eo_to_smt.case_17 x_a0, EoCases.__eo_to_smt.case_18 x_a0, EoCases.__eo_to_smt.case_19 x_a0, EoCases.__eo_to_smt.case_20 x_a0, EoCases.__eo_to_smt.case_21 x_a0, EoCases.__eo_to_smt.case_22 x_a0, EoCases.__eo_to_smt.case_23 x_a0, EoCases.__eo_to_smt.case_24 x_a0, EoCases.__eo_to_smt.case_25 x_a0, EoCases.__eo_to_smt.case_26 x_a0, EoCases.__eo_to_smt.case_27 x_a0, EoCases.__eo_to_smt.case_28 x_a0, EoCases.__eo_to_smt.case_29 x_a0, EoCases.__eo_to_smt.case_30 x_a0, EoCases.__eo_to_smt.case_31 x_a0, EoCases.__eo_to_smt.case_32 x_a0, EoCases.__eo_to_smt.case_33 x_a0, EoCases.__eo_to_smt.case_34 x_a0, EoCases.__eo_to_smt.case_35 x_a0, EoCases.__eo_to_smt.case_36 x_a0, EoCases.__eo_to_smt.case_37 x_a0, EoCases.__eo_to_smt.case_38 x_a0, EoCases.__eo_to_smt.case_39 x_a0, EoCases.__eo_to_smt.case_40 x_a0, EoCases.__eo_to_smt.case_41 x_a0, EoCases.__eo_to_smt.case_42 x_a0, EoCases.__eo_to_smt.case_43 x_a0, EoCases.__eo_to_smt.case_44 x_a0, EoCases.__eo_to_smt.case_45 x_a0, EoCases.__eo_to_smt.case_46 x_a0, EoCases.__eo_to_smt.case_47 x_a0, EoCases.__eo_to_smt.case_48 x_a0, EoCases.__eo_to_smt.case_49 x_a0, EoCases.__eo_to_smt.case_50 x_a0, EoCases.__eo_to_smt.case_51 x_a0, EoCases.__eo_to_smt.case_52 x_a0, EoCases.__eo_to_smt.case_53 x_a0, EoCases.__eo_to_smt.case_54 x_a0, EoCases.__eo_to_smt.case_55 x_a0, EoCases.__eo_to_smt.case_56 x_a0, EoCases.__eo_to_smt.case_57 x_a0, EoCases.__eo_to_smt.case_58 x_a0, EoCases.__eo_to_smt.case_59 x_a0, EoCases.__eo_to_smt.case_60 x_a0, EoCases.__eo_to_smt.case_61 x_a0, EoCases.__eo_to_smt.case_62 x_a0, EoCases.__eo_to_smt.case_63 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_0 x_a0 = none ∧ EoCases.__eo_to_smt.case_1 x_a0 = none ∧ EoCases.__eo_to_smt.case_2 x_a0 = none ∧ EoCases.__eo_to_smt.case_3 x_a0 = none ∧ EoCases.__eo_to_smt.case_4 x_a0 = none ∧ EoCases.__eo_to_smt.case_5 x_a0 = none ∧ EoCases.__eo_to_smt.case_6 x_a0 = none ∧ EoCases.__eo_to_smt.case_7 x_a0 = none ∧ EoCases.__eo_to_smt.case_8 x_a0 = none ∧ EoCases.__eo_to_smt.case_9 x_a0 = none ∧ EoCases.__eo_to_smt.case_10 x_a0 = none ∧ EoCases.__eo_to_smt.case_11 x_a0 = none ∧ EoCases.__eo_to_smt.case_12 x_a0 = none ∧ EoCases.__eo_to_smt.case_13 x_a0 = none ∧ EoCases.__eo_to_smt.case_14 x_a0 = none ∧ EoCases.__eo_to_smt.case_15 x_a0 = none ∧ EoCases.__eo_to_smt.case_16 x_a0 = none ∧ EoCases.__eo_to_smt.case_17 x_a0 = none ∧ EoCases.__eo_to_smt.case_18 x_a0 = none ∧ EoCases.__eo_to_smt.case_19 x_a0 = none ∧ EoCases.__eo_to_smt.case_20 x_a0 = none ∧ EoCases.__eo_to_smt.case_21 x_a0 = none ∧ EoCases.__eo_to_smt.case_22 x_a0 = none ∧ EoCases.__eo_to_smt.case_23 x_a0 = none ∧ EoCases.__eo_to_smt.case_24 x_a0 = none ∧ EoCases.__eo_to_smt.case_25 x_a0 = none ∧ EoCases.__eo_to_smt.case_26 x_a0 = none ∧ EoCases.__eo_to_smt.case_27 x_a0 = none ∧ EoCases.__eo_to_smt.case_28 x_a0 = none ∧ EoCases.__eo_to_smt.case_29 x_a0 = none ∧ EoCases.__eo_to_smt.case_30 x_a0 = none ∧ EoCases.__eo_to_smt.case_31 x_a0 = none ∧ EoCases.__eo_to_smt.case_32 x_a0 = none ∧ EoCases.__eo_to_smt.case_33 x_a0 = none ∧ EoCases.__eo_to_smt.case_34 x_a0 = none ∧ EoCases.__eo_to_smt.case_35 x_a0 = none ∧ EoCases.__eo_to_smt.case_36 x_a0 = none ∧ EoCases.__eo_to_smt.case_37 x_a0 = none ∧ EoCases.__eo_to_smt.case_38 x_a0 = none ∧ EoCases.__eo_to_smt.case_39 x_a0 = none ∧ EoCases.__eo_to_smt.case_40 x_a0 = none ∧ EoCases.__eo_to_smt.case_41 x_a0 = none ∧ EoCases.__eo_to_smt.case_42 x_a0 = none ∧ EoCases.__eo_to_smt.case_43 x_a0 = none ∧ EoCases.__eo_to_smt.case_44 x_a0 = none ∧ EoCases.__eo_to_smt.case_45 x_a0 = none ∧ EoCases.__eo_to_smt.case_46 x_a0 = none ∧ EoCases.__eo_to_smt.case_47 x_a0 = none ∧ EoCases.__eo_to_smt.case_48 x_a0 = none ∧ EoCases.__eo_to_smt.case_49 x_a0 = none ∧ EoCases.__eo_to_smt.case_50 x_a0 = none ∧ EoCases.__eo_to_smt.case_51 x_a0 = none ∧ EoCases.__eo_to_smt.case_52 x_a0 = none ∧ EoCases.__eo_to_smt.case_53 x_a0 = none ∧ EoCases.__eo_to_smt.case_54 x_a0 = none ∧ EoCases.__eo_to_smt.case_55 x_a0 = none ∧ EoCases.__eo_to_smt.case_56 x_a0 = none ∧ EoCases.__eo_to_smt.case_57 x_a0 = none ∧ EoCases.__eo_to_smt.case_58 x_a0 = none ∧ EoCases.__eo_to_smt.case_59 x_a0 = none ∧ EoCases.__eo_to_smt.case_60 x_a0 = none ∧ EoCases.__eo_to_smt.case_61 x_a0 = none ∧ EoCases.__eo_to_smt.case_62 x_a0 = none ∧ EoCases.__eo_to_smt.case_63 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_2_0_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  group_step with cases_1_0_eo__24eo_5fto_5fsmt_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_0 x_a0, EoCases.__eo_to_smt.case_1 x_a0, EoCases.__eo_to_smt.case_2 x_a0, EoCases.__eo_to_smt.case_3 x_a0, EoCases.__eo_to_smt.case_4 x_a0, EoCases.__eo_to_smt.case_5 x_a0, EoCases.__eo_to_smt.case_6 x_a0, EoCases.__eo_to_smt.case_7 x_a0, EoCases.__eo_to_smt.case_8 x_a0, EoCases.__eo_to_smt.case_9 x_a0, EoCases.__eo_to_smt.case_10 x_a0, EoCases.__eo_to_smt.case_11 x_a0, EoCases.__eo_to_smt.case_12 x_a0, EoCases.__eo_to_smt.case_13 x_a0, EoCases.__eo_to_smt.case_14 x_a0, EoCases.__eo_to_smt.case_15 x_a0, EoCases.__eo_to_smt.case_16 x_a0, EoCases.__eo_to_smt.case_17 x_a0, EoCases.__eo_to_smt.case_18 x_a0, EoCases.__eo_to_smt.case_19 x_a0, EoCases.__eo_to_smt.case_20 x_a0, EoCases.__eo_to_smt.case_21 x_a0, EoCases.__eo_to_smt.case_22 x_a0, EoCases.__eo_to_smt.case_23 x_a0, EoCases.__eo_to_smt.case_24 x_a0, EoCases.__eo_to_smt.case_25 x_a0, EoCases.__eo_to_smt.case_26 x_a0, EoCases.__eo_to_smt.case_27 x_a0, EoCases.__eo_to_smt.case_28 x_a0, EoCases.__eo_to_smt.case_29 x_a0, EoCases.__eo_to_smt.case_30 x_a0, EoCases.__eo_to_smt.case_31 x_a0, EoCases.__eo_to_smt.case_32 x_a0, EoCases.__eo_to_smt.case_33 x_a0, EoCases.__eo_to_smt.case_34 x_a0, EoCases.__eo_to_smt.case_35 x_a0, EoCases.__eo_to_smt.case_36 x_a0, EoCases.__eo_to_smt.case_37 x_a0, EoCases.__eo_to_smt.case_38 x_a0, EoCases.__eo_to_smt.case_39 x_a0, EoCases.__eo_to_smt.case_40 x_a0, EoCases.__eo_to_smt.case_41 x_a0, EoCases.__eo_to_smt.case_42 x_a0, EoCases.__eo_to_smt.case_43 x_a0, EoCases.__eo_to_smt.case_44 x_a0, EoCases.__eo_to_smt.case_45 x_a0, EoCases.__eo_to_smt.case_46 x_a0, EoCases.__eo_to_smt.case_47 x_a0, EoCases.__eo_to_smt.case_48 x_a0, EoCases.__eo_to_smt.case_49 x_a0, EoCases.__eo_to_smt.case_50 x_a0, EoCases.__eo_to_smt.case_51 x_a0, EoCases.__eo_to_smt.case_52 x_a0, EoCases.__eo_to_smt.case_53 x_a0, EoCases.__eo_to_smt.case_54 x_a0, EoCases.__eo_to_smt.case_55 x_a0, EoCases.__eo_to_smt.case_56 x_a0, EoCases.__eo_to_smt.case_57 x_a0, EoCases.__eo_to_smt.case_58 x_a0, EoCases.__eo_to_smt.case_59 x_a0, EoCases.__eo_to_smt.case_60 x_a0, EoCases.__eo_to_smt.case_61 x_a0, EoCases.__eo_to_smt.case_62 x_a0, EoCases.__eo_to_smt.case_63 x_a0] = [] ++ [EoCases.__eo_to_smt.case_0 x_a0, EoCases.__eo_to_smt.case_1 x_a0, EoCases.__eo_to_smt.case_2 x_a0, EoCases.__eo_to_smt.case_3 x_a0, EoCases.__eo_to_smt.case_4 x_a0, EoCases.__eo_to_smt.case_5 x_a0, EoCases.__eo_to_smt.case_6 x_a0, EoCases.__eo_to_smt.case_7 x_a0, EoCases.__eo_to_smt.case_8 x_a0, EoCases.__eo_to_smt.case_9 x_a0, EoCases.__eo_to_smt.case_10 x_a0, EoCases.__eo_to_smt.case_11 x_a0, EoCases.__eo_to_smt.case_12 x_a0, EoCases.__eo_to_smt.case_13 x_a0, EoCases.__eo_to_smt.case_14 x_a0, EoCases.__eo_to_smt.case_15 x_a0] ++ [EoCases.__eo_to_smt.case_16 x_a0, EoCases.__eo_to_smt.case_17 x_a0, EoCases.__eo_to_smt.case_18 x_a0, EoCases.__eo_to_smt.case_19 x_a0, EoCases.__eo_to_smt.case_20 x_a0, EoCases.__eo_to_smt.case_21 x_a0, EoCases.__eo_to_smt.case_22 x_a0, EoCases.__eo_to_smt.case_23 x_a0, EoCases.__eo_to_smt.case_24 x_a0, EoCases.__eo_to_smt.case_25 x_a0, EoCases.__eo_to_smt.case_26 x_a0, EoCases.__eo_to_smt.case_27 x_a0, EoCases.__eo_to_smt.case_28 x_a0, EoCases.__eo_to_smt.case_29 x_a0, EoCases.__eo_to_smt.case_30 x_a0, EoCases.__eo_to_smt.case_31 x_a0, EoCases.__eo_to_smt.case_32 x_a0, EoCases.__eo_to_smt.case_33 x_a0, EoCases.__eo_to_smt.case_34 x_a0, EoCases.__eo_to_smt.case_35 x_a0, EoCases.__eo_to_smt.case_36 x_a0, EoCases.__eo_to_smt.case_37 x_a0, EoCases.__eo_to_smt.case_38 x_a0, EoCases.__eo_to_smt.case_39 x_a0, EoCases.__eo_to_smt.case_40 x_a0, EoCases.__eo_to_smt.case_41 x_a0, EoCases.__eo_to_smt.case_42 x_a0, EoCases.__eo_to_smt.case_43 x_a0, EoCases.__eo_to_smt.case_44 x_a0, EoCases.__eo_to_smt.case_45 x_a0, EoCases.__eo_to_smt.case_46 x_a0, EoCases.__eo_to_smt.case_47 x_a0, EoCases.__eo_to_smt.case_48 x_a0, EoCases.__eo_to_smt.case_49 x_a0, EoCases.__eo_to_smt.case_50 x_a0, EoCases.__eo_to_smt.case_51 x_a0, EoCases.__eo_to_smt.case_52 x_a0, EoCases.__eo_to_smt.case_53 x_a0, EoCases.__eo_to_smt.case_54 x_a0, EoCases.__eo_to_smt.case_55 x_a0, EoCases.__eo_to_smt.case_56 x_a0, EoCases.__eo_to_smt.case_57 x_a0, EoCases.__eo_to_smt.case_58 x_a0, EoCases.__eo_to_smt.case_59 x_a0, EoCases.__eo_to_smt.case_60 x_a0, EoCases.__eo_to_smt.case_61 x_a0, EoCases.__eo_to_smt.case_62 x_a0, EoCases.__eo_to_smt.case_63 x_a0] from rfl)
    otherwise ⟨hl_0, hl_1, hl_2, hl_3, hl_4, hl_5, hl_6, hl_7, hl_8, hl_9, hl_10, hl_11, hl_12, hl_13, hl_14, hl_15⟩ using
  group_step with cases_1_1_eo__24eo_5fto_5fsmt_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_0 x_a0, EoCases.__eo_to_smt.case_1 x_a0, EoCases.__eo_to_smt.case_2 x_a0, EoCases.__eo_to_smt.case_3 x_a0, EoCases.__eo_to_smt.case_4 x_a0, EoCases.__eo_to_smt.case_5 x_a0, EoCases.__eo_to_smt.case_6 x_a0, EoCases.__eo_to_smt.case_7 x_a0, EoCases.__eo_to_smt.case_8 x_a0, EoCases.__eo_to_smt.case_9 x_a0, EoCases.__eo_to_smt.case_10 x_a0, EoCases.__eo_to_smt.case_11 x_a0, EoCases.__eo_to_smt.case_12 x_a0, EoCases.__eo_to_smt.case_13 x_a0, EoCases.__eo_to_smt.case_14 x_a0, EoCases.__eo_to_smt.case_15 x_a0, EoCases.__eo_to_smt.case_16 x_a0, EoCases.__eo_to_smt.case_17 x_a0, EoCases.__eo_to_smt.case_18 x_a0, EoCases.__eo_to_smt.case_19 x_a0, EoCases.__eo_to_smt.case_20 x_a0, EoCases.__eo_to_smt.case_21 x_a0, EoCases.__eo_to_smt.case_22 x_a0, EoCases.__eo_to_smt.case_23 x_a0, EoCases.__eo_to_smt.case_24 x_a0, EoCases.__eo_to_smt.case_25 x_a0, EoCases.__eo_to_smt.case_26 x_a0, EoCases.__eo_to_smt.case_27 x_a0, EoCases.__eo_to_smt.case_28 x_a0, EoCases.__eo_to_smt.case_29 x_a0, EoCases.__eo_to_smt.case_30 x_a0, EoCases.__eo_to_smt.case_31 x_a0, EoCases.__eo_to_smt.case_32 x_a0, EoCases.__eo_to_smt.case_33 x_a0, EoCases.__eo_to_smt.case_34 x_a0, EoCases.__eo_to_smt.case_35 x_a0, EoCases.__eo_to_smt.case_36 x_a0, EoCases.__eo_to_smt.case_37 x_a0, EoCases.__eo_to_smt.case_38 x_a0, EoCases.__eo_to_smt.case_39 x_a0, EoCases.__eo_to_smt.case_40 x_a0, EoCases.__eo_to_smt.case_41 x_a0, EoCases.__eo_to_smt.case_42 x_a0, EoCases.__eo_to_smt.case_43 x_a0, EoCases.__eo_to_smt.case_44 x_a0, EoCases.__eo_to_smt.case_45 x_a0, EoCases.__eo_to_smt.case_46 x_a0, EoCases.__eo_to_smt.case_47 x_a0, EoCases.__eo_to_smt.case_48 x_a0, EoCases.__eo_to_smt.case_49 x_a0, EoCases.__eo_to_smt.case_50 x_a0, EoCases.__eo_to_smt.case_51 x_a0, EoCases.__eo_to_smt.case_52 x_a0, EoCases.__eo_to_smt.case_53 x_a0, EoCases.__eo_to_smt.case_54 x_a0, EoCases.__eo_to_smt.case_55 x_a0, EoCases.__eo_to_smt.case_56 x_a0, EoCases.__eo_to_smt.case_57 x_a0, EoCases.__eo_to_smt.case_58 x_a0, EoCases.__eo_to_smt.case_59 x_a0, EoCases.__eo_to_smt.case_60 x_a0, EoCases.__eo_to_smt.case_61 x_a0, EoCases.__eo_to_smt.case_62 x_a0, EoCases.__eo_to_smt.case_63 x_a0] = [EoCases.__eo_to_smt.case_0 x_a0, EoCases.__eo_to_smt.case_1 x_a0, EoCases.__eo_to_smt.case_2 x_a0, EoCases.__eo_to_smt.case_3 x_a0, EoCases.__eo_to_smt.case_4 x_a0, EoCases.__eo_to_smt.case_5 x_a0, EoCases.__eo_to_smt.case_6 x_a0, EoCases.__eo_to_smt.case_7 x_a0, EoCases.__eo_to_smt.case_8 x_a0, EoCases.__eo_to_smt.case_9 x_a0, EoCases.__eo_to_smt.case_10 x_a0, EoCases.__eo_to_smt.case_11 x_a0, EoCases.__eo_to_smt.case_12 x_a0, EoCases.__eo_to_smt.case_13 x_a0, EoCases.__eo_to_smt.case_14 x_a0, EoCases.__eo_to_smt.case_15 x_a0] ++ [EoCases.__eo_to_smt.case_16 x_a0, EoCases.__eo_to_smt.case_17 x_a0, EoCases.__eo_to_smt.case_18 x_a0, EoCases.__eo_to_smt.case_19 x_a0, EoCases.__eo_to_smt.case_20 x_a0, EoCases.__eo_to_smt.case_21 x_a0, EoCases.__eo_to_smt.case_22 x_a0, EoCases.__eo_to_smt.case_23 x_a0, EoCases.__eo_to_smt.case_24 x_a0, EoCases.__eo_to_smt.case_25 x_a0, EoCases.__eo_to_smt.case_26 x_a0, EoCases.__eo_to_smt.case_27 x_a0, EoCases.__eo_to_smt.case_28 x_a0, EoCases.__eo_to_smt.case_29 x_a0, EoCases.__eo_to_smt.case_30 x_a0, EoCases.__eo_to_smt.case_31 x_a0] ++ [EoCases.__eo_to_smt.case_32 x_a0, EoCases.__eo_to_smt.case_33 x_a0, EoCases.__eo_to_smt.case_34 x_a0, EoCases.__eo_to_smt.case_35 x_a0, EoCases.__eo_to_smt.case_36 x_a0, EoCases.__eo_to_smt.case_37 x_a0, EoCases.__eo_to_smt.case_38 x_a0, EoCases.__eo_to_smt.case_39 x_a0, EoCases.__eo_to_smt.case_40 x_a0, EoCases.__eo_to_smt.case_41 x_a0, EoCases.__eo_to_smt.case_42 x_a0, EoCases.__eo_to_smt.case_43 x_a0, EoCases.__eo_to_smt.case_44 x_a0, EoCases.__eo_to_smt.case_45 x_a0, EoCases.__eo_to_smt.case_46 x_a0, EoCases.__eo_to_smt.case_47 x_a0, EoCases.__eo_to_smt.case_48 x_a0, EoCases.__eo_to_smt.case_49 x_a0, EoCases.__eo_to_smt.case_50 x_a0, EoCases.__eo_to_smt.case_51 x_a0, EoCases.__eo_to_smt.case_52 x_a0, EoCases.__eo_to_smt.case_53 x_a0, EoCases.__eo_to_smt.case_54 x_a0, EoCases.__eo_to_smt.case_55 x_a0, EoCases.__eo_to_smt.case_56 x_a0, EoCases.__eo_to_smt.case_57 x_a0, EoCases.__eo_to_smt.case_58 x_a0, EoCases.__eo_to_smt.case_59 x_a0, EoCases.__eo_to_smt.case_60 x_a0, EoCases.__eo_to_smt.case_61 x_a0, EoCases.__eo_to_smt.case_62 x_a0, EoCases.__eo_to_smt.case_63 x_a0] from rfl)
    otherwise ⟨hl_16, hl_17, hl_18, hl_19, hl_20, hl_21, hl_22, hl_23, hl_24, hl_25, hl_26, hl_27, hl_28, hl_29, hl_30, hl_31⟩ using hl_0 hl_1 hl_2 hl_3 hl_4 hl_5 hl_6 hl_7 hl_8 hl_9 hl_10 hl_11 hl_12 hl_13 hl_14 hl_15
  group_step with cases_1_2_eo__24eo_5fto_5fsmt_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_0 x_a0, EoCases.__eo_to_smt.case_1 x_a0, EoCases.__eo_to_smt.case_2 x_a0, EoCases.__eo_to_smt.case_3 x_a0, EoCases.__eo_to_smt.case_4 x_a0, EoCases.__eo_to_smt.case_5 x_a0, EoCases.__eo_to_smt.case_6 x_a0, EoCases.__eo_to_smt.case_7 x_a0, EoCases.__eo_to_smt.case_8 x_a0, EoCases.__eo_to_smt.case_9 x_a0, EoCases.__eo_to_smt.case_10 x_a0, EoCases.__eo_to_smt.case_11 x_a0, EoCases.__eo_to_smt.case_12 x_a0, EoCases.__eo_to_smt.case_13 x_a0, EoCases.__eo_to_smt.case_14 x_a0, EoCases.__eo_to_smt.case_15 x_a0, EoCases.__eo_to_smt.case_16 x_a0, EoCases.__eo_to_smt.case_17 x_a0, EoCases.__eo_to_smt.case_18 x_a0, EoCases.__eo_to_smt.case_19 x_a0, EoCases.__eo_to_smt.case_20 x_a0, EoCases.__eo_to_smt.case_21 x_a0, EoCases.__eo_to_smt.case_22 x_a0, EoCases.__eo_to_smt.case_23 x_a0, EoCases.__eo_to_smt.case_24 x_a0, EoCases.__eo_to_smt.case_25 x_a0, EoCases.__eo_to_smt.case_26 x_a0, EoCases.__eo_to_smt.case_27 x_a0, EoCases.__eo_to_smt.case_28 x_a0, EoCases.__eo_to_smt.case_29 x_a0, EoCases.__eo_to_smt.case_30 x_a0, EoCases.__eo_to_smt.case_31 x_a0, EoCases.__eo_to_smt.case_32 x_a0, EoCases.__eo_to_smt.case_33 x_a0, EoCases.__eo_to_smt.case_34 x_a0, EoCases.__eo_to_smt.case_35 x_a0, EoCases.__eo_to_smt.case_36 x_a0, EoCases.__eo_to_smt.case_37 x_a0, EoCases.__eo_to_smt.case_38 x_a0, EoCases.__eo_to_smt.case_39 x_a0, EoCases.__eo_to_smt.case_40 x_a0, EoCases.__eo_to_smt.case_41 x_a0, EoCases.__eo_to_smt.case_42 x_a0, EoCases.__eo_to_smt.case_43 x_a0, EoCases.__eo_to_smt.case_44 x_a0, EoCases.__eo_to_smt.case_45 x_a0, EoCases.__eo_to_smt.case_46 x_a0, EoCases.__eo_to_smt.case_47 x_a0, EoCases.__eo_to_smt.case_48 x_a0, EoCases.__eo_to_smt.case_49 x_a0, EoCases.__eo_to_smt.case_50 x_a0, EoCases.__eo_to_smt.case_51 x_a0, EoCases.__eo_to_smt.case_52 x_a0, EoCases.__eo_to_smt.case_53 x_a0, EoCases.__eo_to_smt.case_54 x_a0, EoCases.__eo_to_smt.case_55 x_a0, EoCases.__eo_to_smt.case_56 x_a0, EoCases.__eo_to_smt.case_57 x_a0, EoCases.__eo_to_smt.case_58 x_a0, EoCases.__eo_to_smt.case_59 x_a0, EoCases.__eo_to_smt.case_60 x_a0, EoCases.__eo_to_smt.case_61 x_a0, EoCases.__eo_to_smt.case_62 x_a0, EoCases.__eo_to_smt.case_63 x_a0] = [EoCases.__eo_to_smt.case_0 x_a0, EoCases.__eo_to_smt.case_1 x_a0, EoCases.__eo_to_smt.case_2 x_a0, EoCases.__eo_to_smt.case_3 x_a0, EoCases.__eo_to_smt.case_4 x_a0, EoCases.__eo_to_smt.case_5 x_a0, EoCases.__eo_to_smt.case_6 x_a0, EoCases.__eo_to_smt.case_7 x_a0, EoCases.__eo_to_smt.case_8 x_a0, EoCases.__eo_to_smt.case_9 x_a0, EoCases.__eo_to_smt.case_10 x_a0, EoCases.__eo_to_smt.case_11 x_a0, EoCases.__eo_to_smt.case_12 x_a0, EoCases.__eo_to_smt.case_13 x_a0, EoCases.__eo_to_smt.case_14 x_a0, EoCases.__eo_to_smt.case_15 x_a0, EoCases.__eo_to_smt.case_16 x_a0, EoCases.__eo_to_smt.case_17 x_a0, EoCases.__eo_to_smt.case_18 x_a0, EoCases.__eo_to_smt.case_19 x_a0, EoCases.__eo_to_smt.case_20 x_a0, EoCases.__eo_to_smt.case_21 x_a0, EoCases.__eo_to_smt.case_22 x_a0, EoCases.__eo_to_smt.case_23 x_a0, EoCases.__eo_to_smt.case_24 x_a0, EoCases.__eo_to_smt.case_25 x_a0, EoCases.__eo_to_smt.case_26 x_a0, EoCases.__eo_to_smt.case_27 x_a0, EoCases.__eo_to_smt.case_28 x_a0, EoCases.__eo_to_smt.case_29 x_a0, EoCases.__eo_to_smt.case_30 x_a0, EoCases.__eo_to_smt.case_31 x_a0] ++ [EoCases.__eo_to_smt.case_32 x_a0, EoCases.__eo_to_smt.case_33 x_a0, EoCases.__eo_to_smt.case_34 x_a0, EoCases.__eo_to_smt.case_35 x_a0, EoCases.__eo_to_smt.case_36 x_a0, EoCases.__eo_to_smt.case_37 x_a0, EoCases.__eo_to_smt.case_38 x_a0, EoCases.__eo_to_smt.case_39 x_a0, EoCases.__eo_to_smt.case_40 x_a0, EoCases.__eo_to_smt.case_41 x_a0, EoCases.__eo_to_smt.case_42 x_a0, EoCases.__eo_to_smt.case_43 x_a0, EoCases.__eo_to_smt.case_44 x_a0, EoCases.__eo_to_smt.case_45 x_a0, EoCases.__eo_to_smt.case_46 x_a0, EoCases.__eo_to_smt.case_47 x_a0] ++ [EoCases.__eo_to_smt.case_48 x_a0, EoCases.__eo_to_smt.case_49 x_a0, EoCases.__eo_to_smt.case_50 x_a0, EoCases.__eo_to_smt.case_51 x_a0, EoCases.__eo_to_smt.case_52 x_a0, EoCases.__eo_to_smt.case_53 x_a0, EoCases.__eo_to_smt.case_54 x_a0, EoCases.__eo_to_smt.case_55 x_a0, EoCases.__eo_to_smt.case_56 x_a0, EoCases.__eo_to_smt.case_57 x_a0, EoCases.__eo_to_smt.case_58 x_a0, EoCases.__eo_to_smt.case_59 x_a0, EoCases.__eo_to_smt.case_60 x_a0, EoCases.__eo_to_smt.case_61 x_a0, EoCases.__eo_to_smt.case_62 x_a0, EoCases.__eo_to_smt.case_63 x_a0] from rfl)
    otherwise ⟨hl_32, hl_33, hl_34, hl_35, hl_36, hl_37, hl_38, hl_39, hl_40, hl_41, hl_42, hl_43, hl_44, hl_45, hl_46, hl_47⟩ using hl_0 hl_1 hl_2 hl_3 hl_4 hl_5 hl_6 hl_7 hl_8 hl_9 hl_10 hl_11 hl_12 hl_13 hl_14 hl_15 hl_16 hl_17 hl_18 hl_19 hl_20 hl_21 hl_22 hl_23 hl_24 hl_25 hl_26 hl_27 hl_28 hl_29 hl_30 hl_31
  group_step with cases_1_3_eo__24eo_5fto_5fsmt_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_0 x_a0, EoCases.__eo_to_smt.case_1 x_a0, EoCases.__eo_to_smt.case_2 x_a0, EoCases.__eo_to_smt.case_3 x_a0, EoCases.__eo_to_smt.case_4 x_a0, EoCases.__eo_to_smt.case_5 x_a0, EoCases.__eo_to_smt.case_6 x_a0, EoCases.__eo_to_smt.case_7 x_a0, EoCases.__eo_to_smt.case_8 x_a0, EoCases.__eo_to_smt.case_9 x_a0, EoCases.__eo_to_smt.case_10 x_a0, EoCases.__eo_to_smt.case_11 x_a0, EoCases.__eo_to_smt.case_12 x_a0, EoCases.__eo_to_smt.case_13 x_a0, EoCases.__eo_to_smt.case_14 x_a0, EoCases.__eo_to_smt.case_15 x_a0, EoCases.__eo_to_smt.case_16 x_a0, EoCases.__eo_to_smt.case_17 x_a0, EoCases.__eo_to_smt.case_18 x_a0, EoCases.__eo_to_smt.case_19 x_a0, EoCases.__eo_to_smt.case_20 x_a0, EoCases.__eo_to_smt.case_21 x_a0, EoCases.__eo_to_smt.case_22 x_a0, EoCases.__eo_to_smt.case_23 x_a0, EoCases.__eo_to_smt.case_24 x_a0, EoCases.__eo_to_smt.case_25 x_a0, EoCases.__eo_to_smt.case_26 x_a0, EoCases.__eo_to_smt.case_27 x_a0, EoCases.__eo_to_smt.case_28 x_a0, EoCases.__eo_to_smt.case_29 x_a0, EoCases.__eo_to_smt.case_30 x_a0, EoCases.__eo_to_smt.case_31 x_a0, EoCases.__eo_to_smt.case_32 x_a0, EoCases.__eo_to_smt.case_33 x_a0, EoCases.__eo_to_smt.case_34 x_a0, EoCases.__eo_to_smt.case_35 x_a0, EoCases.__eo_to_smt.case_36 x_a0, EoCases.__eo_to_smt.case_37 x_a0, EoCases.__eo_to_smt.case_38 x_a0, EoCases.__eo_to_smt.case_39 x_a0, EoCases.__eo_to_smt.case_40 x_a0, EoCases.__eo_to_smt.case_41 x_a0, EoCases.__eo_to_smt.case_42 x_a0, EoCases.__eo_to_smt.case_43 x_a0, EoCases.__eo_to_smt.case_44 x_a0, EoCases.__eo_to_smt.case_45 x_a0, EoCases.__eo_to_smt.case_46 x_a0, EoCases.__eo_to_smt.case_47 x_a0, EoCases.__eo_to_smt.case_48 x_a0, EoCases.__eo_to_smt.case_49 x_a0, EoCases.__eo_to_smt.case_50 x_a0, EoCases.__eo_to_smt.case_51 x_a0, EoCases.__eo_to_smt.case_52 x_a0, EoCases.__eo_to_smt.case_53 x_a0, EoCases.__eo_to_smt.case_54 x_a0, EoCases.__eo_to_smt.case_55 x_a0, EoCases.__eo_to_smt.case_56 x_a0, EoCases.__eo_to_smt.case_57 x_a0, EoCases.__eo_to_smt.case_58 x_a0, EoCases.__eo_to_smt.case_59 x_a0, EoCases.__eo_to_smt.case_60 x_a0, EoCases.__eo_to_smt.case_61 x_a0, EoCases.__eo_to_smt.case_62 x_a0, EoCases.__eo_to_smt.case_63 x_a0] = [EoCases.__eo_to_smt.case_0 x_a0, EoCases.__eo_to_smt.case_1 x_a0, EoCases.__eo_to_smt.case_2 x_a0, EoCases.__eo_to_smt.case_3 x_a0, EoCases.__eo_to_smt.case_4 x_a0, EoCases.__eo_to_smt.case_5 x_a0, EoCases.__eo_to_smt.case_6 x_a0, EoCases.__eo_to_smt.case_7 x_a0, EoCases.__eo_to_smt.case_8 x_a0, EoCases.__eo_to_smt.case_9 x_a0, EoCases.__eo_to_smt.case_10 x_a0, EoCases.__eo_to_smt.case_11 x_a0, EoCases.__eo_to_smt.case_12 x_a0, EoCases.__eo_to_smt.case_13 x_a0, EoCases.__eo_to_smt.case_14 x_a0, EoCases.__eo_to_smt.case_15 x_a0, EoCases.__eo_to_smt.case_16 x_a0, EoCases.__eo_to_smt.case_17 x_a0, EoCases.__eo_to_smt.case_18 x_a0, EoCases.__eo_to_smt.case_19 x_a0, EoCases.__eo_to_smt.case_20 x_a0, EoCases.__eo_to_smt.case_21 x_a0, EoCases.__eo_to_smt.case_22 x_a0, EoCases.__eo_to_smt.case_23 x_a0, EoCases.__eo_to_smt.case_24 x_a0, EoCases.__eo_to_smt.case_25 x_a0, EoCases.__eo_to_smt.case_26 x_a0, EoCases.__eo_to_smt.case_27 x_a0, EoCases.__eo_to_smt.case_28 x_a0, EoCases.__eo_to_smt.case_29 x_a0, EoCases.__eo_to_smt.case_30 x_a0, EoCases.__eo_to_smt.case_31 x_a0, EoCases.__eo_to_smt.case_32 x_a0, EoCases.__eo_to_smt.case_33 x_a0, EoCases.__eo_to_smt.case_34 x_a0, EoCases.__eo_to_smt.case_35 x_a0, EoCases.__eo_to_smt.case_36 x_a0, EoCases.__eo_to_smt.case_37 x_a0, EoCases.__eo_to_smt.case_38 x_a0, EoCases.__eo_to_smt.case_39 x_a0, EoCases.__eo_to_smt.case_40 x_a0, EoCases.__eo_to_smt.case_41 x_a0, EoCases.__eo_to_smt.case_42 x_a0, EoCases.__eo_to_smt.case_43 x_a0, EoCases.__eo_to_smt.case_44 x_a0, EoCases.__eo_to_smt.case_45 x_a0, EoCases.__eo_to_smt.case_46 x_a0, EoCases.__eo_to_smt.case_47 x_a0] ++ [EoCases.__eo_to_smt.case_48 x_a0, EoCases.__eo_to_smt.case_49 x_a0, EoCases.__eo_to_smt.case_50 x_a0, EoCases.__eo_to_smt.case_51 x_a0, EoCases.__eo_to_smt.case_52 x_a0, EoCases.__eo_to_smt.case_53 x_a0, EoCases.__eo_to_smt.case_54 x_a0, EoCases.__eo_to_smt.case_55 x_a0, EoCases.__eo_to_smt.case_56 x_a0, EoCases.__eo_to_smt.case_57 x_a0, EoCases.__eo_to_smt.case_58 x_a0, EoCases.__eo_to_smt.case_59 x_a0, EoCases.__eo_to_smt.case_60 x_a0, EoCases.__eo_to_smt.case_61 x_a0, EoCases.__eo_to_smt.case_62 x_a0, EoCases.__eo_to_smt.case_63 x_a0] ++ [] from rfl)
    otherwise ⟨hl_48, hl_49, hl_50, hl_51, hl_52, hl_53, hl_54, hl_55, hl_56, hl_57, hl_58, hl_59, hl_60, hl_61, hl_62, hl_63⟩ using hl_0 hl_1 hl_2 hl_3 hl_4 hl_5 hl_6 hl_7 hl_8 hl_9 hl_10 hl_11 hl_12 hl_13 hl_14 hl_15 hl_16 hl_17 hl_18 hl_19 hl_20 hl_21 hl_22 hl_23 hl_24 hl_25 hl_26 hl_27 hl_28 hl_29 hl_30 hl_31 hl_32 hl_33 hl_34 hl_35 hl_36 hl_37 hl_38 hl_39 hl_40 hl_41 hl_42 hl_43 hl_44 hl_45 hl_46 hl_47
  group_none hinv4 hG with ⟨hl_0, hl_1, hl_2, hl_3, hl_4, hl_5, hl_6, hl_7, hl_8, hl_9, hl_10, hl_11, hl_12, hl_13, hl_14, hl_15, hl_16, hl_17, hl_18, hl_19, hl_20, hl_21, hl_22, hl_23, hl_24, hl_25, hl_26, hl_27, hl_28, hl_29, hl_30, hl_31, hl_32, hl_33, hl_34, hl_35, hl_36, hl_37, hl_38, hl_39, hl_40, hl_41, hl_42, hl_43, hl_44, hl_45, hl_46, hl_47, hl_48, hl_49, hl_50, hl_51, hl_52, hl_53, hl_54, hl_55, hl_56, hl_57, hl_58, hl_59, hl_60, hl_61, hl_62, hl_63⟩

theorem cases_2_1_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_2_1_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_to_smt.case_64 x_a0, EoCases.__eo_to_smt.case_65 x_a0, EoCases.__eo_to_smt.case_66 x_a0, EoCases.__eo_to_smt.case_67 x_a0, EoCases.__eo_to_smt.case_68 x_a0, EoCases.__eo_to_smt.case_69 x_a0, EoCases.__eo_to_smt.case_70 x_a0, EoCases.__eo_to_smt.case_71 x_a0, EoCases.__eo_to_smt.case_72 x_a0, EoCases.__eo_to_smt.case_73 x_a0, EoCases.__eo_to_smt.case_74 x_a0, EoCases.__eo_to_smt.case_75 x_a0, EoCases.__eo_to_smt.case_76 x_a0, EoCases.__eo_to_smt.case_77 x_a0, EoCases.__eo_to_smt.case_78 x_a0, EoCases.__eo_to_smt.case_79 x_a0, EoCases.__eo_to_smt.case_80 x_a0, EoCases.__eo_to_smt.case_81 x_a0, EoCases.__eo_to_smt.case_82 x_a0, EoCases.__eo_to_smt.case_83 x_a0, EoCases.__eo_to_smt.case_84 x_a0, EoCases.__eo_to_smt.case_85 x_a0, EoCases.__eo_to_smt.case_86 x_a0, EoCases.__eo_to_smt.case_87 x_a0, EoCases.__eo_to_smt.case_88 x_a0, EoCases.__eo_to_smt.case_89 x_a0, EoCases.__eo_to_smt.case_90 x_a0, EoCases.__eo_to_smt.case_91 x_a0, EoCases.__eo_to_smt.case_92 x_a0, EoCases.__eo_to_smt.case_93 x_a0, EoCases.__eo_to_smt.case_94 x_a0, EoCases.__eo_to_smt.case_95 x_a0, EoCases.__eo_to_smt.case_96 x_a0, EoCases.__eo_to_smt.case_97 x_a0, EoCases.__eo_to_smt.case_98 x_a0, EoCases.__eo_to_smt.case_99 x_a0, EoCases.__eo_to_smt.case_100 x_a0, EoCases.__eo_to_smt.case_101 x_a0, EoCases.__eo_to_smt.case_102 x_a0, EoCases.__eo_to_smt.case_103 x_a0, EoCases.__eo_to_smt.case_104 x_a0, EoCases.__eo_to_smt.case_105 x_a0, EoCases.__eo_to_smt.case_106 x_a0, EoCases.__eo_to_smt.case_107 x_a0, EoCases.__eo_to_smt.case_108 x_a0, EoCases.__eo_to_smt.case_109 x_a0, EoCases.__eo_to_smt.case_110 x_a0, EoCases.__eo_to_smt.case_111 x_a0, EoCases.__eo_to_smt.case_112 x_a0, EoCases.__eo_to_smt.case_113 x_a0, EoCases.__eo_to_smt.case_114 x_a0, EoCases.__eo_to_smt.case_115 x_a0, EoCases.__eo_to_smt.case_116 x_a0, EoCases.__eo_to_smt.case_117 x_a0, EoCases.__eo_to_smt.case_118 x_a0, EoCases.__eo_to_smt.case_119 x_a0, EoCases.__eo_to_smt.case_120 x_a0, EoCases.__eo_to_smt.case_121 x_a0, EoCases.__eo_to_smt.case_122 x_a0, EoCases.__eo_to_smt.case_123 x_a0, EoCases.__eo_to_smt.case_124 x_a0, EoCases.__eo_to_smt.case_125 x_a0, EoCases.__eo_to_smt.case_126 x_a0, EoCases.__eo_to_smt.case_127 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_64 x_a0 = none ∧ EoCases.__eo_to_smt.case_65 x_a0 = none ∧ EoCases.__eo_to_smt.case_66 x_a0 = none ∧ EoCases.__eo_to_smt.case_67 x_a0 = none ∧ EoCases.__eo_to_smt.case_68 x_a0 = none ∧ EoCases.__eo_to_smt.case_69 x_a0 = none ∧ EoCases.__eo_to_smt.case_70 x_a0 = none ∧ EoCases.__eo_to_smt.case_71 x_a0 = none ∧ EoCases.__eo_to_smt.case_72 x_a0 = none ∧ EoCases.__eo_to_smt.case_73 x_a0 = none ∧ EoCases.__eo_to_smt.case_74 x_a0 = none ∧ EoCases.__eo_to_smt.case_75 x_a0 = none ∧ EoCases.__eo_to_smt.case_76 x_a0 = none ∧ EoCases.__eo_to_smt.case_77 x_a0 = none ∧ EoCases.__eo_to_smt.case_78 x_a0 = none ∧ EoCases.__eo_to_smt.case_79 x_a0 = none ∧ EoCases.__eo_to_smt.case_80 x_a0 = none ∧ EoCases.__eo_to_smt.case_81 x_a0 = none ∧ EoCases.__eo_to_smt.case_82 x_a0 = none ∧ EoCases.__eo_to_smt.case_83 x_a0 = none ∧ EoCases.__eo_to_smt.case_84 x_a0 = none ∧ EoCases.__eo_to_smt.case_85 x_a0 = none ∧ EoCases.__eo_to_smt.case_86 x_a0 = none ∧ EoCases.__eo_to_smt.case_87 x_a0 = none ∧ EoCases.__eo_to_smt.case_88 x_a0 = none ∧ EoCases.__eo_to_smt.case_89 x_a0 = none ∧ EoCases.__eo_to_smt.case_90 x_a0 = none ∧ EoCases.__eo_to_smt.case_91 x_a0 = none ∧ EoCases.__eo_to_smt.case_92 x_a0 = none ∧ EoCases.__eo_to_smt.case_93 x_a0 = none ∧ EoCases.__eo_to_smt.case_94 x_a0 = none ∧ EoCases.__eo_to_smt.case_95 x_a0 = none ∧ EoCases.__eo_to_smt.case_96 x_a0 = none ∧ EoCases.__eo_to_smt.case_97 x_a0 = none ∧ EoCases.__eo_to_smt.case_98 x_a0 = none ∧ EoCases.__eo_to_smt.case_99 x_a0 = none ∧ EoCases.__eo_to_smt.case_100 x_a0 = none ∧ EoCases.__eo_to_smt.case_101 x_a0 = none ∧ EoCases.__eo_to_smt.case_102 x_a0 = none ∧ EoCases.__eo_to_smt.case_103 x_a0 = none ∧ EoCases.__eo_to_smt.case_104 x_a0 = none ∧ EoCases.__eo_to_smt.case_105 x_a0 = none ∧ EoCases.__eo_to_smt.case_106 x_a0 = none ∧ EoCases.__eo_to_smt.case_107 x_a0 = none ∧ EoCases.__eo_to_smt.case_108 x_a0 = none ∧ EoCases.__eo_to_smt.case_109 x_a0 = none ∧ EoCases.__eo_to_smt.case_110 x_a0 = none ∧ EoCases.__eo_to_smt.case_111 x_a0 = none ∧ EoCases.__eo_to_smt.case_112 x_a0 = none ∧ EoCases.__eo_to_smt.case_113 x_a0 = none ∧ EoCases.__eo_to_smt.case_114 x_a0 = none ∧ EoCases.__eo_to_smt.case_115 x_a0 = none ∧ EoCases.__eo_to_smt.case_116 x_a0 = none ∧ EoCases.__eo_to_smt.case_117 x_a0 = none ∧ EoCases.__eo_to_smt.case_118 x_a0 = none ∧ EoCases.__eo_to_smt.case_119 x_a0 = none ∧ EoCases.__eo_to_smt.case_120 x_a0 = none ∧ EoCases.__eo_to_smt.case_121 x_a0 = none ∧ EoCases.__eo_to_smt.case_122 x_a0 = none ∧ EoCases.__eo_to_smt.case_123 x_a0 = none ∧ EoCases.__eo_to_smt.case_124 x_a0 = none ∧ EoCases.__eo_to_smt.case_125 x_a0 = none ∧ EoCases.__eo_to_smt.case_126 x_a0 = none ∧ EoCases.__eo_to_smt.case_127 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_2_1_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  group_step with cases_1_4_eo__24eo_5fto_5fsmt_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_64 x_a0, EoCases.__eo_to_smt.case_65 x_a0, EoCases.__eo_to_smt.case_66 x_a0, EoCases.__eo_to_smt.case_67 x_a0, EoCases.__eo_to_smt.case_68 x_a0, EoCases.__eo_to_smt.case_69 x_a0, EoCases.__eo_to_smt.case_70 x_a0, EoCases.__eo_to_smt.case_71 x_a0, EoCases.__eo_to_smt.case_72 x_a0, EoCases.__eo_to_smt.case_73 x_a0, EoCases.__eo_to_smt.case_74 x_a0, EoCases.__eo_to_smt.case_75 x_a0, EoCases.__eo_to_smt.case_76 x_a0, EoCases.__eo_to_smt.case_77 x_a0, EoCases.__eo_to_smt.case_78 x_a0, EoCases.__eo_to_smt.case_79 x_a0, EoCases.__eo_to_smt.case_80 x_a0, EoCases.__eo_to_smt.case_81 x_a0, EoCases.__eo_to_smt.case_82 x_a0, EoCases.__eo_to_smt.case_83 x_a0, EoCases.__eo_to_smt.case_84 x_a0, EoCases.__eo_to_smt.case_85 x_a0, EoCases.__eo_to_smt.case_86 x_a0, EoCases.__eo_to_smt.case_87 x_a0, EoCases.__eo_to_smt.case_88 x_a0, EoCases.__eo_to_smt.case_89 x_a0, EoCases.__eo_to_smt.case_90 x_a0, EoCases.__eo_to_smt.case_91 x_a0, EoCases.__eo_to_smt.case_92 x_a0, EoCases.__eo_to_smt.case_93 x_a0, EoCases.__eo_to_smt.case_94 x_a0, EoCases.__eo_to_smt.case_95 x_a0, EoCases.__eo_to_smt.case_96 x_a0, EoCases.__eo_to_smt.case_97 x_a0, EoCases.__eo_to_smt.case_98 x_a0, EoCases.__eo_to_smt.case_99 x_a0, EoCases.__eo_to_smt.case_100 x_a0, EoCases.__eo_to_smt.case_101 x_a0, EoCases.__eo_to_smt.case_102 x_a0, EoCases.__eo_to_smt.case_103 x_a0, EoCases.__eo_to_smt.case_104 x_a0, EoCases.__eo_to_smt.case_105 x_a0, EoCases.__eo_to_smt.case_106 x_a0, EoCases.__eo_to_smt.case_107 x_a0, EoCases.__eo_to_smt.case_108 x_a0, EoCases.__eo_to_smt.case_109 x_a0, EoCases.__eo_to_smt.case_110 x_a0, EoCases.__eo_to_smt.case_111 x_a0, EoCases.__eo_to_smt.case_112 x_a0, EoCases.__eo_to_smt.case_113 x_a0, EoCases.__eo_to_smt.case_114 x_a0, EoCases.__eo_to_smt.case_115 x_a0, EoCases.__eo_to_smt.case_116 x_a0, EoCases.__eo_to_smt.case_117 x_a0, EoCases.__eo_to_smt.case_118 x_a0, EoCases.__eo_to_smt.case_119 x_a0, EoCases.__eo_to_smt.case_120 x_a0, EoCases.__eo_to_smt.case_121 x_a0, EoCases.__eo_to_smt.case_122 x_a0, EoCases.__eo_to_smt.case_123 x_a0, EoCases.__eo_to_smt.case_124 x_a0, EoCases.__eo_to_smt.case_125 x_a0, EoCases.__eo_to_smt.case_126 x_a0, EoCases.__eo_to_smt.case_127 x_a0] = [] ++ [EoCases.__eo_to_smt.case_64 x_a0, EoCases.__eo_to_smt.case_65 x_a0, EoCases.__eo_to_smt.case_66 x_a0, EoCases.__eo_to_smt.case_67 x_a0, EoCases.__eo_to_smt.case_68 x_a0, EoCases.__eo_to_smt.case_69 x_a0, EoCases.__eo_to_smt.case_70 x_a0, EoCases.__eo_to_smt.case_71 x_a0, EoCases.__eo_to_smt.case_72 x_a0, EoCases.__eo_to_smt.case_73 x_a0, EoCases.__eo_to_smt.case_74 x_a0, EoCases.__eo_to_smt.case_75 x_a0, EoCases.__eo_to_smt.case_76 x_a0, EoCases.__eo_to_smt.case_77 x_a0, EoCases.__eo_to_smt.case_78 x_a0, EoCases.__eo_to_smt.case_79 x_a0] ++ [EoCases.__eo_to_smt.case_80 x_a0, EoCases.__eo_to_smt.case_81 x_a0, EoCases.__eo_to_smt.case_82 x_a0, EoCases.__eo_to_smt.case_83 x_a0, EoCases.__eo_to_smt.case_84 x_a0, EoCases.__eo_to_smt.case_85 x_a0, EoCases.__eo_to_smt.case_86 x_a0, EoCases.__eo_to_smt.case_87 x_a0, EoCases.__eo_to_smt.case_88 x_a0, EoCases.__eo_to_smt.case_89 x_a0, EoCases.__eo_to_smt.case_90 x_a0, EoCases.__eo_to_smt.case_91 x_a0, EoCases.__eo_to_smt.case_92 x_a0, EoCases.__eo_to_smt.case_93 x_a0, EoCases.__eo_to_smt.case_94 x_a0, EoCases.__eo_to_smt.case_95 x_a0, EoCases.__eo_to_smt.case_96 x_a0, EoCases.__eo_to_smt.case_97 x_a0, EoCases.__eo_to_smt.case_98 x_a0, EoCases.__eo_to_smt.case_99 x_a0, EoCases.__eo_to_smt.case_100 x_a0, EoCases.__eo_to_smt.case_101 x_a0, EoCases.__eo_to_smt.case_102 x_a0, EoCases.__eo_to_smt.case_103 x_a0, EoCases.__eo_to_smt.case_104 x_a0, EoCases.__eo_to_smt.case_105 x_a0, EoCases.__eo_to_smt.case_106 x_a0, EoCases.__eo_to_smt.case_107 x_a0, EoCases.__eo_to_smt.case_108 x_a0, EoCases.__eo_to_smt.case_109 x_a0, EoCases.__eo_to_smt.case_110 x_a0, EoCases.__eo_to_smt.case_111 x_a0, EoCases.__eo_to_smt.case_112 x_a0, EoCases.__eo_to_smt.case_113 x_a0, EoCases.__eo_to_smt.case_114 x_a0, EoCases.__eo_to_smt.case_115 x_a0, EoCases.__eo_to_smt.case_116 x_a0, EoCases.__eo_to_smt.case_117 x_a0, EoCases.__eo_to_smt.case_118 x_a0, EoCases.__eo_to_smt.case_119 x_a0, EoCases.__eo_to_smt.case_120 x_a0, EoCases.__eo_to_smt.case_121 x_a0, EoCases.__eo_to_smt.case_122 x_a0, EoCases.__eo_to_smt.case_123 x_a0, EoCases.__eo_to_smt.case_124 x_a0, EoCases.__eo_to_smt.case_125 x_a0, EoCases.__eo_to_smt.case_126 x_a0, EoCases.__eo_to_smt.case_127 x_a0] from rfl)
    otherwise ⟨hl_64, hl_65, hl_66, hl_67, hl_68, hl_69, hl_70, hl_71, hl_72, hl_73, hl_74, hl_75, hl_76, hl_77, hl_78, hl_79⟩ using
  group_step with cases_1_5_eo__24eo_5fto_5fsmt_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_64 x_a0, EoCases.__eo_to_smt.case_65 x_a0, EoCases.__eo_to_smt.case_66 x_a0, EoCases.__eo_to_smt.case_67 x_a0, EoCases.__eo_to_smt.case_68 x_a0, EoCases.__eo_to_smt.case_69 x_a0, EoCases.__eo_to_smt.case_70 x_a0, EoCases.__eo_to_smt.case_71 x_a0, EoCases.__eo_to_smt.case_72 x_a0, EoCases.__eo_to_smt.case_73 x_a0, EoCases.__eo_to_smt.case_74 x_a0, EoCases.__eo_to_smt.case_75 x_a0, EoCases.__eo_to_smt.case_76 x_a0, EoCases.__eo_to_smt.case_77 x_a0, EoCases.__eo_to_smt.case_78 x_a0, EoCases.__eo_to_smt.case_79 x_a0, EoCases.__eo_to_smt.case_80 x_a0, EoCases.__eo_to_smt.case_81 x_a0, EoCases.__eo_to_smt.case_82 x_a0, EoCases.__eo_to_smt.case_83 x_a0, EoCases.__eo_to_smt.case_84 x_a0, EoCases.__eo_to_smt.case_85 x_a0, EoCases.__eo_to_smt.case_86 x_a0, EoCases.__eo_to_smt.case_87 x_a0, EoCases.__eo_to_smt.case_88 x_a0, EoCases.__eo_to_smt.case_89 x_a0, EoCases.__eo_to_smt.case_90 x_a0, EoCases.__eo_to_smt.case_91 x_a0, EoCases.__eo_to_smt.case_92 x_a0, EoCases.__eo_to_smt.case_93 x_a0, EoCases.__eo_to_smt.case_94 x_a0, EoCases.__eo_to_smt.case_95 x_a0, EoCases.__eo_to_smt.case_96 x_a0, EoCases.__eo_to_smt.case_97 x_a0, EoCases.__eo_to_smt.case_98 x_a0, EoCases.__eo_to_smt.case_99 x_a0, EoCases.__eo_to_smt.case_100 x_a0, EoCases.__eo_to_smt.case_101 x_a0, EoCases.__eo_to_smt.case_102 x_a0, EoCases.__eo_to_smt.case_103 x_a0, EoCases.__eo_to_smt.case_104 x_a0, EoCases.__eo_to_smt.case_105 x_a0, EoCases.__eo_to_smt.case_106 x_a0, EoCases.__eo_to_smt.case_107 x_a0, EoCases.__eo_to_smt.case_108 x_a0, EoCases.__eo_to_smt.case_109 x_a0, EoCases.__eo_to_smt.case_110 x_a0, EoCases.__eo_to_smt.case_111 x_a0, EoCases.__eo_to_smt.case_112 x_a0, EoCases.__eo_to_smt.case_113 x_a0, EoCases.__eo_to_smt.case_114 x_a0, EoCases.__eo_to_smt.case_115 x_a0, EoCases.__eo_to_smt.case_116 x_a0, EoCases.__eo_to_smt.case_117 x_a0, EoCases.__eo_to_smt.case_118 x_a0, EoCases.__eo_to_smt.case_119 x_a0, EoCases.__eo_to_smt.case_120 x_a0, EoCases.__eo_to_smt.case_121 x_a0, EoCases.__eo_to_smt.case_122 x_a0, EoCases.__eo_to_smt.case_123 x_a0, EoCases.__eo_to_smt.case_124 x_a0, EoCases.__eo_to_smt.case_125 x_a0, EoCases.__eo_to_smt.case_126 x_a0, EoCases.__eo_to_smt.case_127 x_a0] = [EoCases.__eo_to_smt.case_64 x_a0, EoCases.__eo_to_smt.case_65 x_a0, EoCases.__eo_to_smt.case_66 x_a0, EoCases.__eo_to_smt.case_67 x_a0, EoCases.__eo_to_smt.case_68 x_a0, EoCases.__eo_to_smt.case_69 x_a0, EoCases.__eo_to_smt.case_70 x_a0, EoCases.__eo_to_smt.case_71 x_a0, EoCases.__eo_to_smt.case_72 x_a0, EoCases.__eo_to_smt.case_73 x_a0, EoCases.__eo_to_smt.case_74 x_a0, EoCases.__eo_to_smt.case_75 x_a0, EoCases.__eo_to_smt.case_76 x_a0, EoCases.__eo_to_smt.case_77 x_a0, EoCases.__eo_to_smt.case_78 x_a0, EoCases.__eo_to_smt.case_79 x_a0] ++ [EoCases.__eo_to_smt.case_80 x_a0, EoCases.__eo_to_smt.case_81 x_a0, EoCases.__eo_to_smt.case_82 x_a0, EoCases.__eo_to_smt.case_83 x_a0, EoCases.__eo_to_smt.case_84 x_a0, EoCases.__eo_to_smt.case_85 x_a0, EoCases.__eo_to_smt.case_86 x_a0, EoCases.__eo_to_smt.case_87 x_a0, EoCases.__eo_to_smt.case_88 x_a0, EoCases.__eo_to_smt.case_89 x_a0, EoCases.__eo_to_smt.case_90 x_a0, EoCases.__eo_to_smt.case_91 x_a0, EoCases.__eo_to_smt.case_92 x_a0, EoCases.__eo_to_smt.case_93 x_a0, EoCases.__eo_to_smt.case_94 x_a0, EoCases.__eo_to_smt.case_95 x_a0] ++ [EoCases.__eo_to_smt.case_96 x_a0, EoCases.__eo_to_smt.case_97 x_a0, EoCases.__eo_to_smt.case_98 x_a0, EoCases.__eo_to_smt.case_99 x_a0, EoCases.__eo_to_smt.case_100 x_a0, EoCases.__eo_to_smt.case_101 x_a0, EoCases.__eo_to_smt.case_102 x_a0, EoCases.__eo_to_smt.case_103 x_a0, EoCases.__eo_to_smt.case_104 x_a0, EoCases.__eo_to_smt.case_105 x_a0, EoCases.__eo_to_smt.case_106 x_a0, EoCases.__eo_to_smt.case_107 x_a0, EoCases.__eo_to_smt.case_108 x_a0, EoCases.__eo_to_smt.case_109 x_a0, EoCases.__eo_to_smt.case_110 x_a0, EoCases.__eo_to_smt.case_111 x_a0, EoCases.__eo_to_smt.case_112 x_a0, EoCases.__eo_to_smt.case_113 x_a0, EoCases.__eo_to_smt.case_114 x_a0, EoCases.__eo_to_smt.case_115 x_a0, EoCases.__eo_to_smt.case_116 x_a0, EoCases.__eo_to_smt.case_117 x_a0, EoCases.__eo_to_smt.case_118 x_a0, EoCases.__eo_to_smt.case_119 x_a0, EoCases.__eo_to_smt.case_120 x_a0, EoCases.__eo_to_smt.case_121 x_a0, EoCases.__eo_to_smt.case_122 x_a0, EoCases.__eo_to_smt.case_123 x_a0, EoCases.__eo_to_smt.case_124 x_a0, EoCases.__eo_to_smt.case_125 x_a0, EoCases.__eo_to_smt.case_126 x_a0, EoCases.__eo_to_smt.case_127 x_a0] from rfl)
    otherwise ⟨hl_80, hl_81, hl_82, hl_83, hl_84, hl_85, hl_86, hl_87, hl_88, hl_89, hl_90, hl_91, hl_92, hl_93, hl_94, hl_95⟩ using hl_64 hl_65 hl_66 hl_67 hl_68 hl_69 hl_70 hl_71 hl_72 hl_73 hl_74 hl_75 hl_76 hl_77 hl_78 hl_79
  group_step with cases_1_6_eo__24eo_5fto_5fsmt_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_64 x_a0, EoCases.__eo_to_smt.case_65 x_a0, EoCases.__eo_to_smt.case_66 x_a0, EoCases.__eo_to_smt.case_67 x_a0, EoCases.__eo_to_smt.case_68 x_a0, EoCases.__eo_to_smt.case_69 x_a0, EoCases.__eo_to_smt.case_70 x_a0, EoCases.__eo_to_smt.case_71 x_a0, EoCases.__eo_to_smt.case_72 x_a0, EoCases.__eo_to_smt.case_73 x_a0, EoCases.__eo_to_smt.case_74 x_a0, EoCases.__eo_to_smt.case_75 x_a0, EoCases.__eo_to_smt.case_76 x_a0, EoCases.__eo_to_smt.case_77 x_a0, EoCases.__eo_to_smt.case_78 x_a0, EoCases.__eo_to_smt.case_79 x_a0, EoCases.__eo_to_smt.case_80 x_a0, EoCases.__eo_to_smt.case_81 x_a0, EoCases.__eo_to_smt.case_82 x_a0, EoCases.__eo_to_smt.case_83 x_a0, EoCases.__eo_to_smt.case_84 x_a0, EoCases.__eo_to_smt.case_85 x_a0, EoCases.__eo_to_smt.case_86 x_a0, EoCases.__eo_to_smt.case_87 x_a0, EoCases.__eo_to_smt.case_88 x_a0, EoCases.__eo_to_smt.case_89 x_a0, EoCases.__eo_to_smt.case_90 x_a0, EoCases.__eo_to_smt.case_91 x_a0, EoCases.__eo_to_smt.case_92 x_a0, EoCases.__eo_to_smt.case_93 x_a0, EoCases.__eo_to_smt.case_94 x_a0, EoCases.__eo_to_smt.case_95 x_a0, EoCases.__eo_to_smt.case_96 x_a0, EoCases.__eo_to_smt.case_97 x_a0, EoCases.__eo_to_smt.case_98 x_a0, EoCases.__eo_to_smt.case_99 x_a0, EoCases.__eo_to_smt.case_100 x_a0, EoCases.__eo_to_smt.case_101 x_a0, EoCases.__eo_to_smt.case_102 x_a0, EoCases.__eo_to_smt.case_103 x_a0, EoCases.__eo_to_smt.case_104 x_a0, EoCases.__eo_to_smt.case_105 x_a0, EoCases.__eo_to_smt.case_106 x_a0, EoCases.__eo_to_smt.case_107 x_a0, EoCases.__eo_to_smt.case_108 x_a0, EoCases.__eo_to_smt.case_109 x_a0, EoCases.__eo_to_smt.case_110 x_a0, EoCases.__eo_to_smt.case_111 x_a0, EoCases.__eo_to_smt.case_112 x_a0, EoCases.__eo_to_smt.case_113 x_a0, EoCases.__eo_to_smt.case_114 x_a0, EoCases.__eo_to_smt.case_115 x_a0, EoCases.__eo_to_smt.case_116 x_a0, EoCases.__eo_to_smt.case_117 x_a0, EoCases.__eo_to_smt.case_118 x_a0, EoCases.__eo_to_smt.case_119 x_a0, EoCases.__eo_to_smt.case_120 x_a0, EoCases.__eo_to_smt.case_121 x_a0, EoCases.__eo_to_smt.case_122 x_a0, EoCases.__eo_to_smt.case_123 x_a0, EoCases.__eo_to_smt.case_124 x_a0, EoCases.__eo_to_smt.case_125 x_a0, EoCases.__eo_to_smt.case_126 x_a0, EoCases.__eo_to_smt.case_127 x_a0] = [EoCases.__eo_to_smt.case_64 x_a0, EoCases.__eo_to_smt.case_65 x_a0, EoCases.__eo_to_smt.case_66 x_a0, EoCases.__eo_to_smt.case_67 x_a0, EoCases.__eo_to_smt.case_68 x_a0, EoCases.__eo_to_smt.case_69 x_a0, EoCases.__eo_to_smt.case_70 x_a0, EoCases.__eo_to_smt.case_71 x_a0, EoCases.__eo_to_smt.case_72 x_a0, EoCases.__eo_to_smt.case_73 x_a0, EoCases.__eo_to_smt.case_74 x_a0, EoCases.__eo_to_smt.case_75 x_a0, EoCases.__eo_to_smt.case_76 x_a0, EoCases.__eo_to_smt.case_77 x_a0, EoCases.__eo_to_smt.case_78 x_a0, EoCases.__eo_to_smt.case_79 x_a0, EoCases.__eo_to_smt.case_80 x_a0, EoCases.__eo_to_smt.case_81 x_a0, EoCases.__eo_to_smt.case_82 x_a0, EoCases.__eo_to_smt.case_83 x_a0, EoCases.__eo_to_smt.case_84 x_a0, EoCases.__eo_to_smt.case_85 x_a0, EoCases.__eo_to_smt.case_86 x_a0, EoCases.__eo_to_smt.case_87 x_a0, EoCases.__eo_to_smt.case_88 x_a0, EoCases.__eo_to_smt.case_89 x_a0, EoCases.__eo_to_smt.case_90 x_a0, EoCases.__eo_to_smt.case_91 x_a0, EoCases.__eo_to_smt.case_92 x_a0, EoCases.__eo_to_smt.case_93 x_a0, EoCases.__eo_to_smt.case_94 x_a0, EoCases.__eo_to_smt.case_95 x_a0] ++ [EoCases.__eo_to_smt.case_96 x_a0, EoCases.__eo_to_smt.case_97 x_a0, EoCases.__eo_to_smt.case_98 x_a0, EoCases.__eo_to_smt.case_99 x_a0, EoCases.__eo_to_smt.case_100 x_a0, EoCases.__eo_to_smt.case_101 x_a0, EoCases.__eo_to_smt.case_102 x_a0, EoCases.__eo_to_smt.case_103 x_a0, EoCases.__eo_to_smt.case_104 x_a0, EoCases.__eo_to_smt.case_105 x_a0, EoCases.__eo_to_smt.case_106 x_a0, EoCases.__eo_to_smt.case_107 x_a0, EoCases.__eo_to_smt.case_108 x_a0, EoCases.__eo_to_smt.case_109 x_a0, EoCases.__eo_to_smt.case_110 x_a0, EoCases.__eo_to_smt.case_111 x_a0] ++ [EoCases.__eo_to_smt.case_112 x_a0, EoCases.__eo_to_smt.case_113 x_a0, EoCases.__eo_to_smt.case_114 x_a0, EoCases.__eo_to_smt.case_115 x_a0, EoCases.__eo_to_smt.case_116 x_a0, EoCases.__eo_to_smt.case_117 x_a0, EoCases.__eo_to_smt.case_118 x_a0, EoCases.__eo_to_smt.case_119 x_a0, EoCases.__eo_to_smt.case_120 x_a0, EoCases.__eo_to_smt.case_121 x_a0, EoCases.__eo_to_smt.case_122 x_a0, EoCases.__eo_to_smt.case_123 x_a0, EoCases.__eo_to_smt.case_124 x_a0, EoCases.__eo_to_smt.case_125 x_a0, EoCases.__eo_to_smt.case_126 x_a0, EoCases.__eo_to_smt.case_127 x_a0] from rfl)
    otherwise ⟨hl_96, hl_97, hl_98, hl_99, hl_100, hl_101, hl_102, hl_103, hl_104, hl_105, hl_106, hl_107, hl_108, hl_109, hl_110, hl_111⟩ using hl_64 hl_65 hl_66 hl_67 hl_68 hl_69 hl_70 hl_71 hl_72 hl_73 hl_74 hl_75 hl_76 hl_77 hl_78 hl_79 hl_80 hl_81 hl_82 hl_83 hl_84 hl_85 hl_86 hl_87 hl_88 hl_89 hl_90 hl_91 hl_92 hl_93 hl_94 hl_95
  group_step with cases_1_7_eo__24eo_5fto_5fsmt_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_64 x_a0, EoCases.__eo_to_smt.case_65 x_a0, EoCases.__eo_to_smt.case_66 x_a0, EoCases.__eo_to_smt.case_67 x_a0, EoCases.__eo_to_smt.case_68 x_a0, EoCases.__eo_to_smt.case_69 x_a0, EoCases.__eo_to_smt.case_70 x_a0, EoCases.__eo_to_smt.case_71 x_a0, EoCases.__eo_to_smt.case_72 x_a0, EoCases.__eo_to_smt.case_73 x_a0, EoCases.__eo_to_smt.case_74 x_a0, EoCases.__eo_to_smt.case_75 x_a0, EoCases.__eo_to_smt.case_76 x_a0, EoCases.__eo_to_smt.case_77 x_a0, EoCases.__eo_to_smt.case_78 x_a0, EoCases.__eo_to_smt.case_79 x_a0, EoCases.__eo_to_smt.case_80 x_a0, EoCases.__eo_to_smt.case_81 x_a0, EoCases.__eo_to_smt.case_82 x_a0, EoCases.__eo_to_smt.case_83 x_a0, EoCases.__eo_to_smt.case_84 x_a0, EoCases.__eo_to_smt.case_85 x_a0, EoCases.__eo_to_smt.case_86 x_a0, EoCases.__eo_to_smt.case_87 x_a0, EoCases.__eo_to_smt.case_88 x_a0, EoCases.__eo_to_smt.case_89 x_a0, EoCases.__eo_to_smt.case_90 x_a0, EoCases.__eo_to_smt.case_91 x_a0, EoCases.__eo_to_smt.case_92 x_a0, EoCases.__eo_to_smt.case_93 x_a0, EoCases.__eo_to_smt.case_94 x_a0, EoCases.__eo_to_smt.case_95 x_a0, EoCases.__eo_to_smt.case_96 x_a0, EoCases.__eo_to_smt.case_97 x_a0, EoCases.__eo_to_smt.case_98 x_a0, EoCases.__eo_to_smt.case_99 x_a0, EoCases.__eo_to_smt.case_100 x_a0, EoCases.__eo_to_smt.case_101 x_a0, EoCases.__eo_to_smt.case_102 x_a0, EoCases.__eo_to_smt.case_103 x_a0, EoCases.__eo_to_smt.case_104 x_a0, EoCases.__eo_to_smt.case_105 x_a0, EoCases.__eo_to_smt.case_106 x_a0, EoCases.__eo_to_smt.case_107 x_a0, EoCases.__eo_to_smt.case_108 x_a0, EoCases.__eo_to_smt.case_109 x_a0, EoCases.__eo_to_smt.case_110 x_a0, EoCases.__eo_to_smt.case_111 x_a0, EoCases.__eo_to_smt.case_112 x_a0, EoCases.__eo_to_smt.case_113 x_a0, EoCases.__eo_to_smt.case_114 x_a0, EoCases.__eo_to_smt.case_115 x_a0, EoCases.__eo_to_smt.case_116 x_a0, EoCases.__eo_to_smt.case_117 x_a0, EoCases.__eo_to_smt.case_118 x_a0, EoCases.__eo_to_smt.case_119 x_a0, EoCases.__eo_to_smt.case_120 x_a0, EoCases.__eo_to_smt.case_121 x_a0, EoCases.__eo_to_smt.case_122 x_a0, EoCases.__eo_to_smt.case_123 x_a0, EoCases.__eo_to_smt.case_124 x_a0, EoCases.__eo_to_smt.case_125 x_a0, EoCases.__eo_to_smt.case_126 x_a0, EoCases.__eo_to_smt.case_127 x_a0] = [EoCases.__eo_to_smt.case_64 x_a0, EoCases.__eo_to_smt.case_65 x_a0, EoCases.__eo_to_smt.case_66 x_a0, EoCases.__eo_to_smt.case_67 x_a0, EoCases.__eo_to_smt.case_68 x_a0, EoCases.__eo_to_smt.case_69 x_a0, EoCases.__eo_to_smt.case_70 x_a0, EoCases.__eo_to_smt.case_71 x_a0, EoCases.__eo_to_smt.case_72 x_a0, EoCases.__eo_to_smt.case_73 x_a0, EoCases.__eo_to_smt.case_74 x_a0, EoCases.__eo_to_smt.case_75 x_a0, EoCases.__eo_to_smt.case_76 x_a0, EoCases.__eo_to_smt.case_77 x_a0, EoCases.__eo_to_smt.case_78 x_a0, EoCases.__eo_to_smt.case_79 x_a0, EoCases.__eo_to_smt.case_80 x_a0, EoCases.__eo_to_smt.case_81 x_a0, EoCases.__eo_to_smt.case_82 x_a0, EoCases.__eo_to_smt.case_83 x_a0, EoCases.__eo_to_smt.case_84 x_a0, EoCases.__eo_to_smt.case_85 x_a0, EoCases.__eo_to_smt.case_86 x_a0, EoCases.__eo_to_smt.case_87 x_a0, EoCases.__eo_to_smt.case_88 x_a0, EoCases.__eo_to_smt.case_89 x_a0, EoCases.__eo_to_smt.case_90 x_a0, EoCases.__eo_to_smt.case_91 x_a0, EoCases.__eo_to_smt.case_92 x_a0, EoCases.__eo_to_smt.case_93 x_a0, EoCases.__eo_to_smt.case_94 x_a0, EoCases.__eo_to_smt.case_95 x_a0, EoCases.__eo_to_smt.case_96 x_a0, EoCases.__eo_to_smt.case_97 x_a0, EoCases.__eo_to_smt.case_98 x_a0, EoCases.__eo_to_smt.case_99 x_a0, EoCases.__eo_to_smt.case_100 x_a0, EoCases.__eo_to_smt.case_101 x_a0, EoCases.__eo_to_smt.case_102 x_a0, EoCases.__eo_to_smt.case_103 x_a0, EoCases.__eo_to_smt.case_104 x_a0, EoCases.__eo_to_smt.case_105 x_a0, EoCases.__eo_to_smt.case_106 x_a0, EoCases.__eo_to_smt.case_107 x_a0, EoCases.__eo_to_smt.case_108 x_a0, EoCases.__eo_to_smt.case_109 x_a0, EoCases.__eo_to_smt.case_110 x_a0, EoCases.__eo_to_smt.case_111 x_a0] ++ [EoCases.__eo_to_smt.case_112 x_a0, EoCases.__eo_to_smt.case_113 x_a0, EoCases.__eo_to_smt.case_114 x_a0, EoCases.__eo_to_smt.case_115 x_a0, EoCases.__eo_to_smt.case_116 x_a0, EoCases.__eo_to_smt.case_117 x_a0, EoCases.__eo_to_smt.case_118 x_a0, EoCases.__eo_to_smt.case_119 x_a0, EoCases.__eo_to_smt.case_120 x_a0, EoCases.__eo_to_smt.case_121 x_a0, EoCases.__eo_to_smt.case_122 x_a0, EoCases.__eo_to_smt.case_123 x_a0, EoCases.__eo_to_smt.case_124 x_a0, EoCases.__eo_to_smt.case_125 x_a0, EoCases.__eo_to_smt.case_126 x_a0, EoCases.__eo_to_smt.case_127 x_a0] ++ [] from rfl)
    otherwise ⟨hl_112, hl_113, hl_114, hl_115, hl_116, hl_117, hl_118, hl_119, hl_120, hl_121, hl_122, hl_123, hl_124, hl_125, hl_126, hl_127⟩ using hl_64 hl_65 hl_66 hl_67 hl_68 hl_69 hl_70 hl_71 hl_72 hl_73 hl_74 hl_75 hl_76 hl_77 hl_78 hl_79 hl_80 hl_81 hl_82 hl_83 hl_84 hl_85 hl_86 hl_87 hl_88 hl_89 hl_90 hl_91 hl_92 hl_93 hl_94 hl_95 hl_96 hl_97 hl_98 hl_99 hl_100 hl_101 hl_102 hl_103 hl_104 hl_105 hl_106 hl_107 hl_108 hl_109 hl_110 hl_111
  group_none hinv4 hG with ⟨hl_64, hl_65, hl_66, hl_67, hl_68, hl_69, hl_70, hl_71, hl_72, hl_73, hl_74, hl_75, hl_76, hl_77, hl_78, hl_79, hl_80, hl_81, hl_82, hl_83, hl_84, hl_85, hl_86, hl_87, hl_88, hl_89, hl_90, hl_91, hl_92, hl_93, hl_94, hl_95, hl_96, hl_97, hl_98, hl_99, hl_100, hl_101, hl_102, hl_103, hl_104, hl_105, hl_106, hl_107, hl_108, hl_109, hl_110, hl_111, hl_112, hl_113, hl_114, hl_115, hl_116, hl_117, hl_118, hl_119, hl_120, hl_121, hl_122, hl_123, hl_124, hl_125, hl_126, hl_127⟩

theorem cases_2_2_eo__24eo_5fto_5fsmt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_2_2_eo__24eo_5fto_5fsmt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_to_smt.case_128 x_a0, EoCases.__eo_to_smt.case_129 x_a0, EoCases.__eo_to_smt.case_130 x_a0, EoCases.__eo_to_smt.case_131 x_a0, EoCases.__eo_to_smt.case_132 x_a0, EoCases.__eo_to_smt.case_133 x_a0, EoCases.__eo_to_smt.case_134 x_a0, EoCases.__eo_to_smt.case_135 x_a0, EoCases.__eo_to_smt.case_136 x_a0, EoCases.__eo_to_smt.case_137 x_a0, EoCases.__eo_to_smt.case_138 x_a0, EoCases.__eo_to_smt.case_139 x_a0, EoCases.__eo_to_smt.case_140 x_a0, EoCases.__eo_to_smt.case_141 x_a0, EoCases.__eo_to_smt.case_142 x_a0, EoCases.__eo_to_smt.case_143 x_a0, EoCases.__eo_to_smt.case_144 x_a0, EoCases.__eo_to_smt.case_145 x_a0, EoCases.__eo_to_smt.case_146 x_a0, EoCases.__eo_to_smt.case_147 x_a0, EoCases.__eo_to_smt.case_148 x_a0, EoCases.__eo_to_smt.case_149 x_a0, EoCases.__eo_to_smt.case_150 x_a0, EoCases.__eo_to_smt.case_151 x_a0, EoCases.__eo_to_smt.case_152 x_a0, EoCases.__eo_to_smt.case_153 x_a0, EoCases.__eo_to_smt.case_154 x_a0, EoCases.__eo_to_smt.case_155 x_a0, EoCases.__eo_to_smt.case_156 x_a0, EoCases.__eo_to_smt.case_157 x_a0, EoCases.__eo_to_smt.case_158 x_a0, EoCases.__eo_to_smt.case_159 x_a0, EoCases.__eo_to_smt.case_160 x_a0, EoCases.__eo_to_smt.case_161 x_a0, EoCases.__eo_to_smt.case_162 x_a0, EoCases.__eo_to_smt.case_163 x_a0, EoCases.__eo_to_smt.case_164 x_a0, EoCases.__eo_to_smt.case_165 x_a0, EoCases.__eo_to_smt.case_166 x_a0, EoCases.__eo_to_smt.case_167 x_a0, EoCases.__eo_to_smt.case_168 x_a0, EoCases.__eo_to_smt.case_169 x_a0, EoCases.__eo_to_smt.case_170 x_a0, EoCases.__eo_to_smt.case_171 x_a0, EoCases.__eo_to_smt.case_172 x_a0, EoCases.__eo_to_smt.case_173 x_a0, EoCases.__eo_to_smt.case_174 x_a0, EoCases.__eo_to_smt.case_175 x_a0, EoCases.__eo_to_smt.case_176 x_a0, EoCases.__eo_to_smt.case_177 x_a0, EoCases.__eo_to_smt.case_178 x_a0, EoCases.__eo_to_smt.case_179 x_a0, EoCases.__eo_to_smt.case_180 x_a0, EoCases.__eo_to_smt.case_181 x_a0, EoCases.__eo_to_smt.case_182 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt.case_128 x_a0 = none ∧ EoCases.__eo_to_smt.case_129 x_a0 = none ∧ EoCases.__eo_to_smt.case_130 x_a0 = none ∧ EoCases.__eo_to_smt.case_131 x_a0 = none ∧ EoCases.__eo_to_smt.case_132 x_a0 = none ∧ EoCases.__eo_to_smt.case_133 x_a0 = none ∧ EoCases.__eo_to_smt.case_134 x_a0 = none ∧ EoCases.__eo_to_smt.case_135 x_a0 = none ∧ EoCases.__eo_to_smt.case_136 x_a0 = none ∧ EoCases.__eo_to_smt.case_137 x_a0 = none ∧ EoCases.__eo_to_smt.case_138 x_a0 = none ∧ EoCases.__eo_to_smt.case_139 x_a0 = none ∧ EoCases.__eo_to_smt.case_140 x_a0 = none ∧ EoCases.__eo_to_smt.case_141 x_a0 = none ∧ EoCases.__eo_to_smt.case_142 x_a0 = none ∧ EoCases.__eo_to_smt.case_143 x_a0 = none ∧ EoCases.__eo_to_smt.case_144 x_a0 = none ∧ EoCases.__eo_to_smt.case_145 x_a0 = none ∧ EoCases.__eo_to_smt.case_146 x_a0 = none ∧ EoCases.__eo_to_smt.case_147 x_a0 = none ∧ EoCases.__eo_to_smt.case_148 x_a0 = none ∧ EoCases.__eo_to_smt.case_149 x_a0 = none ∧ EoCases.__eo_to_smt.case_150 x_a0 = none ∧ EoCases.__eo_to_smt.case_151 x_a0 = none ∧ EoCases.__eo_to_smt.case_152 x_a0 = none ∧ EoCases.__eo_to_smt.case_153 x_a0 = none ∧ EoCases.__eo_to_smt.case_154 x_a0 = none ∧ EoCases.__eo_to_smt.case_155 x_a0 = none ∧ EoCases.__eo_to_smt.case_156 x_a0 = none ∧ EoCases.__eo_to_smt.case_157 x_a0 = none ∧ EoCases.__eo_to_smt.case_158 x_a0 = none ∧ EoCases.__eo_to_smt.case_159 x_a0 = none ∧ EoCases.__eo_to_smt.case_160 x_a0 = none ∧ EoCases.__eo_to_smt.case_161 x_a0 = none ∧ EoCases.__eo_to_smt.case_162 x_a0 = none ∧ EoCases.__eo_to_smt.case_163 x_a0 = none ∧ EoCases.__eo_to_smt.case_164 x_a0 = none ∧ EoCases.__eo_to_smt.case_165 x_a0 = none ∧ EoCases.__eo_to_smt.case_166 x_a0 = none ∧ EoCases.__eo_to_smt.case_167 x_a0 = none ∧ EoCases.__eo_to_smt.case_168 x_a0 = none ∧ EoCases.__eo_to_smt.case_169 x_a0 = none ∧ EoCases.__eo_to_smt.case_170 x_a0 = none ∧ EoCases.__eo_to_smt.case_171 x_a0 = none ∧ EoCases.__eo_to_smt.case_172 x_a0 = none ∧ EoCases.__eo_to_smt.case_173 x_a0 = none ∧ EoCases.__eo_to_smt.case_174 x_a0 = none ∧ EoCases.__eo_to_smt.case_175 x_a0 = none ∧ EoCases.__eo_to_smt.case_176 x_a0 = none ∧ EoCases.__eo_to_smt.case_177 x_a0 = none ∧ EoCases.__eo_to_smt.case_178 x_a0 = none ∧ EoCases.__eo_to_smt.case_179 x_a0 = none ∧ EoCases.__eo_to_smt.case_180 x_a0 = none ∧ EoCases.__eo_to_smt.case_181 x_a0 = none ∧ EoCases.__eo_to_smt.case_182 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_2_2_eo__24eo_5fto_5fsmt
  have hG := Store.Grows.refl s
  group_step with cases_1_8_eo__24eo_5fto_5fsmt_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_128 x_a0, EoCases.__eo_to_smt.case_129 x_a0, EoCases.__eo_to_smt.case_130 x_a0, EoCases.__eo_to_smt.case_131 x_a0, EoCases.__eo_to_smt.case_132 x_a0, EoCases.__eo_to_smt.case_133 x_a0, EoCases.__eo_to_smt.case_134 x_a0, EoCases.__eo_to_smt.case_135 x_a0, EoCases.__eo_to_smt.case_136 x_a0, EoCases.__eo_to_smt.case_137 x_a0, EoCases.__eo_to_smt.case_138 x_a0, EoCases.__eo_to_smt.case_139 x_a0, EoCases.__eo_to_smt.case_140 x_a0, EoCases.__eo_to_smt.case_141 x_a0, EoCases.__eo_to_smt.case_142 x_a0, EoCases.__eo_to_smt.case_143 x_a0, EoCases.__eo_to_smt.case_144 x_a0, EoCases.__eo_to_smt.case_145 x_a0, EoCases.__eo_to_smt.case_146 x_a0, EoCases.__eo_to_smt.case_147 x_a0, EoCases.__eo_to_smt.case_148 x_a0, EoCases.__eo_to_smt.case_149 x_a0, EoCases.__eo_to_smt.case_150 x_a0, EoCases.__eo_to_smt.case_151 x_a0, EoCases.__eo_to_smt.case_152 x_a0, EoCases.__eo_to_smt.case_153 x_a0, EoCases.__eo_to_smt.case_154 x_a0, EoCases.__eo_to_smt.case_155 x_a0, EoCases.__eo_to_smt.case_156 x_a0, EoCases.__eo_to_smt.case_157 x_a0, EoCases.__eo_to_smt.case_158 x_a0, EoCases.__eo_to_smt.case_159 x_a0, EoCases.__eo_to_smt.case_160 x_a0, EoCases.__eo_to_smt.case_161 x_a0, EoCases.__eo_to_smt.case_162 x_a0, EoCases.__eo_to_smt.case_163 x_a0, EoCases.__eo_to_smt.case_164 x_a0, EoCases.__eo_to_smt.case_165 x_a0, EoCases.__eo_to_smt.case_166 x_a0, EoCases.__eo_to_smt.case_167 x_a0, EoCases.__eo_to_smt.case_168 x_a0, EoCases.__eo_to_smt.case_169 x_a0, EoCases.__eo_to_smt.case_170 x_a0, EoCases.__eo_to_smt.case_171 x_a0, EoCases.__eo_to_smt.case_172 x_a0, EoCases.__eo_to_smt.case_173 x_a0, EoCases.__eo_to_smt.case_174 x_a0, EoCases.__eo_to_smt.case_175 x_a0, EoCases.__eo_to_smt.case_176 x_a0, EoCases.__eo_to_smt.case_177 x_a0, EoCases.__eo_to_smt.case_178 x_a0, EoCases.__eo_to_smt.case_179 x_a0, EoCases.__eo_to_smt.case_180 x_a0, EoCases.__eo_to_smt.case_181 x_a0, EoCases.__eo_to_smt.case_182 x_a0] = [] ++ [EoCases.__eo_to_smt.case_128 x_a0, EoCases.__eo_to_smt.case_129 x_a0, EoCases.__eo_to_smt.case_130 x_a0, EoCases.__eo_to_smt.case_131 x_a0, EoCases.__eo_to_smt.case_132 x_a0, EoCases.__eo_to_smt.case_133 x_a0, EoCases.__eo_to_smt.case_134 x_a0, EoCases.__eo_to_smt.case_135 x_a0, EoCases.__eo_to_smt.case_136 x_a0, EoCases.__eo_to_smt.case_137 x_a0, EoCases.__eo_to_smt.case_138 x_a0, EoCases.__eo_to_smt.case_139 x_a0, EoCases.__eo_to_smt.case_140 x_a0, EoCases.__eo_to_smt.case_141 x_a0, EoCases.__eo_to_smt.case_142 x_a0, EoCases.__eo_to_smt.case_143 x_a0] ++ [EoCases.__eo_to_smt.case_144 x_a0, EoCases.__eo_to_smt.case_145 x_a0, EoCases.__eo_to_smt.case_146 x_a0, EoCases.__eo_to_smt.case_147 x_a0, EoCases.__eo_to_smt.case_148 x_a0, EoCases.__eo_to_smt.case_149 x_a0, EoCases.__eo_to_smt.case_150 x_a0, EoCases.__eo_to_smt.case_151 x_a0, EoCases.__eo_to_smt.case_152 x_a0, EoCases.__eo_to_smt.case_153 x_a0, EoCases.__eo_to_smt.case_154 x_a0, EoCases.__eo_to_smt.case_155 x_a0, EoCases.__eo_to_smt.case_156 x_a0, EoCases.__eo_to_smt.case_157 x_a0, EoCases.__eo_to_smt.case_158 x_a0, EoCases.__eo_to_smt.case_159 x_a0, EoCases.__eo_to_smt.case_160 x_a0, EoCases.__eo_to_smt.case_161 x_a0, EoCases.__eo_to_smt.case_162 x_a0, EoCases.__eo_to_smt.case_163 x_a0, EoCases.__eo_to_smt.case_164 x_a0, EoCases.__eo_to_smt.case_165 x_a0, EoCases.__eo_to_smt.case_166 x_a0, EoCases.__eo_to_smt.case_167 x_a0, EoCases.__eo_to_smt.case_168 x_a0, EoCases.__eo_to_smt.case_169 x_a0, EoCases.__eo_to_smt.case_170 x_a0, EoCases.__eo_to_smt.case_171 x_a0, EoCases.__eo_to_smt.case_172 x_a0, EoCases.__eo_to_smt.case_173 x_a0, EoCases.__eo_to_smt.case_174 x_a0, EoCases.__eo_to_smt.case_175 x_a0, EoCases.__eo_to_smt.case_176 x_a0, EoCases.__eo_to_smt.case_177 x_a0, EoCases.__eo_to_smt.case_178 x_a0, EoCases.__eo_to_smt.case_179 x_a0, EoCases.__eo_to_smt.case_180 x_a0, EoCases.__eo_to_smt.case_181 x_a0, EoCases.__eo_to_smt.case_182 x_a0] from rfl)
    otherwise ⟨hl_128, hl_129, hl_130, hl_131, hl_132, hl_133, hl_134, hl_135, hl_136, hl_137, hl_138, hl_139, hl_140, hl_141, hl_142, hl_143⟩ using
  group_step with cases_1_9_eo__24eo_5fto_5fsmt_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_128 x_a0, EoCases.__eo_to_smt.case_129 x_a0, EoCases.__eo_to_smt.case_130 x_a0, EoCases.__eo_to_smt.case_131 x_a0, EoCases.__eo_to_smt.case_132 x_a0, EoCases.__eo_to_smt.case_133 x_a0, EoCases.__eo_to_smt.case_134 x_a0, EoCases.__eo_to_smt.case_135 x_a0, EoCases.__eo_to_smt.case_136 x_a0, EoCases.__eo_to_smt.case_137 x_a0, EoCases.__eo_to_smt.case_138 x_a0, EoCases.__eo_to_smt.case_139 x_a0, EoCases.__eo_to_smt.case_140 x_a0, EoCases.__eo_to_smt.case_141 x_a0, EoCases.__eo_to_smt.case_142 x_a0, EoCases.__eo_to_smt.case_143 x_a0, EoCases.__eo_to_smt.case_144 x_a0, EoCases.__eo_to_smt.case_145 x_a0, EoCases.__eo_to_smt.case_146 x_a0, EoCases.__eo_to_smt.case_147 x_a0, EoCases.__eo_to_smt.case_148 x_a0, EoCases.__eo_to_smt.case_149 x_a0, EoCases.__eo_to_smt.case_150 x_a0, EoCases.__eo_to_smt.case_151 x_a0, EoCases.__eo_to_smt.case_152 x_a0, EoCases.__eo_to_smt.case_153 x_a0, EoCases.__eo_to_smt.case_154 x_a0, EoCases.__eo_to_smt.case_155 x_a0, EoCases.__eo_to_smt.case_156 x_a0, EoCases.__eo_to_smt.case_157 x_a0, EoCases.__eo_to_smt.case_158 x_a0, EoCases.__eo_to_smt.case_159 x_a0, EoCases.__eo_to_smt.case_160 x_a0, EoCases.__eo_to_smt.case_161 x_a0, EoCases.__eo_to_smt.case_162 x_a0, EoCases.__eo_to_smt.case_163 x_a0, EoCases.__eo_to_smt.case_164 x_a0, EoCases.__eo_to_smt.case_165 x_a0, EoCases.__eo_to_smt.case_166 x_a0, EoCases.__eo_to_smt.case_167 x_a0, EoCases.__eo_to_smt.case_168 x_a0, EoCases.__eo_to_smt.case_169 x_a0, EoCases.__eo_to_smt.case_170 x_a0, EoCases.__eo_to_smt.case_171 x_a0, EoCases.__eo_to_smt.case_172 x_a0, EoCases.__eo_to_smt.case_173 x_a0, EoCases.__eo_to_smt.case_174 x_a0, EoCases.__eo_to_smt.case_175 x_a0, EoCases.__eo_to_smt.case_176 x_a0, EoCases.__eo_to_smt.case_177 x_a0, EoCases.__eo_to_smt.case_178 x_a0, EoCases.__eo_to_smt.case_179 x_a0, EoCases.__eo_to_smt.case_180 x_a0, EoCases.__eo_to_smt.case_181 x_a0, EoCases.__eo_to_smt.case_182 x_a0] = [EoCases.__eo_to_smt.case_128 x_a0, EoCases.__eo_to_smt.case_129 x_a0, EoCases.__eo_to_smt.case_130 x_a0, EoCases.__eo_to_smt.case_131 x_a0, EoCases.__eo_to_smt.case_132 x_a0, EoCases.__eo_to_smt.case_133 x_a0, EoCases.__eo_to_smt.case_134 x_a0, EoCases.__eo_to_smt.case_135 x_a0, EoCases.__eo_to_smt.case_136 x_a0, EoCases.__eo_to_smt.case_137 x_a0, EoCases.__eo_to_smt.case_138 x_a0, EoCases.__eo_to_smt.case_139 x_a0, EoCases.__eo_to_smt.case_140 x_a0, EoCases.__eo_to_smt.case_141 x_a0, EoCases.__eo_to_smt.case_142 x_a0, EoCases.__eo_to_smt.case_143 x_a0] ++ [EoCases.__eo_to_smt.case_144 x_a0, EoCases.__eo_to_smt.case_145 x_a0, EoCases.__eo_to_smt.case_146 x_a0, EoCases.__eo_to_smt.case_147 x_a0, EoCases.__eo_to_smt.case_148 x_a0, EoCases.__eo_to_smt.case_149 x_a0, EoCases.__eo_to_smt.case_150 x_a0, EoCases.__eo_to_smt.case_151 x_a0, EoCases.__eo_to_smt.case_152 x_a0, EoCases.__eo_to_smt.case_153 x_a0, EoCases.__eo_to_smt.case_154 x_a0, EoCases.__eo_to_smt.case_155 x_a0, EoCases.__eo_to_smt.case_156 x_a0, EoCases.__eo_to_smt.case_157 x_a0, EoCases.__eo_to_smt.case_158 x_a0, EoCases.__eo_to_smt.case_159 x_a0] ++ [EoCases.__eo_to_smt.case_160 x_a0, EoCases.__eo_to_smt.case_161 x_a0, EoCases.__eo_to_smt.case_162 x_a0, EoCases.__eo_to_smt.case_163 x_a0, EoCases.__eo_to_smt.case_164 x_a0, EoCases.__eo_to_smt.case_165 x_a0, EoCases.__eo_to_smt.case_166 x_a0, EoCases.__eo_to_smt.case_167 x_a0, EoCases.__eo_to_smt.case_168 x_a0, EoCases.__eo_to_smt.case_169 x_a0, EoCases.__eo_to_smt.case_170 x_a0, EoCases.__eo_to_smt.case_171 x_a0, EoCases.__eo_to_smt.case_172 x_a0, EoCases.__eo_to_smt.case_173 x_a0, EoCases.__eo_to_smt.case_174 x_a0, EoCases.__eo_to_smt.case_175 x_a0, EoCases.__eo_to_smt.case_176 x_a0, EoCases.__eo_to_smt.case_177 x_a0, EoCases.__eo_to_smt.case_178 x_a0, EoCases.__eo_to_smt.case_179 x_a0, EoCases.__eo_to_smt.case_180 x_a0, EoCases.__eo_to_smt.case_181 x_a0, EoCases.__eo_to_smt.case_182 x_a0] from rfl)
    otherwise ⟨hl_144, hl_145, hl_146, hl_147, hl_148, hl_149, hl_150, hl_151, hl_152, hl_153, hl_154, hl_155, hl_156, hl_157, hl_158, hl_159⟩ using hl_128 hl_129 hl_130 hl_131 hl_132 hl_133 hl_134 hl_135 hl_136 hl_137 hl_138 hl_139 hl_140 hl_141 hl_142 hl_143
  group_step with cases_1_10_eo__24eo_5fto_5fsmt_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_128 x_a0, EoCases.__eo_to_smt.case_129 x_a0, EoCases.__eo_to_smt.case_130 x_a0, EoCases.__eo_to_smt.case_131 x_a0, EoCases.__eo_to_smt.case_132 x_a0, EoCases.__eo_to_smt.case_133 x_a0, EoCases.__eo_to_smt.case_134 x_a0, EoCases.__eo_to_smt.case_135 x_a0, EoCases.__eo_to_smt.case_136 x_a0, EoCases.__eo_to_smt.case_137 x_a0, EoCases.__eo_to_smt.case_138 x_a0, EoCases.__eo_to_smt.case_139 x_a0, EoCases.__eo_to_smt.case_140 x_a0, EoCases.__eo_to_smt.case_141 x_a0, EoCases.__eo_to_smt.case_142 x_a0, EoCases.__eo_to_smt.case_143 x_a0, EoCases.__eo_to_smt.case_144 x_a0, EoCases.__eo_to_smt.case_145 x_a0, EoCases.__eo_to_smt.case_146 x_a0, EoCases.__eo_to_smt.case_147 x_a0, EoCases.__eo_to_smt.case_148 x_a0, EoCases.__eo_to_smt.case_149 x_a0, EoCases.__eo_to_smt.case_150 x_a0, EoCases.__eo_to_smt.case_151 x_a0, EoCases.__eo_to_smt.case_152 x_a0, EoCases.__eo_to_smt.case_153 x_a0, EoCases.__eo_to_smt.case_154 x_a0, EoCases.__eo_to_smt.case_155 x_a0, EoCases.__eo_to_smt.case_156 x_a0, EoCases.__eo_to_smt.case_157 x_a0, EoCases.__eo_to_smt.case_158 x_a0, EoCases.__eo_to_smt.case_159 x_a0, EoCases.__eo_to_smt.case_160 x_a0, EoCases.__eo_to_smt.case_161 x_a0, EoCases.__eo_to_smt.case_162 x_a0, EoCases.__eo_to_smt.case_163 x_a0, EoCases.__eo_to_smt.case_164 x_a0, EoCases.__eo_to_smt.case_165 x_a0, EoCases.__eo_to_smt.case_166 x_a0, EoCases.__eo_to_smt.case_167 x_a0, EoCases.__eo_to_smt.case_168 x_a0, EoCases.__eo_to_smt.case_169 x_a0, EoCases.__eo_to_smt.case_170 x_a0, EoCases.__eo_to_smt.case_171 x_a0, EoCases.__eo_to_smt.case_172 x_a0, EoCases.__eo_to_smt.case_173 x_a0, EoCases.__eo_to_smt.case_174 x_a0, EoCases.__eo_to_smt.case_175 x_a0, EoCases.__eo_to_smt.case_176 x_a0, EoCases.__eo_to_smt.case_177 x_a0, EoCases.__eo_to_smt.case_178 x_a0, EoCases.__eo_to_smt.case_179 x_a0, EoCases.__eo_to_smt.case_180 x_a0, EoCases.__eo_to_smt.case_181 x_a0, EoCases.__eo_to_smt.case_182 x_a0] = [EoCases.__eo_to_smt.case_128 x_a0, EoCases.__eo_to_smt.case_129 x_a0, EoCases.__eo_to_smt.case_130 x_a0, EoCases.__eo_to_smt.case_131 x_a0, EoCases.__eo_to_smt.case_132 x_a0, EoCases.__eo_to_smt.case_133 x_a0, EoCases.__eo_to_smt.case_134 x_a0, EoCases.__eo_to_smt.case_135 x_a0, EoCases.__eo_to_smt.case_136 x_a0, EoCases.__eo_to_smt.case_137 x_a0, EoCases.__eo_to_smt.case_138 x_a0, EoCases.__eo_to_smt.case_139 x_a0, EoCases.__eo_to_smt.case_140 x_a0, EoCases.__eo_to_smt.case_141 x_a0, EoCases.__eo_to_smt.case_142 x_a0, EoCases.__eo_to_smt.case_143 x_a0, EoCases.__eo_to_smt.case_144 x_a0, EoCases.__eo_to_smt.case_145 x_a0, EoCases.__eo_to_smt.case_146 x_a0, EoCases.__eo_to_smt.case_147 x_a0, EoCases.__eo_to_smt.case_148 x_a0, EoCases.__eo_to_smt.case_149 x_a0, EoCases.__eo_to_smt.case_150 x_a0, EoCases.__eo_to_smt.case_151 x_a0, EoCases.__eo_to_smt.case_152 x_a0, EoCases.__eo_to_smt.case_153 x_a0, EoCases.__eo_to_smt.case_154 x_a0, EoCases.__eo_to_smt.case_155 x_a0, EoCases.__eo_to_smt.case_156 x_a0, EoCases.__eo_to_smt.case_157 x_a0, EoCases.__eo_to_smt.case_158 x_a0, EoCases.__eo_to_smt.case_159 x_a0] ++ [EoCases.__eo_to_smt.case_160 x_a0, EoCases.__eo_to_smt.case_161 x_a0, EoCases.__eo_to_smt.case_162 x_a0, EoCases.__eo_to_smt.case_163 x_a0, EoCases.__eo_to_smt.case_164 x_a0, EoCases.__eo_to_smt.case_165 x_a0, EoCases.__eo_to_smt.case_166 x_a0, EoCases.__eo_to_smt.case_167 x_a0, EoCases.__eo_to_smt.case_168 x_a0, EoCases.__eo_to_smt.case_169 x_a0, EoCases.__eo_to_smt.case_170 x_a0, EoCases.__eo_to_smt.case_171 x_a0, EoCases.__eo_to_smt.case_172 x_a0, EoCases.__eo_to_smt.case_173 x_a0, EoCases.__eo_to_smt.case_174 x_a0, EoCases.__eo_to_smt.case_175 x_a0] ++ [EoCases.__eo_to_smt.case_176 x_a0, EoCases.__eo_to_smt.case_177 x_a0, EoCases.__eo_to_smt.case_178 x_a0, EoCases.__eo_to_smt.case_179 x_a0, EoCases.__eo_to_smt.case_180 x_a0, EoCases.__eo_to_smt.case_181 x_a0, EoCases.__eo_to_smt.case_182 x_a0] from rfl)
    otherwise ⟨hl_160, hl_161, hl_162, hl_163, hl_164, hl_165, hl_166, hl_167, hl_168, hl_169, hl_170, hl_171, hl_172, hl_173, hl_174, hl_175⟩ using hl_128 hl_129 hl_130 hl_131 hl_132 hl_133 hl_134 hl_135 hl_136 hl_137 hl_138 hl_139 hl_140 hl_141 hl_142 hl_143 hl_144 hl_145 hl_146 hl_147 hl_148 hl_149 hl_150 hl_151 hl_152 hl_153 hl_154 hl_155 hl_156 hl_157 hl_158 hl_159
  group_step with cases_1_11_eo__24eo_5fto_5fsmt_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt.case_128 x_a0, EoCases.__eo_to_smt.case_129 x_a0, EoCases.__eo_to_smt.case_130 x_a0, EoCases.__eo_to_smt.case_131 x_a0, EoCases.__eo_to_smt.case_132 x_a0, EoCases.__eo_to_smt.case_133 x_a0, EoCases.__eo_to_smt.case_134 x_a0, EoCases.__eo_to_smt.case_135 x_a0, EoCases.__eo_to_smt.case_136 x_a0, EoCases.__eo_to_smt.case_137 x_a0, EoCases.__eo_to_smt.case_138 x_a0, EoCases.__eo_to_smt.case_139 x_a0, EoCases.__eo_to_smt.case_140 x_a0, EoCases.__eo_to_smt.case_141 x_a0, EoCases.__eo_to_smt.case_142 x_a0, EoCases.__eo_to_smt.case_143 x_a0, EoCases.__eo_to_smt.case_144 x_a0, EoCases.__eo_to_smt.case_145 x_a0, EoCases.__eo_to_smt.case_146 x_a0, EoCases.__eo_to_smt.case_147 x_a0, EoCases.__eo_to_smt.case_148 x_a0, EoCases.__eo_to_smt.case_149 x_a0, EoCases.__eo_to_smt.case_150 x_a0, EoCases.__eo_to_smt.case_151 x_a0, EoCases.__eo_to_smt.case_152 x_a0, EoCases.__eo_to_smt.case_153 x_a0, EoCases.__eo_to_smt.case_154 x_a0, EoCases.__eo_to_smt.case_155 x_a0, EoCases.__eo_to_smt.case_156 x_a0, EoCases.__eo_to_smt.case_157 x_a0, EoCases.__eo_to_smt.case_158 x_a0, EoCases.__eo_to_smt.case_159 x_a0, EoCases.__eo_to_smt.case_160 x_a0, EoCases.__eo_to_smt.case_161 x_a0, EoCases.__eo_to_smt.case_162 x_a0, EoCases.__eo_to_smt.case_163 x_a0, EoCases.__eo_to_smt.case_164 x_a0, EoCases.__eo_to_smt.case_165 x_a0, EoCases.__eo_to_smt.case_166 x_a0, EoCases.__eo_to_smt.case_167 x_a0, EoCases.__eo_to_smt.case_168 x_a0, EoCases.__eo_to_smt.case_169 x_a0, EoCases.__eo_to_smt.case_170 x_a0, EoCases.__eo_to_smt.case_171 x_a0, EoCases.__eo_to_smt.case_172 x_a0, EoCases.__eo_to_smt.case_173 x_a0, EoCases.__eo_to_smt.case_174 x_a0, EoCases.__eo_to_smt.case_175 x_a0, EoCases.__eo_to_smt.case_176 x_a0, EoCases.__eo_to_smt.case_177 x_a0, EoCases.__eo_to_smt.case_178 x_a0, EoCases.__eo_to_smt.case_179 x_a0, EoCases.__eo_to_smt.case_180 x_a0, EoCases.__eo_to_smt.case_181 x_a0, EoCases.__eo_to_smt.case_182 x_a0] = [EoCases.__eo_to_smt.case_128 x_a0, EoCases.__eo_to_smt.case_129 x_a0, EoCases.__eo_to_smt.case_130 x_a0, EoCases.__eo_to_smt.case_131 x_a0, EoCases.__eo_to_smt.case_132 x_a0, EoCases.__eo_to_smt.case_133 x_a0, EoCases.__eo_to_smt.case_134 x_a0, EoCases.__eo_to_smt.case_135 x_a0, EoCases.__eo_to_smt.case_136 x_a0, EoCases.__eo_to_smt.case_137 x_a0, EoCases.__eo_to_smt.case_138 x_a0, EoCases.__eo_to_smt.case_139 x_a0, EoCases.__eo_to_smt.case_140 x_a0, EoCases.__eo_to_smt.case_141 x_a0, EoCases.__eo_to_smt.case_142 x_a0, EoCases.__eo_to_smt.case_143 x_a0, EoCases.__eo_to_smt.case_144 x_a0, EoCases.__eo_to_smt.case_145 x_a0, EoCases.__eo_to_smt.case_146 x_a0, EoCases.__eo_to_smt.case_147 x_a0, EoCases.__eo_to_smt.case_148 x_a0, EoCases.__eo_to_smt.case_149 x_a0, EoCases.__eo_to_smt.case_150 x_a0, EoCases.__eo_to_smt.case_151 x_a0, EoCases.__eo_to_smt.case_152 x_a0, EoCases.__eo_to_smt.case_153 x_a0, EoCases.__eo_to_smt.case_154 x_a0, EoCases.__eo_to_smt.case_155 x_a0, EoCases.__eo_to_smt.case_156 x_a0, EoCases.__eo_to_smt.case_157 x_a0, EoCases.__eo_to_smt.case_158 x_a0, EoCases.__eo_to_smt.case_159 x_a0, EoCases.__eo_to_smt.case_160 x_a0, EoCases.__eo_to_smt.case_161 x_a0, EoCases.__eo_to_smt.case_162 x_a0, EoCases.__eo_to_smt.case_163 x_a0, EoCases.__eo_to_smt.case_164 x_a0, EoCases.__eo_to_smt.case_165 x_a0, EoCases.__eo_to_smt.case_166 x_a0, EoCases.__eo_to_smt.case_167 x_a0, EoCases.__eo_to_smt.case_168 x_a0, EoCases.__eo_to_smt.case_169 x_a0, EoCases.__eo_to_smt.case_170 x_a0, EoCases.__eo_to_smt.case_171 x_a0, EoCases.__eo_to_smt.case_172 x_a0, EoCases.__eo_to_smt.case_173 x_a0, EoCases.__eo_to_smt.case_174 x_a0, EoCases.__eo_to_smt.case_175 x_a0] ++ [EoCases.__eo_to_smt.case_176 x_a0, EoCases.__eo_to_smt.case_177 x_a0, EoCases.__eo_to_smt.case_178 x_a0, EoCases.__eo_to_smt.case_179 x_a0, EoCases.__eo_to_smt.case_180 x_a0, EoCases.__eo_to_smt.case_181 x_a0, EoCases.__eo_to_smt.case_182 x_a0] ++ [] from rfl)
    otherwise ⟨hl_176, hl_177, hl_178, hl_179, hl_180, hl_181, hl_182⟩ using hl_128 hl_129 hl_130 hl_131 hl_132 hl_133 hl_134 hl_135 hl_136 hl_137 hl_138 hl_139 hl_140 hl_141 hl_142 hl_143 hl_144 hl_145 hl_146 hl_147 hl_148 hl_149 hl_150 hl_151 hl_152 hl_153 hl_154 hl_155 hl_156 hl_157 hl_158 hl_159 hl_160 hl_161 hl_162 hl_163 hl_164 hl_165 hl_166 hl_167 hl_168 hl_169 hl_170 hl_171 hl_172 hl_173 hl_174 hl_175
  group_none hinv4 hG with ⟨hl_128, hl_129, hl_130, hl_131, hl_132, hl_133, hl_134, hl_135, hl_136, hl_137, hl_138, hl_139, hl_140, hl_141, hl_142, hl_143, hl_144, hl_145, hl_146, hl_147, hl_148, hl_149, hl_150, hl_151, hl_152, hl_153, hl_154, hl_155, hl_156, hl_157, hl_158, hl_159, hl_160, hl_161, hl_162, hl_163, hl_164, hl_165, hl_166, hl_167, hl_168, hl_169, hl_170, hl_171, hl_172, hl_173, hl_174, hl_175, hl_176, hl_177, hl_178, hl_179, hl_180, hl_181, hl_182⟩

/-- logos's `__eo_to_smt` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fto_5fsmt.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_to_smt x_a0 =
      (firstSome [EoCases.__eo_to_smt.case_0 x_a0, EoCases.__eo_to_smt.case_1 x_a0, EoCases.__eo_to_smt.case_2 x_a0, EoCases.__eo_to_smt.case_3 x_a0, EoCases.__eo_to_smt.case_4 x_a0, EoCases.__eo_to_smt.case_5 x_a0, EoCases.__eo_to_smt.case_6 x_a0, EoCases.__eo_to_smt.case_7 x_a0, EoCases.__eo_to_smt.case_8 x_a0, EoCases.__eo_to_smt.case_9 x_a0, EoCases.__eo_to_smt.case_10 x_a0, EoCases.__eo_to_smt.case_11 x_a0, EoCases.__eo_to_smt.case_12 x_a0, EoCases.__eo_to_smt.case_13 x_a0, EoCases.__eo_to_smt.case_14 x_a0, EoCases.__eo_to_smt.case_15 x_a0, EoCases.__eo_to_smt.case_16 x_a0, EoCases.__eo_to_smt.case_17 x_a0, EoCases.__eo_to_smt.case_18 x_a0, EoCases.__eo_to_smt.case_19 x_a0, EoCases.__eo_to_smt.case_20 x_a0, EoCases.__eo_to_smt.case_21 x_a0, EoCases.__eo_to_smt.case_22 x_a0, EoCases.__eo_to_smt.case_23 x_a0, EoCases.__eo_to_smt.case_24 x_a0, EoCases.__eo_to_smt.case_25 x_a0, EoCases.__eo_to_smt.case_26 x_a0, EoCases.__eo_to_smt.case_27 x_a0, EoCases.__eo_to_smt.case_28 x_a0, EoCases.__eo_to_smt.case_29 x_a0, EoCases.__eo_to_smt.case_30 x_a0, EoCases.__eo_to_smt.case_31 x_a0, EoCases.__eo_to_smt.case_32 x_a0, EoCases.__eo_to_smt.case_33 x_a0, EoCases.__eo_to_smt.case_34 x_a0, EoCases.__eo_to_smt.case_35 x_a0, EoCases.__eo_to_smt.case_36 x_a0, EoCases.__eo_to_smt.case_37 x_a0, EoCases.__eo_to_smt.case_38 x_a0, EoCases.__eo_to_smt.case_39 x_a0, EoCases.__eo_to_smt.case_40 x_a0, EoCases.__eo_to_smt.case_41 x_a0, EoCases.__eo_to_smt.case_42 x_a0, EoCases.__eo_to_smt.case_43 x_a0, EoCases.__eo_to_smt.case_44 x_a0, EoCases.__eo_to_smt.case_45 x_a0, EoCases.__eo_to_smt.case_46 x_a0, EoCases.__eo_to_smt.case_47 x_a0, EoCases.__eo_to_smt.case_48 x_a0, EoCases.__eo_to_smt.case_49 x_a0, EoCases.__eo_to_smt.case_50 x_a0, EoCases.__eo_to_smt.case_51 x_a0, EoCases.__eo_to_smt.case_52 x_a0, EoCases.__eo_to_smt.case_53 x_a0, EoCases.__eo_to_smt.case_54 x_a0, EoCases.__eo_to_smt.case_55 x_a0, EoCases.__eo_to_smt.case_56 x_a0, EoCases.__eo_to_smt.case_57 x_a0, EoCases.__eo_to_smt.case_58 x_a0, EoCases.__eo_to_smt.case_59 x_a0, EoCases.__eo_to_smt.case_60 x_a0, EoCases.__eo_to_smt.case_61 x_a0, EoCases.__eo_to_smt.case_62 x_a0, EoCases.__eo_to_smt.case_63 x_a0, EoCases.__eo_to_smt.case_64 x_a0, EoCases.__eo_to_smt.case_65 x_a0, EoCases.__eo_to_smt.case_66 x_a0, EoCases.__eo_to_smt.case_67 x_a0, EoCases.__eo_to_smt.case_68 x_a0, EoCases.__eo_to_smt.case_69 x_a0, EoCases.__eo_to_smt.case_70 x_a0, EoCases.__eo_to_smt.case_71 x_a0, EoCases.__eo_to_smt.case_72 x_a0, EoCases.__eo_to_smt.case_73 x_a0, EoCases.__eo_to_smt.case_74 x_a0, EoCases.__eo_to_smt.case_75 x_a0, EoCases.__eo_to_smt.case_76 x_a0, EoCases.__eo_to_smt.case_77 x_a0, EoCases.__eo_to_smt.case_78 x_a0, EoCases.__eo_to_smt.case_79 x_a0, EoCases.__eo_to_smt.case_80 x_a0, EoCases.__eo_to_smt.case_81 x_a0, EoCases.__eo_to_smt.case_82 x_a0, EoCases.__eo_to_smt.case_83 x_a0, EoCases.__eo_to_smt.case_84 x_a0, EoCases.__eo_to_smt.case_85 x_a0, EoCases.__eo_to_smt.case_86 x_a0, EoCases.__eo_to_smt.case_87 x_a0, EoCases.__eo_to_smt.case_88 x_a0, EoCases.__eo_to_smt.case_89 x_a0, EoCases.__eo_to_smt.case_90 x_a0, EoCases.__eo_to_smt.case_91 x_a0, EoCases.__eo_to_smt.case_92 x_a0, EoCases.__eo_to_smt.case_93 x_a0, EoCases.__eo_to_smt.case_94 x_a0, EoCases.__eo_to_smt.case_95 x_a0, EoCases.__eo_to_smt.case_96 x_a0, EoCases.__eo_to_smt.case_97 x_a0, EoCases.__eo_to_smt.case_98 x_a0, EoCases.__eo_to_smt.case_99 x_a0, EoCases.__eo_to_smt.case_100 x_a0, EoCases.__eo_to_smt.case_101 x_a0, EoCases.__eo_to_smt.case_102 x_a0, EoCases.__eo_to_smt.case_103 x_a0, EoCases.__eo_to_smt.case_104 x_a0, EoCases.__eo_to_smt.case_105 x_a0, EoCases.__eo_to_smt.case_106 x_a0, EoCases.__eo_to_smt.case_107 x_a0, EoCases.__eo_to_smt.case_108 x_a0, EoCases.__eo_to_smt.case_109 x_a0, EoCases.__eo_to_smt.case_110 x_a0, EoCases.__eo_to_smt.case_111 x_a0, EoCases.__eo_to_smt.case_112 x_a0, EoCases.__eo_to_smt.case_113 x_a0, EoCases.__eo_to_smt.case_114 x_a0, EoCases.__eo_to_smt.case_115 x_a0, EoCases.__eo_to_smt.case_116 x_a0, EoCases.__eo_to_smt.case_117 x_a0, EoCases.__eo_to_smt.case_118 x_a0, EoCases.__eo_to_smt.case_119 x_a0, EoCases.__eo_to_smt.case_120 x_a0, EoCases.__eo_to_smt.case_121 x_a0, EoCases.__eo_to_smt.case_122 x_a0, EoCases.__eo_to_smt.case_123 x_a0, EoCases.__eo_to_smt.case_124 x_a0, EoCases.__eo_to_smt.case_125 x_a0, EoCases.__eo_to_smt.case_126 x_a0, EoCases.__eo_to_smt.case_127 x_a0, EoCases.__eo_to_smt.case_128 x_a0, EoCases.__eo_to_smt.case_129 x_a0, EoCases.__eo_to_smt.case_130 x_a0, EoCases.__eo_to_smt.case_131 x_a0, EoCases.__eo_to_smt.case_132 x_a0, EoCases.__eo_to_smt.case_133 x_a0, EoCases.__eo_to_smt.case_134 x_a0, EoCases.__eo_to_smt.case_135 x_a0, EoCases.__eo_to_smt.case_136 x_a0, EoCases.__eo_to_smt.case_137 x_a0, EoCases.__eo_to_smt.case_138 x_a0, EoCases.__eo_to_smt.case_139 x_a0, EoCases.__eo_to_smt.case_140 x_a0, EoCases.__eo_to_smt.case_141 x_a0, EoCases.__eo_to_smt.case_142 x_a0, EoCases.__eo_to_smt.case_143 x_a0, EoCases.__eo_to_smt.case_144 x_a0, EoCases.__eo_to_smt.case_145 x_a0, EoCases.__eo_to_smt.case_146 x_a0, EoCases.__eo_to_smt.case_147 x_a0, EoCases.__eo_to_smt.case_148 x_a0, EoCases.__eo_to_smt.case_149 x_a0, EoCases.__eo_to_smt.case_150 x_a0, EoCases.__eo_to_smt.case_151 x_a0, EoCases.__eo_to_smt.case_152 x_a0, EoCases.__eo_to_smt.case_153 x_a0, EoCases.__eo_to_smt.case_154 x_a0, EoCases.__eo_to_smt.case_155 x_a0, EoCases.__eo_to_smt.case_156 x_a0, EoCases.__eo_to_smt.case_157 x_a0, EoCases.__eo_to_smt.case_158 x_a0, EoCases.__eo_to_smt.case_159 x_a0, EoCases.__eo_to_smt.case_160 x_a0, EoCases.__eo_to_smt.case_161 x_a0, EoCases.__eo_to_smt.case_162 x_a0, EoCases.__eo_to_smt.case_163 x_a0, EoCases.__eo_to_smt.case_164 x_a0, EoCases.__eo_to_smt.case_165 x_a0, EoCases.__eo_to_smt.case_166 x_a0, EoCases.__eo_to_smt.case_167 x_a0, EoCases.__eo_to_smt.case_168 x_a0, EoCases.__eo_to_smt.case_169 x_a0, EoCases.__eo_to_smt.case_170 x_a0, EoCases.__eo_to_smt.case_171 x_a0, EoCases.__eo_to_smt.case_172 x_a0, EoCases.__eo_to_smt.case_173 x_a0, EoCases.__eo_to_smt.case_174 x_a0, EoCases.__eo_to_smt.case_175 x_a0, EoCases.__eo_to_smt.case_176 x_a0, EoCases.__eo_to_smt.case_177 x_a0, EoCases.__eo_to_smt.case_178 x_a0, EoCases.__eo_to_smt.case_179 x_a0, EoCases.__eo_to_smt.case_180 x_a0, EoCases.__eo_to_smt.case_181 x_a0, EoCases.__eo_to_smt.case_182 x_a0] default) := by
  logos_eq_large

end pathos_compiled_checker
