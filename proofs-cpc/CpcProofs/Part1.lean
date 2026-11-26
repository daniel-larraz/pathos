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

theorem case_0_eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) (hn_a4 : x_a4 ≠ Eo.Term.Stuck) :
    case_0_eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__bv_mk_bitblast_step_shr_rec.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _) (u3 : Term) (y3 : _) (u4 : Term) (y4 : _), arr.val = [u0, u1, u2, u3, u4] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧ Represents.rep s' u3 y3 ∧ Represents.rep s' u4 y4 ∧
          EoCases.__bv_mk_bitblast_step_shr_rec.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 = some (__bv_mk_bitblast_step_shr_rec y0 y1 y2 y3 y4)
      | core.result.Result.Ok none => EoCases.__bv_mk_bitblast_step_shr_rec.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec
  have hG := Store.Grows.refl s
  pat_same a3 a2 with h_a3 h_a2 using hinv else hinv hG in EoCases.__bv_mk_bitblast_step_shr_rec.case_0
  case_done hinv hG with h_a0 in EoCases.__bv_mk_bitblast_step_shr_rec.case_0 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4

theorem case_1_eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) (hn_a4 : x_a4 ≠ Eo.Term.Stuck) :
    case_1_eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__bv_mk_bitblast_step_shr_rec.case_1 x_a0 x_a1 x_a2 x_a3 x_a4 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _) (u3 : Term) (y3 : _) (u4 : Term) (y4 : _), arr.val = [u0, u1, u2, u3, u4] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧ Represents.rep s' u3 y3 ∧ Represents.rep s' u4 y4 ∧
          EoCases.__bv_mk_bitblast_step_shr_rec.case_1 x_a0 x_a1 x_a2 x_a3 x_a4 = some (__bv_mk_bitblast_step_shr_rec y0 y1 y2 y3 y4)
      | core.result.Result.Ok none => EoCases.__bv_mk_bitblast_step_shr_rec.case_1 x_a0 x_a1 x_a2 x_a3 x_a4 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec
  have hG := Store.Grows.refl s
  pat_unapply h_a1 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__bv_mk_bitblast_step_shr_rec.case_1
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__bv_mk_bitblast_step_shr_rec.case_1
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__bv_mk_bitblast_step_shr_rec.case_1
  step as ⟨e_v7, he_v7⟩
  store_step with Store.builtin_spec_is_z s1 e_v7 (by rw [he_v7]; rfl) h_a2 hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6
  have h_ite_v15 := (show if_1_eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec s2 v7 a2 ⦃ r s' => s'.Inv ∧ s2.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_1_eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s2
    rcases Store.boolean_value_term h_v7 with ⟨hx_8, hbv_8⟩ | ⟨hx_8, hbv_8⟩ | ⟨hx_8, hbv_8⟩
    · ite_branch hbv_8
      step as ⟨e_v8, he_v8⟩
      store_step with Store.builtin_spec_is_neg s2 e_v8 (by rw [he_v8]; rfl) h_a2 hinv2 h64 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
      have h_ite_v12 := (show if_0_eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec s3 v8 a2 ⦃ r s' => s'.Inv ∧ s3.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_0_eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s3
        rcases Store.boolean_value_term h_v8 with ⟨hx_9, hbv_9⟩ | ⟨hx_9, hbv_9⟩ | ⟨hx_9, hbv_9⟩
        · ite_branch hbv_9
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s3 0#u32 (0) (by scalar_tac) hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
          ite_done hinv4 hG with (eo_ite_true_rep _ hx_9 h_v9)
        · ite_branch hbv_9
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s3 2#u32 (2) (by scalar_tac) hinv3 h64 as ⟨v10, s4, hinv4, h_v10⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
          step as ⟨e_v11, he_v11⟩
          store_step with Store.builtin_spec_pow s4 e_v11 (by rw [he_v11]; rfl) h_v10 h_a2 hinv4 h64 as ⟨v11, s5, hinv5, h_v11⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v10
          ite_done hinv5 hG with (eo_ite_false_rep _ hx_9 h_v11)
        · ite_branch hbv_9
          ite_stuck hinv3 hG with hx_9)
      store_step with h_ite_v12 as ⟨v12, s4, hinv4, h_v12⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
      ite_done hinv4 hG with (eo_ite_true_rep _ hx_8 h_v12)
    · ite_branch hbv_8
      step as ⟨e_v13, he_v13⟩
      store_step with CtorSpec.eo_int_2epow2.construct s2 e_v13 (by rw [he_v13]; exact empty_args) hinv2 h64 as ⟨v13, s3, hinv3, h_v13⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
      store_step with Store.apply_rep s3 v13 a2 _ _ hinv3 h64 h_v13 h_a2 (by ns_tac) (by ns_tac) as ⟨v14, s4, hinv4, h_v14⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v13
      ite_done hinv4 hG with (eo_ite_false_rep _ hx_8 h_v14)
    · ite_branch hbv_8
      ite_stuck hinv2 hG with hx_8)
  store_step with h_ite_v15 as ⟨v15, s3, hinv3, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec_5fstep s3 a0 a0 v15 v5 a4 _ _ _ _ _ hinv3 h64 (hG.rem hrem) h_a0 h_a0 h_v15 h_v5 h_a4 as ⟨v16, s4, hinv4, h_v16⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v15
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s4 1#u32 (1) (by scalar_tac) hinv4 h64 as ⟨v17, s5, hinv5, h_v17⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v15 h_v16
  step as ⟨e_v18, he_v18⟩
  store_step with Store.builtin_spec_add s5 e_v18 (by rw [he_v18]; rfl) h_a2 h_v17 hinv5 h64 as ⟨v18, s6, hinv6, h_v18⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v15 h_v16 h_v17
  case_again hinv6 hG with h_v16 h_v2 h_v18 h_a3 h_a4 in EoCases.__bv_mk_bitblast_step_shr_rec.case_1 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_v1 hn_v2 hn_v4 hn_v5

/-- logos's `__bv_mk_bitblast_step_shr_rec` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) (hw_a4 : Valid.valid x_a4) :
    __bv_mk_bitblast_step_shr_rec x_a0 x_a1 x_a2 x_a3 x_a4 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else if x_a4 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__bv_mk_bitblast_step_shr_rec.case_0 x_a0 x_a1 x_a2 x_a3 x_a4, EoCases.__bv_mk_bitblast_step_shr_rec.case_1 x_a0 x_a1 x_a2 x_a3 x_a4] HasStuck.stuck) := by
  conv => lhs; unfold __bv_mk_bitblast_step_shr_rec
  unfold EoCases.__bv_mk_bitblast_step_shr_rec.case_0 EoCases.__bv_mk_bitblast_step_shr_rec.case_1
  try unfold Eo.__eo_l_1___bv_mk_bitblast_step_shr_rec
  logos_eq_deep

theorem step_eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) :
    step_eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (Next.Done t) => Represents.rep s' t (__bv_mk_bitblast_step_shr_rec x_a0 x_a1 x_a2 x_a3 x_a4)
      | core.result.Result.Ok (Next.Again arr) =>
        s'.budget < s.budget ∧ ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _) (u3 : Term) (y3 : _) (u4 : Term) (y4 : _), arr.val = [u0, u1, u2, u3, u4] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧ Represents.rep s' u3 y3 ∧ Represents.rep s' u4 y4 ∧
          __bv_mk_bitblast_step_shr_rec x_a0 x_a1 x_a2 x_a3 x_a4 = __bv_mk_bitblast_step_shr_rec y0 y1 y2 y3 y4
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec.rust_eq x_a0 x_a1 x_a2 x_a3 x_a4 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3) (by valid_tac hinv h_a4)]
  unfold step_eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec
  have hG := Store.Grows.refl s
  tick_step as ⟨s1, hinv1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4
  stuck_check h_a0 : x_a0 as hn_a0 else hinv1 hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv1 hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv1 hG
  stuck_check h_a3 : x_a3 as hn_a3 else hinv1 hG
  stuck_check h_a4 : x_a4 as hn_a4 else hinv1 hG
  round_step with case_0_eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec_spec n ih s1 a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 h_a3 h_a4 hn_a0 hn_a1 hn_a2 hn_a3 hn_a4
    as ⟨s2, hinv2, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 hbud using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4
  round_step with case_1_eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec_spec n ih s2 a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv2 h64 (hG.rem hrem) h_a0 h_a1 h_a2 h_a3 h_a4 hn_a0 hn_a1 hn_a2 hn_a3 hn_a4
    as ⟨s3, hinv3, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 hbud using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hc0
  round_stuck hinv3 hG using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hc0 hc1 in EoCases.__bv_mk_bitblast_step_shr_rec.case_0 EoCases.__bv_mk_bitblast_step_shr_rec.case_1

theorem body_eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) :
    body_eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__bv_mk_bitblast_step_shr_rec x_a0 x_a1 x_a2 x_a3 x_a4)
      | core.result.Result.Err _ => True ⦄div := by
  refine (?_ : ∀ (k : Nat) (a0 a1 a2 a3 a4 : Term) (s : Store) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _), s.budget ≤ k → s.Inv → s.remaining ≤ n →
      Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 → Represents.rep s a4 x_a4 →
      body_eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__bv_mk_bitblast_step_shr_rec x_a0 x_a1 x_a2 x_a3 x_a4)
      | core.result.Result.Err _ => True ⦄div) s.budget a0 a1 a2 a3 a4 s x_a0 x_a1 x_a2 x_a3 x_a4 le_rfl hinv hrem h_a0 h_a1 h_a2 h_a3 h_a4
  intro k
  refine Nat.strong_induction_on k ?_
  intro k ihl a0 a1 a2 a3 a4 s x_a0 x_a1 x_a2 x_a3 x_a4 hk hinv hrem h_a0 h_a1 h_a2 h_a3 h_a4
  unfold body_eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec body_eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec_loop
  step with step_eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec_spec n ih s a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 as ⟨r, s1, hinv1, hg1, hr⟩
  cases r with
  | Err e => simp only [WP.dspec_ok, WP.uncurry'_pair]; exact ⟨hinv1, hg1, trivial⟩
  | Ok nx =>
    cases nx with
    | Done value =>
      simp only [WP.dspec_ok, WP.uncurry'_pair]
      exact ⟨hinv1, hg1, hr⟩
    | Again next =>
      obtain ⟨hlt, u0, y0, u1, y1, u2, y2, u3, y3, u4, y4, hnext, hrep0, hrep1, hrep2, hrep3, hrep4, heq⟩ := hr
      simp only
      have hlen : next.length = 5 := by simp [Array.length, hnext]
      step as ⟨b0, hb0⟩
      obtain rfl : b0 = u0 := by simp [hb0, hnext]
      step as ⟨b1, hb1⟩
      obtain rfl : b1 = u1 := by simp [hb1, hnext]
      step as ⟨b2, hb2⟩
      obtain rfl : b2 = u2 := by simp [hb2, hnext]
      step as ⟨b3, hb3⟩
      obtain rfl : b3 = u3 := by simp [hb3, hnext]
      step as ⟨b4, hb4⟩
      obtain rfl : b4 = u4 := by simp [hb4, hnext]
      have hrec := ihl s1.budget (by omega) b0 b1 b2 b3 b4 s1 y0 y1 y2 y3 y4 le_rfl hinv1 (hg1.rem hrem)  hrep0  hrep1  hrep2  hrep3  hrep4
      unfold body_eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec at hrec
      apply WP.dspec_mono hrec
      loop_close hg1 heq

theorem eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec.Spec n := by
  intro s a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4
  unfold eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 43#u32 _ [a0, a1, a2, a3, a4] rfl
    (fun s1 => body_eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec s1 a0 a1 a2 a3 a4) (fun s' t => Represents.rep s' t (__bv_mk_bitblast_step_shr_rec x_a0 x_a1 x_a2 x_a3 x_a4))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, b2, b3, b4, y0, y1, y2, y3, y4, hargs, hb0, hb1, hb2, hb3, hb4, hr⟩ := ProgramSem.of_43 hsem
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
      exact ProgramSem.to_43 ⟨a0, a1, a2, a3, a4, x_a0, x_a1, x_a2, x_a3, x_a4, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, Rep.mono hpre h_a2, Rep.mono hpre h_a3, Rep.mono hpre h_a4, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec_spec m (ih m hm) s1 a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn) (by congr_one h_a4 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec_5fstep_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) (hn_a4 : x_a4 ≠ Eo.Term.Stuck) :
    case_0_eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec_5fstep s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__bv_mk_bitblast_step_shr_rec_step.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _) (u3 : Term) (y3 : _) (u4 : Term) (y4 : _), arr.val = [u0, u1, u2, u3, u4] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧ Represents.rep s' u3 y3 ∧ Represents.rep s' u4 y4 ∧
          EoCases.__bv_mk_bitblast_step_shr_rec_step.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 = some (__bv_mk_bitblast_step_shr_rec_step y0 y1 y2 y3 y4)
      | core.result.Result.Ok none => EoCases.__bv_mk_bitblast_step_shr_rec_step.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec_5fstep
  have hG := Store.Grows.refl s
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__bv_mk_bitblast_step_shr_rec_step.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s1 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__bv_mk_bitblast_step_shr_rec_step.case_0 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4

theorem case_1_eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec_5fstep_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) (hn_a4 : x_a4 ≠ Eo.Term.Stuck) :
    case_1_eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec_5fstep s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__bv_mk_bitblast_step_shr_rec_step.case_1 x_a0 x_a1 x_a2 x_a3 x_a4 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _) (u3 : Term) (y3 : _) (u4 : Term) (y4 : _), arr.val = [u0, u1, u2, u3, u4] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧ Represents.rep s' u3 y3 ∧ Represents.rep s' u4 y4 ∧
          EoCases.__bv_mk_bitblast_step_shr_rec_step.case_1 x_a0 x_a1 x_a2 x_a3 x_a4 = some (__bv_mk_bitblast_step_shr_rec_step y0 y1 y2 y3 y4)
      | core.result.Result.Ok none => EoCases.__bv_mk_bitblast_step_shr_rec_step.case_1 x_a0 x_a1 x_a2 x_a3 x_a4 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec_5fstep more_0_eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec_5fstep
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__bv_mk_bitblast_step_shr_rec_step.case_1
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__bv_mk_bitblast_step_shr_rec_step.case_1
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__bv_mk_bitblast_step_shr_rec_step.case_1
  pat_unapply h_a1 as ⟨v8, v9, x_v8, x_v9, h_v8, h_v9, hn_v8, hn_v9⟩ using hinv1 else hinv1 hG in EoCases.__bv_mk_bitblast_step_shr_rec_step.case_1
  pat_unapply h_v8 as ⟨v11, v12, x_v11, x_v12, h_v11, h_v12, hn_v11, hn_v12⟩ using hinv1 else hinv1 hG in EoCases.__bv_mk_bitblast_step_shr_rec_step.case_1
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s1 e_v13 (by rw [he_v13]; exact empty_args) hinv1 h64 as ⟨v13, s2, hinv2, h_v13⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12
  pat_same v11 v13 with h_v11 h_v13 using hinv2 else hinv2 hG in EoCases.__bv_mk_bitblast_step_shr_rec_step.case_1
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s2 0#u32 (0) (by scalar_tac) hinv2 h64 as ⟨v14, s3, hinv3, h_v14⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13
  pat_same a2 v14 with h_a2 h_v14 using hinv3 else hinv3 hG in EoCases.__bv_mk_bitblast_step_shr_rec_step.case_1
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s3 e_v15 (by rw [he_v15]; exact empty_args) hinv3 h64 as ⟨v15, s4, hinv4, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14
  step as ⟨e_v16, he_v16⟩
  store_step with CtorSpec.eo_ite.construct s4 e_v16 (by rw [he_v16]; exact empty_args) hinv4 h64 as ⟨v16, s5, hinv5, h_v16⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15
  step as ⟨e_v17, he_v17⟩
  store_step with CtorSpec.eo_not.construct s5 e_v17 (by rw [he_v17]; exact empty_args) hinv5 h64 as ⟨v17, s6, hinv6, h_v17⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16
  store_step with Store.apply_rep s6 v17 a3 _ _ hinv6 h64 h_v17 h_a3 (by ns_tac) (by ns_tac) as ⟨v18, s7, hinv7, h_v18⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17
  store_step with Store.apply_rep s7 v16 v18 _ _ hinv7 h64 h_v16 h_v18 (by ns_tac) (by ns_tac) as ⟨v19, s8, hinv8, h_v19⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18
  store_step with Store.apply_rep s8 v19 v5 _ _ hinv8 h64 h_v19 h_v5 (by ns_tac) (by ns_tac) as ⟨v20, s9, hinv9, h_v20⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19
  store_step with Store.apply_rep s9 v20 v12 _ _ hinv9 h64 h_v20 h_v12 (by ns_tac) (by ns_tac) as ⟨v21, s10, hinv10, h_v21⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20
  store_step with Store.apply_rep s10 v15 v21 _ _ hinv10 h64 h_v15 h_v21 (by ns_tac) (by ns_tac) as ⟨v22, s11, hinv11, h_v22⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s11 0#u32 (0) (by scalar_tac) hinv11 h64 as ⟨v23, s12, hinv12, h_v23⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22
  store_step with ih.eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec_5fstep s12 v2 v9 v23 a3 a4 _ _ _ _ _ hinv12 h64 (hG.rem hrem) h_v2 h_v9 h_v23 h_a3 h_a4 as ⟨v24, s13, hinv13, h_v24⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23
  store_step with Store.apply_mk_rep s13 v22 v24 _ _ hinv13 h64 h_v22 h_v24 as ⟨v25, s14, hinv14, h_v25⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24
  case_done hinv14 hG with h_v25 in EoCases.__bv_mk_bitblast_step_shr_rec_step.case_1 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_v1 hn_v2 hn_v4 hn_v5 hn_v8 hn_v9 hn_v11 hn_v12

theorem case_2_eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec_5fstep_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) (hn_a4 : x_a4 ≠ Eo.Term.Stuck) :
    case_2_eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec_5fstep s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__bv_mk_bitblast_step_shr_rec_step.case_2 x_a0 x_a1 x_a2 x_a3 x_a4 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _) (u3 : Term) (y3 : _) (u4 : Term) (y4 : _), arr.val = [u0, u1, u2, u3, u4] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧ Represents.rep s' u3 y3 ∧ Represents.rep s' u4 y4 ∧
          EoCases.__bv_mk_bitblast_step_shr_rec_step.case_2 x_a0 x_a1 x_a2 x_a3 x_a4 = some (__bv_mk_bitblast_step_shr_rec_step y0 y1 y2 y3 y4)
      | core.result.Result.Ok none => EoCases.__bv_mk_bitblast_step_shr_rec_step.case_2 x_a0 x_a1 x_a2 x_a3 x_a4 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec_5fstep more_1_eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec_5fstep
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__bv_mk_bitblast_step_shr_rec_step.case_2
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__bv_mk_bitblast_step_shr_rec_step.case_2
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__bv_mk_bitblast_step_shr_rec_step.case_2
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s1 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6
  pat_same a1 v7 with h_a1 h_v7 using hinv2 else hinv2 hG in EoCases.__bv_mk_bitblast_step_shr_rec_step.case_2
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s2 0#u32 (0) (by scalar_tac) hinv2 h64 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  pat_same a2 v8 with h_a2 h_v8 using hinv3 else hinv3 hG in EoCases.__bv_mk_bitblast_step_shr_rec_step.case_2
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s3 e_v9 (by rw [he_v9]; exact empty_args) hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo_ite.construct s4 e_v10 (by rw [he_v10]; exact empty_args) hinv4 h64 as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  store_step with Store.apply_rep s5 v10 a3 _ _ hinv5 h64 h_v10 h_a3 (by ns_tac) (by ns_tac) as ⟨v11, s6, hinv6, h_v11⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
  store_step with Store.apply_rep s6 v11 a4 _ _ hinv6 h64 h_v11 h_a4 (by ns_tac) (by ns_tac) as ⟨v12, s7, hinv7, h_v12⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11
  store_step with Store.apply_rep s7 v12 v5 _ _ hinv7 h64 h_v12 h_v5 (by ns_tac) (by ns_tac) as ⟨v13, s8, hinv8, h_v13⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
  store_step with Store.apply_rep s8 v9 v13 _ _ hinv8 h64 h_v9 h_v13 (by ns_tac) (by ns_tac) as ⟨v14, s9, hinv9, h_v14⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s9 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv9 h64 as ⟨v15, s10, hinv10, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s10 0#u32 (0) (by scalar_tac) hinv10 h64 as ⟨v16, s11, hinv11, h_v16⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15
  store_step with ih.eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec_5fstep s11 v2 v15 v16 a3 a4 _ _ _ _ _ hinv11 h64 (hG.rem hrem) h_v2 h_v15 h_v16 h_a3 h_a4 as ⟨v17, s12, hinv12, h_v17⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16
  store_step with Store.apply_mk_rep s12 v14 v17 _ _ hinv12 h64 h_v14 h_v17 as ⟨v18, s13, hinv13, h_v18⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17
  case_done hinv13 hG with h_v18 in EoCases.__bv_mk_bitblast_step_shr_rec_step.case_2 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_3_eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec_5fstep_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) (hn_a4 : x_a4 ≠ Eo.Term.Stuck) :
    case_3_eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec_5fstep s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__bv_mk_bitblast_step_shr_rec_step.case_3 x_a0 x_a1 x_a2 x_a3 x_a4 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _) (u3 : Term) (y3 : _) (u4 : Term) (y4 : _), arr.val = [u0, u1, u2, u3, u4] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧ Represents.rep s' u3 y3 ∧ Represents.rep s' u4 y4 ∧
          EoCases.__bv_mk_bitblast_step_shr_rec_step.case_3 x_a0 x_a1 x_a2 x_a3 x_a4 = some (__bv_mk_bitblast_step_shr_rec_step y0 y1 y2 y3 y4)
      | core.result.Result.Ok none => EoCases.__bv_mk_bitblast_step_shr_rec_step.case_3 x_a0 x_a1 x_a2 x_a3 x_a4 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_3_eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec_5fstep
  have hG := Store.Grows.refl s
  pat_unapply h_a1 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__bv_mk_bitblast_step_shr_rec_step.case_3
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__bv_mk_bitblast_step_shr_rec_step.case_3
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__bv_mk_bitblast_step_shr_rec_step.case_3
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_neg_u32_spec s1 1#u32 (-1) (by scalar_tac) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6
  step as ⟨e_v8, he_v8⟩
  store_step with Store.builtin_spec_add s2 e_v8 (by rw [he_v8]; rfl) h_a2 h_v7 hinv2 h64 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  case_again hinv3 hG with h_a0 h_v2 h_v8 h_a3 h_a4 in EoCases.__bv_mk_bitblast_step_shr_rec_step.case_3 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_v1 hn_v2 hn_v4 hn_v5

/-- logos's `__bv_mk_bitblast_step_shr_rec_step` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec_5fstep.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) (hw_a4 : Valid.valid x_a4) :
    __bv_mk_bitblast_step_shr_rec_step x_a0 x_a1 x_a2 x_a3 x_a4 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else if x_a4 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__bv_mk_bitblast_step_shr_rec_step.case_0 x_a0 x_a1 x_a2 x_a3 x_a4, EoCases.__bv_mk_bitblast_step_shr_rec_step.case_1 x_a0 x_a1 x_a2 x_a3 x_a4, EoCases.__bv_mk_bitblast_step_shr_rec_step.case_2 x_a0 x_a1 x_a2 x_a3 x_a4, EoCases.__bv_mk_bitblast_step_shr_rec_step.case_3 x_a0 x_a1 x_a2 x_a3 x_a4] HasStuck.stuck) := by
  conv => lhs; unfold __bv_mk_bitblast_step_shr_rec_step
  unfold EoCases.__bv_mk_bitblast_step_shr_rec_step.case_0 EoCases.__bv_mk_bitblast_step_shr_rec_step.case_1 EoCases.__bv_mk_bitblast_step_shr_rec_step.case_2 EoCases.__bv_mk_bitblast_step_shr_rec_step.case_3
  logos_eq

theorem step_eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec_5fstep_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) :
    step_eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec_5fstep s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (Next.Done t) => Represents.rep s' t (__bv_mk_bitblast_step_shr_rec_step x_a0 x_a1 x_a2 x_a3 x_a4)
      | core.result.Result.Ok (Next.Again arr) =>
        s'.budget < s.budget ∧ ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _) (u3 : Term) (y3 : _) (u4 : Term) (y4 : _), arr.val = [u0, u1, u2, u3, u4] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧ Represents.rep s' u3 y3 ∧ Represents.rep s' u4 y4 ∧
          __bv_mk_bitblast_step_shr_rec_step x_a0 x_a1 x_a2 x_a3 x_a4 = __bv_mk_bitblast_step_shr_rec_step y0 y1 y2 y3 y4
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec_5fstep.rust_eq x_a0 x_a1 x_a2 x_a3 x_a4 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3) (by valid_tac hinv h_a4)]
  unfold step_eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec_5fstep
  have hG := Store.Grows.refl s
  tick_step as ⟨s1, hinv1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4
  stuck_check h_a0 : x_a0 as hn_a0 else hinv1 hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv1 hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv1 hG
  stuck_check h_a3 : x_a3 as hn_a3 else hinv1 hG
  stuck_check h_a4 : x_a4 as hn_a4 else hinv1 hG
  round_step with case_0_eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec_5fstep_spec n ih s1 a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 h_a3 h_a4 hn_a0 hn_a1 hn_a2 hn_a3 hn_a4
    as ⟨s2, hinv2, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 hbud using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4
  round_step with case_1_eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec_5fstep_spec n ih s2 a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv2 h64 (hG.rem hrem) h_a0 h_a1 h_a2 h_a3 h_a4 hn_a0 hn_a1 hn_a2 hn_a3 hn_a4
    as ⟨s3, hinv3, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 hbud using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hc0
  round_step with case_2_eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec_5fstep_spec n ih s3 a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv3 h64 (hG.rem hrem) h_a0 h_a1 h_a2 h_a3 h_a4 hn_a0 hn_a1 hn_a2 hn_a3 hn_a4
    as ⟨s4, hinv4, hc2⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 hbud using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hc0 hc1
  round_step with case_3_eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec_5fstep_spec n ih s4 a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv4 h64 (hG.rem hrem) h_a0 h_a1 h_a2 h_a3 h_a4 hn_a0 hn_a1 hn_a2 hn_a3 hn_a4
    as ⟨s5, hinv5, hc3⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 hbud using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hc0 hc1 hc2
  round_stuck hinv5 hG using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hc0 hc1 hc2 hc3 in EoCases.__bv_mk_bitblast_step_shr_rec_step.case_0 EoCases.__bv_mk_bitblast_step_shr_rec_step.case_1 EoCases.__bv_mk_bitblast_step_shr_rec_step.case_2 EoCases.__bv_mk_bitblast_step_shr_rec_step.case_3

theorem body_eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec_5fstep_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) :
    body_eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec_5fstep s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__bv_mk_bitblast_step_shr_rec_step x_a0 x_a1 x_a2 x_a3 x_a4)
      | core.result.Result.Err _ => True ⦄div := by
  refine (?_ : ∀ (k : Nat) (a0 a1 a2 a3 a4 : Term) (s : Store) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _), s.budget ≤ k → s.Inv → s.remaining ≤ n →
      Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 → Represents.rep s a4 x_a4 →
      body_eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec_5fstep s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__bv_mk_bitblast_step_shr_rec_step x_a0 x_a1 x_a2 x_a3 x_a4)
      | core.result.Result.Err _ => True ⦄div) s.budget a0 a1 a2 a3 a4 s x_a0 x_a1 x_a2 x_a3 x_a4 le_rfl hinv hrem h_a0 h_a1 h_a2 h_a3 h_a4
  intro k
  refine Nat.strong_induction_on k ?_
  intro k ihl a0 a1 a2 a3 a4 s x_a0 x_a1 x_a2 x_a3 x_a4 hk hinv hrem h_a0 h_a1 h_a2 h_a3 h_a4
  unfold body_eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec_5fstep body_eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec_5fstep_loop
  step with step_eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec_5fstep_spec n ih s a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 as ⟨r, s1, hinv1, hg1, hr⟩
  cases r with
  | Err e => simp only [WP.dspec_ok, WP.uncurry'_pair]; exact ⟨hinv1, hg1, trivial⟩
  | Ok nx =>
    cases nx with
    | Done value =>
      simp only [WP.dspec_ok, WP.uncurry'_pair]
      exact ⟨hinv1, hg1, hr⟩
    | Again next =>
      obtain ⟨hlt, u0, y0, u1, y1, u2, y2, u3, y3, u4, y4, hnext, hrep0, hrep1, hrep2, hrep3, hrep4, heq⟩ := hr
      simp only
      have hlen : next.length = 5 := by simp [Array.length, hnext]
      step as ⟨b0, hb0⟩
      obtain rfl : b0 = u0 := by simp [hb0, hnext]
      step as ⟨b1, hb1⟩
      obtain rfl : b1 = u1 := by simp [hb1, hnext]
      step as ⟨b2, hb2⟩
      obtain rfl : b2 = u2 := by simp [hb2, hnext]
      step as ⟨b3, hb3⟩
      obtain rfl : b3 = u3 := by simp [hb3, hnext]
      step as ⟨b4, hb4⟩
      obtain rfl : b4 = u4 := by simp [hb4, hnext]
      have hrec := ihl s1.budget (by omega) b0 b1 b2 b3 b4 s1 y0 y1 y2 y3 y4 le_rfl hinv1 (hg1.rem hrem)  hrep0  hrep1  hrep2  hrep3  hrep4
      unfold body_eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec_5fstep at hrec
      apply WP.dspec_mono hrec
      loop_close hg1 heq

theorem eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec_5fstep_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec_5fstep.Spec n := by
  intro s a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4
  unfold eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec_5fstep
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 44#u32 _ [a0, a1, a2, a3, a4] rfl
    (fun s1 => body_eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec_5fstep s1 a0 a1 a2 a3 a4) (fun s' t => Represents.rep s' t (__bv_mk_bitblast_step_shr_rec_step x_a0 x_a1 x_a2 x_a3 x_a4))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, b2, b3, b4, y0, y1, y2, y3, y4, hargs, hb0, hb1, hb2, hb3, hb4, hr⟩ := ProgramSem.of_44 hsem
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
      exact ProgramSem.to_44 ⟨a0, a1, a2, a3, a4, x_a0, x_a1, x_a2, x_a3, x_a4, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, Rep.mono hpre h_a2, Rep.mono hpre h_a3, Rep.mono hpre h_a4, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24bv_5fmk_5fbitblast_5fstep_5fshr_5frec_5fstep_spec m (ih m hm) s1 a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn) (by congr_one h_a4 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24bv_5fmk_5fbitblast_5fstep_5fvar_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24bv_5fmk_5fbitblast_5fstep_5fvar_5frec s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__bv_mk_bitblast_step_var_rec.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__bv_mk_bitblast_step_var_rec.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24bv_5fmk_5fbitblast_5fstep_5fvar_5frec
  have hG := Store.Grows.refl s
  pat_unapply h_a1 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__bv_mk_bitblast_step_var_rec.case_0
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__40_40TypedList_2enil.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__bv_mk_bitblast_step_var_rec.case_0
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo_Int.construct s1 e_v4 (by rw [he_v4]; exact empty_args) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3
  pat_same v2 v4 with h_v2 h_v4 using hinv2 else hinv2 hG in EoCases.__bv_mk_bitblast_step_var_rec.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s2 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__bv_mk_bitblast_step_var_rec.case_0 using hn_a0 hn_a1 hn_v1 hn_v2

theorem case_1_eo__24bv_5fmk_5fbitblast_5fstep_5fvar_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_1_eo__24bv_5fmk_5fbitblast_5fstep_5fvar_5frec s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__bv_mk_bitblast_step_var_rec.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__bv_mk_bitblast_step_var_rec.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24bv_5fmk_5fbitblast_5fstep_5fvar_5frec
  have hG := Store.Grows.refl s
  pat_unapply h_a1 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__bv_mk_bitblast_step_var_rec.case_1
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__bv_mk_bitblast_step_var_rec.case_1
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__40_40TypedList_2econs.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__bv_mk_bitblast_step_var_rec.case_1
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s1 e_v7 (by rw [he_v7]; exact empty_args) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__40bit.construct s2 e_v8 (by rw [he_v8]; rfl) h_v5 hinv2 h64 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with Store.apply_rep s3 v8 a0 _ _ hinv3 h64 h_v8 h_a0 (by ns_tac) (by ns_tac) as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  store_step with Store.apply_rep s4 v7 v9 _ _ hinv4 h64 h_v7 h_v9 (by ns_tac) (by ns_tac) as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  store_step with ih.eo__24bv_5fmk_5fbitblast_5fstep_5fvar_5frec s5 a0 v2 _ _ hinv5 h64 (hG.rem hrem) h_a0 h_v2 as ⟨v11, s6, hinv6, h_v11⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
  store_step with Store.apply_mk_rep s6 v10 v11 _ _ hinv6 h64 h_v10 h_v11 as ⟨v12, s7, hinv7, h_v12⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11
  case_done hinv7 hG with h_v12 in EoCases.__bv_mk_bitblast_step_var_rec.case_1 using hn_a0 hn_a1 hn_v1 hn_v2 hn_v4 hn_v5

/-- logos's `__bv_mk_bitblast_step_var_rec` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24bv_5fmk_5fbitblast_5fstep_5fvar_5frec.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __bv_mk_bitblast_step_var_rec x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__bv_mk_bitblast_step_var_rec.case_0 x_a0 x_a1, EoCases.__bv_mk_bitblast_step_var_rec.case_1 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __bv_mk_bitblast_step_var_rec
  unfold EoCases.__bv_mk_bitblast_step_var_rec.case_0 EoCases.__bv_mk_bitblast_step_var_rec.case_1
  logos_eq

theorem body_eo__24bv_5fmk_5fbitblast_5fstep_5fvar_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24bv_5fmk_5fbitblast_5fstep_5fvar_5frec s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__bv_mk_bitblast_step_var_rec x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24bv_5fmk_5fbitblast_5fstep_5fvar_5frec.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24bv_5fmk_5fbitblast_5fstep_5fvar_5frec
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24bv_5fmk_5fbitblast_5fstep_5fvar_5frec_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  case_step with case_1_eo__24bv_5fmk_5fbitblast_5fstep_5fvar_5frec_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1 hc0
  body_stuck hinv2 hG using hn_a0 hn_a1 hc0 hc1 in EoCases.__bv_mk_bitblast_step_var_rec.case_0 EoCases.__bv_mk_bitblast_step_var_rec.case_1

theorem eo__24bv_5fmk_5fbitblast_5fstep_5fvar_5frec_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24bv_5fmk_5fbitblast_5fstep_5fvar_5frec.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24bv_5fmk_5fbitblast_5fstep_5fvar_5frec
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 45#u32 _ [a0, a1] rfl
    (fun s1 => body_eo__24bv_5fmk_5fbitblast_5fstep_5fvar_5frec s1 a0 a1) (fun s' t => Represents.rep s' t (__bv_mk_bitblast_step_var_rec x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, y0, y1, hargs, hb0, hb1, hr⟩ := ProgramSem.of_45 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_45 ⟨a0, a1, x_a0, x_a1, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24bv_5fmk_5fbitblast_5fstep_5fvar_5frec_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24bv_5fmk_5fbitwise_5fslicing_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 a6 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) (h_a6 : Represents.rep s a6 x_a6) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) (hn_a4 : x_a4 ≠ Eo.Term.Stuck) (hn_a5 : x_a5 ≠ Eo.Term.Stuck) (hn_a6 : x_a6 ≠ Eo.Term.Stuck) :
    case_0_eo__24bv_5fmk_5fbitwise_5fslicing_5frec s a0 a1 a2 a3 a4 a5 a6 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__bv_mk_bitwise_slicing_rec.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__bv_mk_bitwise_slicing_rec.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24bv_5fmk_5fbitwise_5fslicing_5frec more_0_eo__24bv_5fmk_5fbitwise_5fslicing_5frec
  have hG := Store.Grows.refl s
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6
  pat_same a3 v0 with h_a3 h_v0 using hinv1 else hinv1 hG in EoCases.__bv_mk_bitwise_slicing_rec.case_0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_concat.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s2 0#u32 (0) (by scalar_tac) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v0 h_v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_extract.construct s3 e_v3 (by rw [he_v3]; rfl) h_a5 h_v2 hinv3 h64 as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v3 a1 _ _ hinv4 h64 h_v3 h_a1 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v0 h_v1 h_v2 h_v3
  store_step with Store.apply_rep s5 a0 v4 _ _ hinv5 h64 h_a0 h_v4 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v0 h_v1 h_v2 h_v3 h_v4
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s6 0#u32 (0) (by scalar_tac) hinv6 h64 as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo_extract.construct s7 e_v7 (by rw [he_v7]; rfl) h_a5 h_v6 hinv7 h64 as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  store_step with Store.apply_rep s8 v7 a2 _ _ hinv8 h64 h_v7 h_a2 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  store_step with Store.apply_rep s9 a0 v8 _ _ hinv9 h64 h_a0 h_v8 (by ns_tac) (by ns_tac) as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s10 0#u32 (0) (by scalar_tac) hinv10 h64 as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  step as ⟨e_v11, he_v11⟩
  store_step with CtorSpec.eo_extract.construct s11 e_v11 (by rw [he_v11]; rfl) h_a5 h_v10 hinv11 h64 as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
  store_step with Store.apply_rep s12 v11 a1 _ _ hinv12 h64 h_v11 h_a1 (by ns_tac) (by ns_tac) as ⟨v12, s13, hinv13, h_v12⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11
  store_step with ih.eo__24eo_5ftypeof s13 v12 _ hinv13 h64 (hG.rem hrem) h_v12 as ⟨v13, s14, hinv14, h_v13⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
  store_step with ih.eo__24eo_5fnil s14 a0 v13 _ _ hinv14 h64 (hG.rem hrem) h_a0 h_v13 as ⟨v14, s15, hinv15, h_v14⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13
  store_step with Store.apply_mk_rep s15 v9 v14 _ _ hinv15 h64 h_v9 h_v14 as ⟨v15, s16, hinv16, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14
  store_step with Store.apply_mk_rep s16 v5 v15 _ _ hinv16 h64 h_v5 h_v15 as ⟨v16, s17, hinv17, h_v16⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15
  store_step with Store.apply_mk_rep s17 v1 v16 _ _ hinv17 h64 h_v1 h_v16 as ⟨v17, s18, hinv18, h_v17⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s18 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv18 h64 as ⟨v18, s19, hinv19, h_v18⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17
  store_step with Store.apply_mk_rep s19 v17 v18 _ _ hinv19 h64 h_v17 h_v18 as ⟨v19, s20, hinv20, h_v19⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18
  case_done hinv20 hG with h_v19 in EoCases.__bv_mk_bitwise_slicing_rec.case_0 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_a5 hn_a6

theorem case_1_eo__24bv_5fmk_5fbitwise_5fslicing_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 a6 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) (h_a6 : Represents.rep s a6 x_a6) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) (hn_a4 : x_a4 ≠ Eo.Term.Stuck) (hn_a5 : x_a5 ≠ Eo.Term.Stuck) (hn_a6 : x_a6 ≠ Eo.Term.Stuck) :
    case_1_eo__24bv_5fmk_5fbitwise_5fslicing_5frec s a0 a1 a2 a3 a4 a5 a6 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__bv_mk_bitwise_slicing_rec.case_1 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__bv_mk_bitwise_slicing_rec.case_1 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24bv_5fmk_5fbitwise_5fslicing_5frec
  have hG := Store.Grows.refl s
  pat_unapply h_a3 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__bv_mk_bitwise_slicing_rec.case_1
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__bv_mk_bitwise_slicing_rec.case_1
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__bv_mk_bitwise_slicing_rec.case_1
  step as ⟨e_v7, he_v7⟩
  store_step with Store.builtin_spec_eq s1 e_v7 (by rw [he_v7]; rfl) h_v5 h_a4 hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v1 h_v2 h_v4 h_v5 h_v6
  have h_ite_v35 := (show if_2_eo__24bv_5fmk_5fbitwise_5fslicing_5frec s2 v7 a6 a0 a1 a2 v2 v5 a5 ⦃ r s' => s'.Inv ∧ s2.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_2_eo__24bv_5fmk_5fbitwise_5fslicing_5frec more_1_eo__24bv_5fmk_5fbitwise_5fslicing_5frec
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s2
    rcases Store.boolean_value_term h_v7 with ⟨hx_8, hbv_8⟩ | ⟨hx_8, hbv_8⟩ | ⟨hx_8, hbv_8⟩
    · ite_branch hbv_8
      try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
      store_step with Store.literal_int_neg_u32_spec s2 1#u32 (-1) (by scalar_tac) hinv2 h64 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
      step as ⟨e_v9, he_v9⟩
      store_step with Store.builtin_spec_add s3 e_v9 (by rw [he_v9]; rfl) h_a6 h_v8 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
      store_step with ih.eo__24bv_5fmk_5fbitwise_5fslicing_5frec s4 a0 a1 a2 v2 v5 a5 v9 _ _ _ _ _ _ _ hinv4 h64 (hG.rem hrem) h_a0 h_a1 h_a2 h_v2 h_v5 h_a5 h_v9 as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
      ite_done hinv5 hG with (eo_ite_true_rep _ hx_8 h_v10)
    · ite_branch hbv_8
      step as ⟨e_v11, he_v11⟩
      store_step with CtorSpec.eo_concat.construct s2 e_v11 (by rw [he_v11]; exact empty_args) hinv2 h64 as ⟨v11, s3, hinv3, h_v11⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
      try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
      store_step with Store.literal_int_u32_spec s3 1#u32 (1) (by scalar_tac) hinv3 h64 as ⟨v12, s4, hinv4, h_v12⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v11
      step as ⟨e_v13, he_v13⟩
      store_step with Store.builtin_spec_add s4 e_v13 (by rw [he_v13]; rfl) h_a6 h_v12 hinv4 h64 as ⟨v13, s5, hinv5, h_v13⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v11 h_v12
      step as ⟨e_v14, he_v14⟩
      store_step with CtorSpec.eo_extract.construct s5 e_v14 (by rw [he_v14]; rfl) h_a5 h_v13 hinv5 h64 as ⟨v14, s6, hinv6, h_v14⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v11 h_v12 h_v13
      store_step with Store.apply_mk_rep s6 v14 a1 _ _ hinv6 h64 h_v14 h_a1 as ⟨v15, s7, hinv7, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v11 h_v12 h_v13 h_v14
      store_step with Store.apply_mk_rep s7 a0 v15 _ _ hinv7 h64 h_a0 h_v15 as ⟨v16, s8, hinv8, h_v16⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v11 h_v12 h_v13 h_v14 h_v15
      try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
      store_step with Store.literal_int_u32_spec s8 1#u32 (1) (by scalar_tac) hinv8 h64 as ⟨v17, s9, hinv9, h_v17⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16
      step as ⟨e_v18, he_v18⟩
      store_step with Store.builtin_spec_add s9 e_v18 (by rw [he_v18]; rfl) h_a6 h_v17 hinv9 h64 as ⟨v18, s10, hinv10, h_v18⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17
      step as ⟨e_v19, he_v19⟩
      store_step with CtorSpec.eo_extract.construct s10 e_v19 (by rw [he_v19]; rfl) h_a5 h_v18 hinv10 h64 as ⟨v19, s11, hinv11, h_v19⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18
      store_step with Store.apply_mk_rep s11 v19 a2 _ _ hinv11 h64 h_v19 h_a2 as ⟨v20, s12, hinv12, h_v20⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19
      store_step with Store.apply_mk_rep s12 a0 v20 _ _ hinv12 h64 h_a0 h_v20 as ⟨v21, s13, hinv13, h_v21⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20
      try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
      store_step with Store.literal_int_u32_spec s13 1#u32 (1) (by scalar_tac) hinv13 h64 as ⟨v22, s14, hinv14, h_v22⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21
      step as ⟨e_v23, he_v23⟩
      store_step with Store.builtin_spec_add s14 e_v23 (by rw [he_v23]; rfl) h_a6 h_v22 hinv14 h64 as ⟨v23, s15, hinv15, h_v23⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22
      step as ⟨e_v24, he_v24⟩
      store_step with CtorSpec.eo_extract.construct s15 e_v24 (by rw [he_v24]; rfl) h_a5 h_v23 hinv15 h64 as ⟨v24, s16, hinv16, h_v24⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23
      store_step with Store.apply_mk_rep s16 v24 a1 _ _ hinv16 h64 h_v24 h_a1 as ⟨v25, s17, hinv17, h_v25⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24
      store_step with ih.eo__24eo_5ftypeof s17 v25 _ hinv17 h64 (hG.rem hrem) h_v25 as ⟨v26, s18, hinv18, h_v26⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25
      store_step with ih.eo__24eo_5fnil s18 a0 v26 _ _ hinv18 h64 (hG.rem hrem) h_a0 h_v26 as ⟨v27, s19, hinv19, h_v27⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26
      store_step with Store.apply_mk_rep s19 v21 v27 _ _ hinv19 h64 h_v21 h_v27 as ⟨v28, s20, hinv20, h_v28⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27
      store_step with Store.apply_mk_rep s20 v16 v28 _ _ hinv20 h64 h_v16 h_v28 as ⟨v29, s21, hinv21, h_v29⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28
      store_step with Store.apply_mk_rep s21 v11 v29 _ _ hinv21 h64 h_v11 h_v29 as ⟨v30, s22, hinv22, h_v30⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29
      try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
      store_step with Store.literal_int_neg_u32_spec s22 1#u32 (-1) (by scalar_tac) hinv22 h64 as ⟨v31, s23, hinv23, h_v31⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30
      step as ⟨e_v32, he_v32⟩
      store_step with Store.builtin_spec_add s23 e_v32 (by rw [he_v32]; rfl) h_a6 h_v31 hinv23 h64 as ⟨v32, s24, hinv24, h_v32⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31
      store_step with ih.eo__24bv_5fmk_5fbitwise_5fslicing_5frec s24 a0 a1 a2 v2 v5 a6 v32 _ _ _ _ _ _ _ hinv24 h64 (hG.rem hrem) h_a0 h_a1 h_a2 h_v2 h_v5 h_a6 h_v32 as ⟨v33, s25, hinv25, h_v33⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32
      store_step with Store.apply_mk_rep s25 v30 v33 _ _ hinv25 h64 h_v30 h_v33 as ⟨v34, s26, hinv26, h_v34⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33
      ite_done hinv26 hG with (eo_ite_false_rep _ hx_8 h_v34)
    · ite_branch hbv_8
      ite_stuck hinv2 hG with hx_8)
  store_step with h_ite_v35 as ⟨v35, s3, hinv3, h_v35⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  case_done hinv3 hG with h_v35 in EoCases.__bv_mk_bitwise_slicing_rec.case_1 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_a5 hn_a6 hn_v1 hn_v2 hn_v4 hn_v5

/-- logos's `__bv_mk_bitwise_slicing_rec` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24bv_5fmk_5fbitwise_5fslicing_5frec.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) (hw_a4 : Valid.valid x_a4) (hw_a5 : Valid.valid x_a5) (hw_a6 : Valid.valid x_a6) :
    __bv_mk_bitwise_slicing_rec x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else if x_a4 = Eo.Term.Stuck then HasStuck.stuck else if x_a5 = Eo.Term.Stuck then HasStuck.stuck else if x_a6 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__bv_mk_bitwise_slicing_rec.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6, EoCases.__bv_mk_bitwise_slicing_rec.case_1 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6] HasStuck.stuck) := by
  conv => lhs; unfold __bv_mk_bitwise_slicing_rec
  unfold EoCases.__bv_mk_bitwise_slicing_rec.case_0 EoCases.__bv_mk_bitwise_slicing_rec.case_1
  logos_eq

theorem body_eo__24bv_5fmk_5fbitwise_5fslicing_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 a6 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) (h_a6 : Represents.rep s a6 x_a6) :
    body_eo__24bv_5fmk_5fbitwise_5fslicing_5frec s a0 a1 a2 a3 a4 a5 a6 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__bv_mk_bitwise_slicing_rec x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24bv_5fmk_5fbitwise_5fslicing_5frec.rust_eq x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3) (by valid_tac hinv h_a4) (by valid_tac hinv h_a5) (by valid_tac hinv h_a6)]
  unfold body_eo__24bv_5fmk_5fbitwise_5fslicing_5frec
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  stuck_check h_a3 : x_a3 as hn_a3 else hinv hG
  stuck_check h_a4 : x_a4 as hn_a4 else hinv hG
  stuck_check h_a5 : x_a5 as hn_a5 else hinv hG
  stuck_check h_a6 : x_a6 as hn_a6 else hinv hG
  case_step with case_0_eo__24bv_5fmk_5fbitwise_5fslicing_5frec_spec n ih s a0 a1 a2 a3 a4 a5 a6 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_a5 hn_a6
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_a5 hn_a6
  case_step with case_1_eo__24bv_5fmk_5fbitwise_5fslicing_5frec_spec n ih s1 a0 a1 a2 a3 a4 a5 a6 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_a5 hn_a6
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_a5 hn_a6 hc0
  body_stuck hinv2 hG using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_a5 hn_a6 hc0 hc1 in EoCases.__bv_mk_bitwise_slicing_rec.case_0 EoCases.__bv_mk_bitwise_slicing_rec.case_1

theorem eo__24bv_5fmk_5fbitwise_5fslicing_5frec_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24bv_5fmk_5fbitwise_5fslicing_5frec.Spec n := by
  intro s a0 a1 a2 a3 a4 a5 a6 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6
  unfold eo__24bv_5fmk_5fbitwise_5fslicing_5frec
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 47#u32 _ [a0, a1, a2, a3, a4, a5, a6] rfl
    (fun s1 => body_eo__24bv_5fmk_5fbitwise_5fslicing_5frec s1 a0 a1 a2 a3 a4 a5 a6) (fun s' t => Represents.rep s' t (__bv_mk_bitwise_slicing_rec x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, b2, b3, b4, b5, b6, y0, y1, y2, y3, y4, y5, y6, hargs, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hr⟩ := ProgramSem.of_47 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      obtain rfl := Rep.functional hb2 (Represents.congr h_a2 hn)
      obtain rfl := Rep.functional hb3 (Represents.congr h_a3 hn)
      obtain rfl := Rep.functional hb4 (Represents.congr h_a4 hn)
      obtain rfl := Rep.functional hb5 (Represents.congr h_a5 hn)
      obtain rfl := Rep.functional hb6 (Represents.congr h_a6 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_47 ⟨a0, a1, a2, a3, a4, a5, a6, x_a0, x_a1, x_a2, x_a3, x_a4, x_a5, x_a6, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, Rep.mono hpre h_a2, Rep.mono hpre h_a3, Rep.mono hpre h_a4, Rep.mono hpre h_a5, Rep.mono hpre h_a6, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24bv_5fmk_5fbitwise_5fslicing_5frec_spec m (ih m hm) s1 a0 a1 a2 a3 a4 a5 a6 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn) (by congr_one h_a4 hn) (by congr_one h_a5 hn) (by congr_one h_a6 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24bv_5fripple_5fcarry_5fadder_5f2_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    case_0_eo__24bv_5fripple_5fcarry_5fadder_5f2 s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__bv_ripple_carry_adder_2.case_0 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _) (u3 : Term) (y3 : _), arr.val = [u0, u1, u2, u3] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧ Represents.rep s' u3 y3 ∧
          EoCases.__bv_ripple_carry_adder_2.case_0 x_a0 x_a1 x_a2 x_a3 = some (__bv_ripple_carry_adder_2 y0 y1 y2 y3)
      | core.result.Result.Ok none => EoCases.__bv_ripple_carry_adder_2.case_0 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24bv_5fripple_5fcarry_5fadder_5f2 more_0_eo__24bv_5fripple_5fcarry_5fadder_5f2 more_1_eo__24bv_5fripple_5fcarry_5fadder_5f2 more_2_eo__24bv_5fripple_5fcarry_5fadder_5f2
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__bv_ripple_carry_adder_2.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__bv_ripple_carry_adder_2.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__bv_ripple_carry_adder_2.case_0
  pat_unapply h_a1 as ⟨v8, v9, x_v8, x_v9, h_v8, h_v9, hn_v8, hn_v9⟩ using hinv1 else hinv1 hG in EoCases.__bv_ripple_carry_adder_2.case_0
  pat_unapply h_v8 as ⟨v11, v12, x_v11, x_v12, h_v11, h_v12, hn_v11, hn_v12⟩ using hinv1 else hinv1 hG in EoCases.__bv_ripple_carry_adder_2.case_0
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s1 e_v13 (by rw [he_v13]; exact empty_args) hinv1 h64 as ⟨v13, s2, hinv2, h_v13⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12
  pat_same v11 v13 with h_v11 h_v13 using hinv2 else hinv2 hG in EoCases.__bv_ripple_carry_adder_2.case_0
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo_or.construct s2 e_v14 (by rw [he_v14]; exact empty_args) hinv2 h64 as ⟨v14, s3, hinv3, h_v14⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo_and.construct s3 e_v15 (by rw [he_v15]; exact empty_args) hinv3 h64 as ⟨v15, s4, hinv4, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14
  store_step with Store.apply_rep s4 v15 v5 _ _ hinv4 h64 h_v15 h_v5 (by ns_tac) (by ns_tac) as ⟨v16, s5, hinv5, h_v16⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15
  step as ⟨e_v17, he_v17⟩
  store_step with CtorSpec.eo_and.construct s5 e_v17 (by rw [he_v17]; exact empty_args) hinv5 h64 as ⟨v17, s6, hinv6, h_v17⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16
  store_step with Store.apply_rep s6 v17 v12 _ _ hinv6 h64 h_v17 h_v12 (by ns_tac) (by ns_tac) as ⟨v18, s7, hinv7, h_v18⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17
  store_step with Store.literal_boolean_spec s7 true hinv7 h64 as ⟨v19, s8, hinv8, h_v19⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18
  store_step with Store.apply_rep s8 v18 v19 _ _ hinv8 h64 h_v18 h_v19 (by ns_tac) (by ns_tac) as ⟨v20, s9, hinv9, h_v20⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19
  store_step with Store.apply_rep s9 v16 v20 _ _ hinv9 h64 h_v16 h_v20 (by ns_tac) (by ns_tac) as ⟨v21, s10, hinv10, h_v21⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20
  store_step with Store.apply_rep s10 v14 v21 _ _ hinv10 h64 h_v14 h_v21 (by ns_tac) (by ns_tac) as ⟨v22, s11, hinv11, h_v22⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21
  step as ⟨e_v23, he_v23⟩
  store_step with CtorSpec.eo_or.construct s11 e_v23 (by rw [he_v23]; exact empty_args) hinv11 h64 as ⟨v23, s12, hinv12, h_v23⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22
  step as ⟨e_v24, he_v24⟩
  store_step with CtorSpec.eo_and.construct s12 e_v24 (by rw [he_v24]; exact empty_args) hinv12 h64 as ⟨v24, s13, hinv13, h_v24⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23
  step as ⟨e_v25, he_v25⟩
  store_step with CtorSpec.eo_xor.construct s13 e_v25 (by rw [he_v25]; exact empty_args) hinv13 h64 as ⟨v25, s14, hinv14, h_v25⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24
  store_step with Store.apply_rep s14 v25 v5 _ _ hinv14 h64 h_v25 h_v5 (by ns_tac) (by ns_tac) as ⟨v26, s15, hinv15, h_v26⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25
  store_step with Store.apply_rep s15 v26 v12 _ _ hinv15 h64 h_v26 h_v12 (by ns_tac) (by ns_tac) as ⟨v27, s16, hinv16, h_v27⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26
  store_step with Store.apply_rep s16 v24 v27 _ _ hinv16 h64 h_v24 h_v27 (by ns_tac) (by ns_tac) as ⟨v28, s17, hinv17, h_v28⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27
  step as ⟨e_v29, he_v29⟩
  store_step with CtorSpec.eo_and.construct s17 e_v29 (by rw [he_v29]; exact empty_args) hinv17 h64 as ⟨v29, s18, hinv18, h_v29⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28
  store_step with Store.apply_rep s18 v29 a2 _ _ hinv18 h64 h_v29 h_a2 (by ns_tac) (by ns_tac) as ⟨v30, s19, hinv19, h_v30⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29
  store_step with Store.literal_boolean_spec s19 true hinv19 h64 as ⟨v31, s20, hinv20, h_v31⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30
  store_step with Store.apply_rep s20 v30 v31 _ _ hinv20 h64 h_v30 h_v31 (by ns_tac) (by ns_tac) as ⟨v32, s21, hinv21, h_v32⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31
  store_step with Store.apply_rep s21 v28 v32 _ _ hinv21 h64 h_v28 h_v32 (by ns_tac) (by ns_tac) as ⟨v33, s22, hinv22, h_v33⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32
  store_step with Store.apply_rep s22 v23 v33 _ _ hinv22 h64 h_v23 h_v33 (by ns_tac) (by ns_tac) as ⟨v34, s23, hinv23, h_v34⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33
  store_step with Store.literal_boolean_spec s23 false hinv23 h64 as ⟨v35, s24, hinv24, h_v35⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34
  store_step with Store.apply_rep s24 v34 v35 _ _ hinv24 h64 h_v34 h_v35 (by ns_tac) (by ns_tac) as ⟨v36, s25, hinv25, h_v36⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35
  store_step with Store.apply_rep s25 v22 v36 _ _ hinv25 h64 h_v22 h_v36 (by ns_tac) (by ns_tac) as ⟨v37, s26, hinv26, h_v37⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36
  step as ⟨e_v38, he_v38⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s26 e_v38 (by rw [he_v38]; exact empty_args) hinv26 h64 as ⟨v38, s27, hinv27, h_v38⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37
  step as ⟨e_v39, he_v39⟩
  store_step with CtorSpec.eo_xor.construct s27 e_v39 (by rw [he_v39]; exact empty_args) hinv27 h64 as ⟨v39, s28, hinv28, h_v39⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38
  step as ⟨e_v40, he_v40⟩
  store_step with CtorSpec.eo_xor.construct s28 e_v40 (by rw [he_v40]; exact empty_args) hinv28 h64 as ⟨v40, s29, hinv29, h_v40⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39
  store_step with Store.apply_rep s29 v40 v5 _ _ hinv29 h64 h_v40 h_v5 (by ns_tac) (by ns_tac) as ⟨v41, s30, hinv30, h_v41⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40
  store_step with Store.apply_rep s30 v41 v12 _ _ hinv30 h64 h_v41 h_v12 (by ns_tac) (by ns_tac) as ⟨v42, s31, hinv31, h_v42⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41
  store_step with Store.apply_rep s31 v39 v42 _ _ hinv31 h64 h_v39 h_v42 (by ns_tac) (by ns_tac) as ⟨v43, s32, hinv32, h_v43⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42
  store_step with Store.apply_rep s32 v43 a2 _ _ hinv32 h64 h_v43 h_a2 (by ns_tac) (by ns_tac) as ⟨v44, s33, hinv33, h_v44⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43
  store_step with Store.apply_rep s33 v38 v44 _ _ hinv33 h64 h_v38 h_v44 (by ns_tac) (by ns_tac) as ⟨v45, s34, hinv34, h_v45⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44
  store_step with Store.apply_rep s34 v45 a3 _ _ hinv34 h64 h_v45 h_a3 (by ns_tac) (by ns_tac) as ⟨v46, s35, hinv35, h_v46⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45
  case_again hinv35 hG with h_v2 h_v9 h_v37 h_v46 in EoCases.__bv_ripple_carry_adder_2.case_0 using hn_a0 hn_a1 hn_a2 hn_a3 hn_v1 hn_v2 hn_v4 hn_v5 hn_v8 hn_v9 hn_v11 hn_v12

theorem case_1_eo__24bv_5fripple_5fcarry_5fadder_5f2_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    case_1_eo__24bv_5fripple_5fcarry_5fadder_5f2 s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__bv_ripple_carry_adder_2.case_1 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _) (u3 : Term) (y3 : _), arr.val = [u0, u1, u2, u3] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧ Represents.rep s' u3 y3 ∧
          EoCases.__bv_ripple_carry_adder_2.case_1 x_a0 x_a1 x_a2 x_a3 = some (__bv_ripple_carry_adder_2 y0 y1 y2 y3)
      | core.result.Result.Ok none => EoCases.__bv_ripple_carry_adder_2.case_1 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24bv_5fripple_5fcarry_5fadder_5f2
  have hG := Store.Grows.refl s
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__bv_ripple_carry_adder_2.case_1
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s1 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0
  pat_same a1 v1 with h_a1 h_v1 using hinv2 else hinv2 hG in EoCases.__bv_ripple_carry_adder_2.case_1
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__40_40pair.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a2 _ _ hinv3 h64 h_v2 h_a2 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s4 e_v4 (by rw [he_v4]; exact empty_args) hinv4 h64 as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with Store.builtin_spec_list_rev n ih.eo__24eo_5fis_5flist_5fnil s5 e_v5 (by rw [he_v5]; rfl) h_v4 h_a3 hinv5 h64 (hG.rem hrem) (by not_left_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4
  store_step with Store.apply_mk_rep s6 v3 v5 _ _ hinv6 h64 h_v3 h_v5 as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5
  case_done hinv7 hG with h_v6 in EoCases.__bv_ripple_carry_adder_2.case_1 using hn_a0 hn_a1 hn_a2 hn_a3

/-- logos's `__bv_ripple_carry_adder_2` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24bv_5fripple_5fcarry_5fadder_5f2.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) :
    __bv_ripple_carry_adder_2 x_a0 x_a1 x_a2 x_a3 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__bv_ripple_carry_adder_2.case_0 x_a0 x_a1 x_a2 x_a3, EoCases.__bv_ripple_carry_adder_2.case_1 x_a0 x_a1 x_a2 x_a3] HasStuck.stuck) := by
  conv => lhs; unfold __bv_ripple_carry_adder_2
  unfold EoCases.__bv_ripple_carry_adder_2.case_0 EoCases.__bv_ripple_carry_adder_2.case_1
  logos_eq

theorem step_eo__24bv_5fripple_5fcarry_5fadder_5f2_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) :
    step_eo__24bv_5fripple_5fcarry_5fadder_5f2 s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (Next.Done t) => Represents.rep s' t (__bv_ripple_carry_adder_2 x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Ok (Next.Again arr) =>
        s'.budget < s.budget ∧ ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _) (u3 : Term) (y3 : _), arr.val = [u0, u1, u2, u3] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧ Represents.rep s' u3 y3 ∧
          __bv_ripple_carry_adder_2 x_a0 x_a1 x_a2 x_a3 = __bv_ripple_carry_adder_2 y0 y1 y2 y3
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24bv_5fripple_5fcarry_5fadder_5f2.rust_eq x_a0 x_a1 x_a2 x_a3 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3)]
  unfold step_eo__24bv_5fripple_5fcarry_5fadder_5f2
  have hG := Store.Grows.refl s
  tick_step as ⟨s1, hinv1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
  stuck_check h_a0 : x_a0 as hn_a0 else hinv1 hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv1 hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv1 hG
  stuck_check h_a3 : x_a3 as hn_a3 else hinv1 hG
  round_step with case_0_eo__24bv_5fripple_5fcarry_5fadder_5f2_spec n ih s1 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2 hn_a3
    as ⟨s2, hinv2, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 hbud using hn_a0 hn_a1 hn_a2 hn_a3
  round_step with case_1_eo__24bv_5fripple_5fcarry_5fadder_5f2_spec n ih s2 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv2 h64 (hG.rem hrem) h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2 hn_a3
    as ⟨s3, hinv3, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 hbud using hn_a0 hn_a1 hn_a2 hn_a3 hc0
  round_stuck hinv3 hG using hn_a0 hn_a1 hn_a2 hn_a3 hc0 hc1 in EoCases.__bv_ripple_carry_adder_2.case_0 EoCases.__bv_ripple_carry_adder_2.case_1

theorem body_eo__24bv_5fripple_5fcarry_5fadder_5f2_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) :
    body_eo__24bv_5fripple_5fcarry_5fadder_5f2 s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__bv_ripple_carry_adder_2 x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div := by
  refine (?_ : ∀ (k : Nat) (a0 a1 a2 a3 : Term) (s : Store) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _), s.budget ≤ k → s.Inv → s.remaining ≤ n →
      Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 →
      body_eo__24bv_5fripple_5fcarry_5fadder_5f2 s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__bv_ripple_carry_adder_2 x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div) s.budget a0 a1 a2 a3 s x_a0 x_a1 x_a2 x_a3 le_rfl hinv hrem h_a0 h_a1 h_a2 h_a3
  intro k
  refine Nat.strong_induction_on k ?_
  intro k ihl a0 a1 a2 a3 s x_a0 x_a1 x_a2 x_a3 hk hinv hrem h_a0 h_a1 h_a2 h_a3
  unfold body_eo__24bv_5fripple_5fcarry_5fadder_5f2 body_eo__24bv_5fripple_5fcarry_5fadder_5f2_loop
  step with step_eo__24bv_5fripple_5fcarry_5fadder_5f2_spec n ih s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 as ⟨r, s1, hinv1, hg1, hr⟩
  cases r with
  | Err e => simp only [WP.dspec_ok, WP.uncurry'_pair]; exact ⟨hinv1, hg1, trivial⟩
  | Ok nx =>
    cases nx with
    | Done value =>
      simp only [WP.dspec_ok, WP.uncurry'_pair]
      exact ⟨hinv1, hg1, hr⟩
    | Again next =>
      obtain ⟨hlt, u0, y0, u1, y1, u2, y2, u3, y3, hnext, hrep0, hrep1, hrep2, hrep3, heq⟩ := hr
      simp only
      have hlen : next.length = 4 := by simp [Array.length, hnext]
      step as ⟨b0, hb0⟩
      obtain rfl : b0 = u0 := by simp [hb0, hnext]
      step as ⟨b1, hb1⟩
      obtain rfl : b1 = u1 := by simp [hb1, hnext]
      step as ⟨b2, hb2⟩
      obtain rfl : b2 = u2 := by simp [hb2, hnext]
      step as ⟨b3, hb3⟩
      obtain rfl : b3 = u3 := by simp [hb3, hnext]
      have hrec := ihl s1.budget (by omega) b0 b1 b2 b3 s1 y0 y1 y2 y3 le_rfl hinv1 (hg1.rem hrem)  hrep0  hrep1  hrep2  hrep3
      unfold body_eo__24bv_5fripple_5fcarry_5fadder_5f2 at hrec
      apply WP.dspec_mono hrec
      loop_close hg1 heq

theorem eo__24bv_5fripple_5fcarry_5fadder_5f2_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24bv_5fripple_5fcarry_5fadder_5f2.Spec n := by
  intro s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3
  unfold eo__24bv_5fripple_5fcarry_5fadder_5f2
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 48#u32 _ [a0, a1, a2, a3] rfl
    (fun s1 => body_eo__24bv_5fripple_5fcarry_5fadder_5f2 s1 a0 a1 a2 a3) (fun s' t => Represents.rep s' t (__bv_ripple_carry_adder_2 x_a0 x_a1 x_a2 x_a3))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, b2, b3, y0, y1, y2, y3, hargs, hb0, hb1, hb2, hb3, hr⟩ := ProgramSem.of_48 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      obtain rfl := Rep.functional hb2 (Represents.congr h_a2 hn)
      obtain rfl := Rep.functional hb3 (Represents.congr h_a3 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_48 ⟨a0, a1, a2, a3, x_a0, x_a1, x_a2, x_a3, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, Rep.mono hpre h_a2, Rep.mono hpre h_a3, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24bv_5fripple_5fcarry_5fadder_5f2_spec m (ih m hm) s1 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24bv_5fshift_5fadd_5fmultiplier_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    case_0_eo__24bv_5fshift_5fadd_5fmultiplier_5frec s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__bv_shift_add_multiplier_rec.case_0 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _) (u3 : Term) (y3 : _), arr.val = [u0, u1, u2, u3] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧ Represents.rep s' u3 y3 ∧
          EoCases.__bv_shift_add_multiplier_rec.case_0 x_a0 x_a1 x_a2 x_a3 = some (__bv_shift_add_multiplier_rec y0 y1 y2 y3)
      | core.result.Result.Ok none => EoCases.__bv_shift_add_multiplier_rec.case_0 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24bv_5fshift_5fadd_5fmultiplier_5frec
  have hG := Store.Grows.refl s
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__bv_shift_add_multiplier_rec.case_0
  case_done hinv1 hG with h_a3 in EoCases.__bv_shift_add_multiplier_rec.case_0 using hn_a0 hn_a1 hn_a2 hn_a3

theorem case_1_eo__24bv_5fshift_5fadd_5fmultiplier_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    case_1_eo__24bv_5fshift_5fadd_5fmultiplier_5frec s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__bv_shift_add_multiplier_rec.case_1 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _) (u3 : Term) (y3 : _), arr.val = [u0, u1, u2, u3] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧ Represents.rep s' u3 y3 ∧
          EoCases.__bv_shift_add_multiplier_rec.case_1 x_a0 x_a1 x_a2 x_a3 = some (__bv_shift_add_multiplier_rec y0 y1 y2 y3)
      | core.result.Result.Ok none => EoCases.__bv_shift_add_multiplier_rec.case_1 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24bv_5fshift_5fadd_5fmultiplier_5frec
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__bv_shift_add_multiplier_rec.case_1
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__bv_shift_add_multiplier_rec.case_1
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__bv_shift_add_multiplier_rec.case_1
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s1 1#u32 (1) (by scalar_tac) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v2 h_v4 h_v5 h_v6
  step as ⟨e_v8, he_v8⟩
  store_step with Store.builtin_spec_add s2 e_v8 (by rw [he_v8]; rfl) h_a2 h_v7 hinv2 h64 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with Store.literal_boolean_spec s3 false hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  store_step with ih.eo__24bv_5fshift_5fadd_5fmultiplier_5frec_5fstep s4 v5 a1 a2 a3 v9 _ _ _ _ _ hinv4 h64 (hG.rem hrem) h_v5 h_a1 h_a2 h_a3 h_v9 as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  case_again hinv5 hG with h_v2 h_a1 h_v8 h_v10 in EoCases.__bv_shift_add_multiplier_rec.case_1 using hn_a0 hn_a1 hn_a2 hn_a3 hn_v1 hn_v2 hn_v4 hn_v5

/-- logos's `__bv_shift_add_multiplier_rec` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24bv_5fshift_5fadd_5fmultiplier_5frec.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) :
    __bv_shift_add_multiplier_rec x_a0 x_a1 x_a2 x_a3 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__bv_shift_add_multiplier_rec.case_0 x_a0 x_a1 x_a2 x_a3, EoCases.__bv_shift_add_multiplier_rec.case_1 x_a0 x_a1 x_a2 x_a3] HasStuck.stuck) := by
  conv => lhs; unfold __bv_shift_add_multiplier_rec
  unfold EoCases.__bv_shift_add_multiplier_rec.case_0 EoCases.__bv_shift_add_multiplier_rec.case_1
  logos_eq

theorem step_eo__24bv_5fshift_5fadd_5fmultiplier_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) :
    step_eo__24bv_5fshift_5fadd_5fmultiplier_5frec s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (Next.Done t) => Represents.rep s' t (__bv_shift_add_multiplier_rec x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Ok (Next.Again arr) =>
        s'.budget < s.budget ∧ ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _) (u3 : Term) (y3 : _), arr.val = [u0, u1, u2, u3] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧ Represents.rep s' u3 y3 ∧
          __bv_shift_add_multiplier_rec x_a0 x_a1 x_a2 x_a3 = __bv_shift_add_multiplier_rec y0 y1 y2 y3
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24bv_5fshift_5fadd_5fmultiplier_5frec.rust_eq x_a0 x_a1 x_a2 x_a3 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3)]
  unfold step_eo__24bv_5fshift_5fadd_5fmultiplier_5frec
  have hG := Store.Grows.refl s
  tick_step as ⟨s1, hinv1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
  stuck_check h_a0 : x_a0 as hn_a0 else hinv1 hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv1 hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv1 hG
  stuck_check h_a3 : x_a3 as hn_a3 else hinv1 hG
  round_step with case_0_eo__24bv_5fshift_5fadd_5fmultiplier_5frec_spec n ih s1 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2 hn_a3
    as ⟨s2, hinv2, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 hbud using hn_a0 hn_a1 hn_a2 hn_a3
  round_step with case_1_eo__24bv_5fshift_5fadd_5fmultiplier_5frec_spec n ih s2 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv2 h64 (hG.rem hrem) h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2 hn_a3
    as ⟨s3, hinv3, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 hbud using hn_a0 hn_a1 hn_a2 hn_a3 hc0
  round_stuck hinv3 hG using hn_a0 hn_a1 hn_a2 hn_a3 hc0 hc1 in EoCases.__bv_shift_add_multiplier_rec.case_0 EoCases.__bv_shift_add_multiplier_rec.case_1

theorem body_eo__24bv_5fshift_5fadd_5fmultiplier_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) :
    body_eo__24bv_5fshift_5fadd_5fmultiplier_5frec s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__bv_shift_add_multiplier_rec x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div := by
  refine (?_ : ∀ (k : Nat) (a0 a1 a2 a3 : Term) (s : Store) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _), s.budget ≤ k → s.Inv → s.remaining ≤ n →
      Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 →
      body_eo__24bv_5fshift_5fadd_5fmultiplier_5frec s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__bv_shift_add_multiplier_rec x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div) s.budget a0 a1 a2 a3 s x_a0 x_a1 x_a2 x_a3 le_rfl hinv hrem h_a0 h_a1 h_a2 h_a3
  intro k
  refine Nat.strong_induction_on k ?_
  intro k ihl a0 a1 a2 a3 s x_a0 x_a1 x_a2 x_a3 hk hinv hrem h_a0 h_a1 h_a2 h_a3
  unfold body_eo__24bv_5fshift_5fadd_5fmultiplier_5frec body_eo__24bv_5fshift_5fadd_5fmultiplier_5frec_loop
  step with step_eo__24bv_5fshift_5fadd_5fmultiplier_5frec_spec n ih s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 as ⟨r, s1, hinv1, hg1, hr⟩
  cases r with
  | Err e => simp only [WP.dspec_ok, WP.uncurry'_pair]; exact ⟨hinv1, hg1, trivial⟩
  | Ok nx =>
    cases nx with
    | Done value =>
      simp only [WP.dspec_ok, WP.uncurry'_pair]
      exact ⟨hinv1, hg1, hr⟩
    | Again next =>
      obtain ⟨hlt, u0, y0, u1, y1, u2, y2, u3, y3, hnext, hrep0, hrep1, hrep2, hrep3, heq⟩ := hr
      simp only
      have hlen : next.length = 4 := by simp [Array.length, hnext]
      step as ⟨b0, hb0⟩
      obtain rfl : b0 = u0 := by simp [hb0, hnext]
      step as ⟨b1, hb1⟩
      obtain rfl : b1 = u1 := by simp [hb1, hnext]
      step as ⟨b2, hb2⟩
      obtain rfl : b2 = u2 := by simp [hb2, hnext]
      step as ⟨b3, hb3⟩
      obtain rfl : b3 = u3 := by simp [hb3, hnext]
      have hrec := ihl s1.budget (by omega) b0 b1 b2 b3 s1 y0 y1 y2 y3 le_rfl hinv1 (hg1.rem hrem)  hrep0  hrep1  hrep2  hrep3
      unfold body_eo__24bv_5fshift_5fadd_5fmultiplier_5frec at hrec
      apply WP.dspec_mono hrec
      loop_close hg1 heq

theorem eo__24bv_5fshift_5fadd_5fmultiplier_5frec_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24bv_5fshift_5fadd_5fmultiplier_5frec.Spec n := by
  intro s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3
  unfold eo__24bv_5fshift_5fadd_5fmultiplier_5frec
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 50#u32 _ [a0, a1, a2, a3] rfl
    (fun s1 => body_eo__24bv_5fshift_5fadd_5fmultiplier_5frec s1 a0 a1 a2 a3) (fun s' t => Represents.rep s' t (__bv_shift_add_multiplier_rec x_a0 x_a1 x_a2 x_a3))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, b2, b3, y0, y1, y2, y3, hargs, hb0, hb1, hb2, hb3, hr⟩ := ProgramSem.of_50 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      obtain rfl := Rep.functional hb2 (Represents.congr h_a2 hn)
      obtain rfl := Rep.functional hb3 (Represents.congr h_a3 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_50 ⟨a0, a1, a2, a3, x_a0, x_a1, x_a2, x_a3, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, Rep.mono hpre h_a2, Rep.mono hpre h_a3, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24bv_5fshift_5fadd_5fmultiplier_5frec_spec m (ih m hm) s1 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24bv_5fshift_5fadd_5fmultiplier_5frec_5fstep_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) (hn_a4 : x_a4 ≠ Eo.Term.Stuck) :
    case_0_eo__24bv_5fshift_5fadd_5fmultiplier_5frec_5fstep s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__bv_shift_add_multiplier_rec_step.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__bv_shift_add_multiplier_rec_step.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24bv_5fshift_5fadd_5fmultiplier_5frec_5fstep
  have hG := Store.Grows.refl s
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s 0#u32 (0) (by scalar_tac) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4
  pat_same a2 v0 with h_a2 h_v0 using hinv1 else hinv1 hG in EoCases.__bv_shift_add_multiplier_rec_step.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s1 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v0
  pat_same a3 v1 with h_a3 h_v1 using hinv2 else hinv2 hG in EoCases.__bv_shift_add_multiplier_rec_step.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s2 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v0 h_v1
  case_done hinv3 hG with h_v2 in EoCases.__bv_shift_add_multiplier_rec_step.case_0 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4

theorem case_1_eo__24bv_5fshift_5fadd_5fmultiplier_5frec_5fstep_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) (hn_a4 : x_a4 ≠ Eo.Term.Stuck) :
    case_1_eo__24bv_5fshift_5fadd_5fmultiplier_5frec_5fstep s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__bv_shift_add_multiplier_rec_step.case_1 x_a0 x_a1 x_a2 x_a3 x_a4 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__bv_shift_add_multiplier_rec_step.case_1 x_a0 x_a1 x_a2 x_a3 x_a4 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24bv_5fshift_5fadd_5fmultiplier_5frec_5fstep more_0_eo__24bv_5fshift_5fadd_5fmultiplier_5frec_5fstep more_1_eo__24bv_5fshift_5fadd_5fmultiplier_5frec_5fstep more_2_eo__24bv_5fshift_5fadd_5fmultiplier_5frec_5fstep more_3_eo__24bv_5fshift_5fadd_5fmultiplier_5frec_5fstep more_4_eo__24bv_5fshift_5fadd_5fmultiplier_5frec_5fstep
  have hG := Store.Grows.refl s
  pat_unapply h_a1 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__bv_shift_add_multiplier_rec_step.case_1
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__bv_shift_add_multiplier_rec_step.case_1
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__bv_shift_add_multiplier_rec_step.case_1
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s1 0#u32 (0) (by scalar_tac) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6
  pat_same a2 v7 with h_a2 h_v7 using hinv2 else hinv2 hG in EoCases.__bv_shift_add_multiplier_rec_step.case_1
  pat_unapply h_a3 as ⟨v9, v10, x_v9, x_v10, h_v9, h_v10, hn_v9, hn_v10⟩ using hinv2 else hinv2 hG in EoCases.__bv_shift_add_multiplier_rec_step.case_1
  pat_unapply h_v9 as ⟨v12, v13, x_v12, x_v13, h_v12, h_v13, hn_v12, hn_v13⟩ using hinv2 else hinv2 hG in EoCases.__bv_shift_add_multiplier_rec_step.case_1
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s2 e_v14 (by rw [he_v14]; exact empty_args) hinv2 h64 as ⟨v14, s3, hinv3, h_v14⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v12 h_v13
  pat_same v12 v14 with h_v12 h_v14 using hinv3 else hinv3 hG in EoCases.__bv_shift_add_multiplier_rec_step.case_1
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s3 e_v15 (by rw [he_v15]; exact empty_args) hinv3 h64 as ⟨v15, s4, hinv4, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14
  step as ⟨e_v16, he_v16⟩
  store_step with CtorSpec.eo_xor.construct s4 e_v16 (by rw [he_v16]; exact empty_args) hinv4 h64 as ⟨v16, s5, hinv5, h_v16⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14 h_v15
  step as ⟨e_v17, he_v17⟩
  store_step with CtorSpec.eo_xor.construct s5 e_v17 (by rw [he_v17]; exact empty_args) hinv5 h64 as ⟨v17, s6, hinv6, h_v17⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14 h_v15 h_v16
  store_step with Store.apply_rep s6 v17 v13 _ _ hinv6 h64 h_v17 h_v13 (by ns_tac) (by ns_tac) as ⟨v18, s7, hinv7, h_v18⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17
  step as ⟨e_v19, he_v19⟩
  store_step with CtorSpec.eo_and.construct s7 e_v19 (by rw [he_v19]; exact empty_args) hinv7 h64 as ⟨v19, s8, hinv8, h_v19⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18
  store_step with Store.apply_rep s8 v19 a0 _ _ hinv8 h64 h_v19 h_a0 (by ns_tac) (by ns_tac) as ⟨v20, s9, hinv9, h_v20⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19
  step as ⟨e_v21, he_v21⟩
  store_step with CtorSpec.eo_and.construct s9 e_v21 (by rw [he_v21]; exact empty_args) hinv9 h64 as ⟨v21, s10, hinv10, h_v21⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20
  store_step with Store.apply_rep s10 v21 v5 _ _ hinv10 h64 h_v21 h_v5 (by ns_tac) (by ns_tac) as ⟨v22, s11, hinv11, h_v22⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21
  store_step with Store.literal_boolean_spec s11 true hinv11 h64 as ⟨v23, s12, hinv12, h_v23⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22
  store_step with Store.apply_rep s12 v22 v23 _ _ hinv12 h64 h_v22 h_v23 (by ns_tac) (by ns_tac) as ⟨v24, s13, hinv13, h_v24⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23
  store_step with Store.apply_rep s13 v20 v24 _ _ hinv13 h64 h_v20 h_v24 (by ns_tac) (by ns_tac) as ⟨v25, s14, hinv14, h_v25⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24
  store_step with Store.apply_rep s14 v18 v25 _ _ hinv14 h64 h_v18 h_v25 (by ns_tac) (by ns_tac) as ⟨v26, s15, hinv15, h_v26⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25
  store_step with Store.apply_rep s15 v16 v26 _ _ hinv15 h64 h_v16 h_v26 (by ns_tac) (by ns_tac) as ⟨v27, s16, hinv16, h_v27⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26
  store_step with Store.apply_rep s16 v27 a4 _ _ hinv16 h64 h_v27 h_a4 (by ns_tac) (by ns_tac) as ⟨v28, s17, hinv17, h_v28⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27
  store_step with Store.apply_rep s17 v15 v28 _ _ hinv17 h64 h_v15 h_v28 (by ns_tac) (by ns_tac) as ⟨v29, s18, hinv18, h_v29⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s18 0#u32 (0) (by scalar_tac) hinv18 h64 as ⟨v30, s19, hinv19, h_v30⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29
  step as ⟨e_v31, he_v31⟩
  store_step with CtorSpec.eo_or.construct s19 e_v31 (by rw [he_v31]; exact empty_args) hinv19 h64 as ⟨v31, s20, hinv20, h_v31⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30
  step as ⟨e_v32, he_v32⟩
  store_step with CtorSpec.eo_and.construct s20 e_v32 (by rw [he_v32]; exact empty_args) hinv20 h64 as ⟨v32, s21, hinv21, h_v32⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31
  store_step with Store.apply_rep s21 v32 v13 _ _ hinv21 h64 h_v32 h_v13 (by ns_tac) (by ns_tac) as ⟨v33, s22, hinv22, h_v33⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32
  step as ⟨e_v34, he_v34⟩
  store_step with CtorSpec.eo_and.construct s22 e_v34 (by rw [he_v34]; exact empty_args) hinv22 h64 as ⟨v34, s23, hinv23, h_v34⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33
  step as ⟨e_v35, he_v35⟩
  store_step with CtorSpec.eo_and.construct s23 e_v35 (by rw [he_v35]; exact empty_args) hinv23 h64 as ⟨v35, s24, hinv24, h_v35⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34
  store_step with Store.apply_rep s24 v35 a0 _ _ hinv24 h64 h_v35 h_a0 (by ns_tac) (by ns_tac) as ⟨v36, s25, hinv25, h_v36⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35
  step as ⟨e_v37, he_v37⟩
  store_step with CtorSpec.eo_and.construct s25 e_v37 (by rw [he_v37]; exact empty_args) hinv25 h64 as ⟨v37, s26, hinv26, h_v37⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36
  store_step with Store.apply_rep s26 v37 v5 _ _ hinv26 h64 h_v37 h_v5 (by ns_tac) (by ns_tac) as ⟨v38, s27, hinv27, h_v38⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37
  store_step with Store.literal_boolean_spec s27 true hinv27 h64 as ⟨v39, s28, hinv28, h_v39⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38
  store_step with Store.apply_rep s28 v38 v39 _ _ hinv28 h64 h_v38 h_v39 (by ns_tac) (by ns_tac) as ⟨v40, s29, hinv29, h_v40⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39
  store_step with Store.apply_rep s29 v36 v40 _ _ hinv29 h64 h_v36 h_v40 (by ns_tac) (by ns_tac) as ⟨v41, s30, hinv30, h_v41⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40
  store_step with Store.apply_rep s30 v34 v41 _ _ hinv30 h64 h_v34 h_v41 (by ns_tac) (by ns_tac) as ⟨v42, s31, hinv31, h_v42⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41
  store_step with Store.literal_boolean_spec s31 true hinv31 h64 as ⟨v43, s32, hinv32, h_v43⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42
  store_step with Store.apply_rep s32 v42 v43 _ _ hinv32 h64 h_v42 h_v43 (by ns_tac) (by ns_tac) as ⟨v44, s33, hinv33, h_v44⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43
  store_step with Store.apply_rep s33 v33 v44 _ _ hinv33 h64 h_v33 h_v44 (by ns_tac) (by ns_tac) as ⟨v45, s34, hinv34, h_v45⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44
  store_step with Store.apply_rep s34 v31 v45 _ _ hinv34 h64 h_v31 h_v45 (by ns_tac) (by ns_tac) as ⟨v46, s35, hinv35, h_v46⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45
  step as ⟨e_v47, he_v47⟩
  store_step with CtorSpec.eo_or.construct s35 e_v47 (by rw [he_v47]; exact empty_args) hinv35 h64 as ⟨v47, s36, hinv36, h_v47⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46
  step as ⟨e_v48, he_v48⟩
  store_step with CtorSpec.eo_and.construct s36 e_v48 (by rw [he_v48]; exact empty_args) hinv36 h64 as ⟨v48, s37, hinv37, h_v48⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47
  step as ⟨e_v49, he_v49⟩
  store_step with CtorSpec.eo_xor.construct s37 e_v49 (by rw [he_v49]; exact empty_args) hinv37 h64 as ⟨v49, s38, hinv38, h_v49⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48
  store_step with Store.apply_rep s38 v49 v13 _ _ hinv38 h64 h_v49 h_v13 (by ns_tac) (by ns_tac) as ⟨v50, s39, hinv39, h_v50⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49
  step as ⟨e_v51, he_v51⟩
  store_step with CtorSpec.eo_and.construct s39 e_v51 (by rw [he_v51]; exact empty_args) hinv39 h64 as ⟨v51, s40, hinv40, h_v51⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50
  store_step with Store.apply_rep s40 v51 a0 _ _ hinv40 h64 h_v51 h_a0 (by ns_tac) (by ns_tac) as ⟨v52, s41, hinv41, h_v52⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51
  step as ⟨e_v53, he_v53⟩
  store_step with CtorSpec.eo_and.construct s41 e_v53 (by rw [he_v53]; exact empty_args) hinv41 h64 as ⟨v53, s42, hinv42, h_v53⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52
  store_step with Store.apply_rep s42 v53 v5 _ _ hinv42 h64 h_v53 h_v5 (by ns_tac) (by ns_tac) as ⟨v54, s43, hinv43, h_v54⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53
  store_step with Store.literal_boolean_spec s43 true hinv43 h64 as ⟨v55, s44, hinv44, h_v55⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54
  store_step with Store.apply_rep s44 v54 v55 _ _ hinv44 h64 h_v54 h_v55 (by ns_tac) (by ns_tac) as ⟨v56, s45, hinv45, h_v56⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55
  store_step with Store.apply_rep s45 v52 v56 _ _ hinv45 h64 h_v52 h_v56 (by ns_tac) (by ns_tac) as ⟨v57, s46, hinv46, h_v57⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56
  store_step with Store.apply_rep s46 v50 v57 _ _ hinv46 h64 h_v50 h_v57 (by ns_tac) (by ns_tac) as ⟨v58, s47, hinv47, h_v58⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57
  store_step with Store.apply_rep s47 v48 v58 _ _ hinv47 h64 h_v48 h_v58 (by ns_tac) (by ns_tac) as ⟨v59, s48, hinv48, h_v59⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58
  step as ⟨e_v60, he_v60⟩
  store_step with CtorSpec.eo_and.construct s48 e_v60 (by rw [he_v60]; exact empty_args) hinv48 h64 as ⟨v60, s49, hinv49, h_v60⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59
  store_step with Store.apply_rep s49 v60 a4 _ _ hinv49 h64 h_v60 h_a4 (by ns_tac) (by ns_tac) as ⟨v61, s50, hinv50, h_v61⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60
  store_step with Store.literal_boolean_spec s50 true hinv50 h64 as ⟨v62, s51, hinv51, h_v62⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61
  store_step with Store.apply_rep s51 v61 v62 _ _ hinv51 h64 h_v61 h_v62 (by ns_tac) (by ns_tac) as ⟨v63, s52, hinv52, h_v63⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62
  store_step with Store.apply_rep s52 v59 v63 _ _ hinv52 h64 h_v59 h_v63 (by ns_tac) (by ns_tac) as ⟨v64, s53, hinv53, h_v64⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63
  store_step with Store.apply_rep s53 v47 v64 _ _ hinv53 h64 h_v47 h_v64 (by ns_tac) (by ns_tac) as ⟨v65, s54, hinv54, h_v65⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64
  store_step with Store.literal_boolean_spec s54 false hinv54 h64 as ⟨v66, s55, hinv55, h_v66⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65
  store_step with Store.apply_rep s55 v65 v66 _ _ hinv55 h64 h_v65 h_v66 (by ns_tac) (by ns_tac) as ⟨v67, s56, hinv56, h_v67⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66
  store_step with Store.apply_rep s56 v46 v67 _ _ hinv56 h64 h_v46 h_v67 (by ns_tac) (by ns_tac) as ⟨v68, s57, hinv57, h_v68⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67
  store_step with ih.eo__24bv_5fshift_5fadd_5fmultiplier_5frec_5fstep s57 a0 v2 v30 v10 v68 _ _ _ _ _ hinv57 h64 (hG.rem hrem) h_a0 h_v2 h_v30 h_v10 h_v68 as ⟨v69, s58, hinv58, h_v69⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68
  store_step with Store.apply_mk_rep s58 v29 v69 _ _ hinv58 h64 h_v29 h_v69 as ⟨v70, s59, hinv59, h_v70⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69
  case_done hinv59 hG with h_v70 in EoCases.__bv_shift_add_multiplier_rec_step.case_1 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_v1 hn_v2 hn_v4 hn_v5 hn_v9 hn_v10 hn_v12 hn_v13

theorem case_2_eo__24bv_5fshift_5fadd_5fmultiplier_5frec_5fstep_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) (hn_a4 : x_a4 ≠ Eo.Term.Stuck) :
    case_2_eo__24bv_5fshift_5fadd_5fmultiplier_5frec_5fstep s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__bv_shift_add_multiplier_rec_step.case_2 x_a0 x_a1 x_a2 x_a3 x_a4 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__bv_shift_add_multiplier_rec_step.case_2 x_a0 x_a1 x_a2 x_a3 x_a4 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24bv_5fshift_5fadd_5fmultiplier_5frec_5fstep
  have hG := Store.Grows.refl s
  pat_unapply h_a3 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__bv_shift_add_multiplier_rec_step.case_2
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__bv_shift_add_multiplier_rec_step.case_2
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__bv_shift_add_multiplier_rec_step.case_2
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s1 e_v7 (by rw [he_v7]; exact empty_args) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with Store.apply_rep s2 v7 v5 _ _ hinv2 h64 h_v7 h_v5 (by ns_tac) (by ns_tac) as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_neg_u32_spec s3 1#u32 (-1) (by scalar_tac) hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  step as ⟨e_v10, he_v10⟩
  store_step with Store.builtin_spec_add s4 e_v10 (by rw [he_v10]; rfl) h_a2 h_v9 hinv4 h64 as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  store_step with ih.eo__24bv_5fshift_5fadd_5fmultiplier_5frec_5fstep s5 a0 a1 v10 v2 a4 _ _ _ _ _ hinv5 h64 (hG.rem hrem) h_a0 h_a1 h_v10 h_v2 h_a4 as ⟨v11, s6, hinv6, h_v11⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
  store_step with Store.apply_mk_rep s6 v8 v11 _ _ hinv6 h64 h_v8 h_v11 as ⟨v12, s7, hinv7, h_v12⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11
  case_done hinv7 hG with h_v12 in EoCases.__bv_shift_add_multiplier_rec_step.case_2 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_v1 hn_v2 hn_v4 hn_v5

/-- logos's `__bv_shift_add_multiplier_rec_step` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24bv_5fshift_5fadd_5fmultiplier_5frec_5fstep.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) (hw_a4 : Valid.valid x_a4) :
    __bv_shift_add_multiplier_rec_step x_a0 x_a1 x_a2 x_a3 x_a4 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else if x_a4 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__bv_shift_add_multiplier_rec_step.case_0 x_a0 x_a1 x_a2 x_a3 x_a4, EoCases.__bv_shift_add_multiplier_rec_step.case_1 x_a0 x_a1 x_a2 x_a3 x_a4, EoCases.__bv_shift_add_multiplier_rec_step.case_2 x_a0 x_a1 x_a2 x_a3 x_a4] HasStuck.stuck) := by
  conv => lhs; unfold __bv_shift_add_multiplier_rec_step
  unfold EoCases.__bv_shift_add_multiplier_rec_step.case_0 EoCases.__bv_shift_add_multiplier_rec_step.case_1 EoCases.__bv_shift_add_multiplier_rec_step.case_2
  logos_eq

theorem body_eo__24bv_5fshift_5fadd_5fmultiplier_5frec_5fstep_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) :
    body_eo__24bv_5fshift_5fadd_5fmultiplier_5frec_5fstep s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__bv_shift_add_multiplier_rec_step x_a0 x_a1 x_a2 x_a3 x_a4)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24bv_5fshift_5fadd_5fmultiplier_5frec_5fstep.rust_eq x_a0 x_a1 x_a2 x_a3 x_a4 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3) (by valid_tac hinv h_a4)]
  unfold body_eo__24bv_5fshift_5fadd_5fmultiplier_5frec_5fstep
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  stuck_check h_a3 : x_a3 as hn_a3 else hinv hG
  stuck_check h_a4 : x_a4 as hn_a4 else hinv hG
  case_step with case_0_eo__24bv_5fshift_5fadd_5fmultiplier_5frec_5fstep_spec n ih s a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 hn_a0 hn_a1 hn_a2 hn_a3 hn_a4
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4
  case_step with case_1_eo__24bv_5fshift_5fadd_5fmultiplier_5frec_5fstep_spec n ih s1 a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 h_a3 h_a4 hn_a0 hn_a1 hn_a2 hn_a3 hn_a4
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hc0
  case_step with case_2_eo__24bv_5fshift_5fadd_5fmultiplier_5frec_5fstep_spec n ih s2 a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv2 h64 (hG.rem hrem) h_a0 h_a1 h_a2 h_a3 h_a4 hn_a0 hn_a1 hn_a2 hn_a3 hn_a4
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hc0 hc1
  body_stuck hinv3 hG using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hc0 hc1 hc2 in EoCases.__bv_shift_add_multiplier_rec_step.case_0 EoCases.__bv_shift_add_multiplier_rec_step.case_1 EoCases.__bv_shift_add_multiplier_rec_step.case_2

theorem eo__24bv_5fshift_5fadd_5fmultiplier_5frec_5fstep_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24bv_5fshift_5fadd_5fmultiplier_5frec_5fstep.Spec n := by
  intro s a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4
  unfold eo__24bv_5fshift_5fadd_5fmultiplier_5frec_5fstep
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 51#u32 _ [a0, a1, a2, a3, a4] rfl
    (fun s1 => body_eo__24bv_5fshift_5fadd_5fmultiplier_5frec_5fstep s1 a0 a1 a2 a3 a4) (fun s' t => Represents.rep s' t (__bv_shift_add_multiplier_rec_step x_a0 x_a1 x_a2 x_a3 x_a4))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, b2, b3, b4, y0, y1, y2, y3, y4, hargs, hb0, hb1, hb2, hb3, hb4, hr⟩ := ProgramSem.of_51 hsem
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
      exact ProgramSem.to_51 ⟨a0, a1, a2, a3, a4, x_a0, x_a1, x_a2, x_a3, x_a4, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, Rep.mono hpre h_a2, Rep.mono hpre h_a3, Rep.mono hpre h_a4, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24bv_5fshift_5fadd_5fmultiplier_5frec_5fstep_spec m (ih m hm) s1 a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn) (by congr_one h_a4 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24bv_5fsmulo_5felim_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) (hn_a4 : x_a4 ≠ Eo.Term.Stuck) (hn_a5 : x_a5 ≠ Eo.Term.Stuck) :
    case_0_eo__24bv_5fsmulo_5felim_5frec s a0 a1 a2 a3 a4 a5 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__bv_smulo_elim_rec.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _) (u3 : Term) (y3 : _) (u4 : Term) (y4 : _) (u5 : Term) (y5 : _), arr.val = [u0, u1, u2, u3, u4, u5] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧ Represents.rep s' u3 y3 ∧ Represents.rep s' u4 y4 ∧ Represents.rep s' u5 y5 ∧
          EoCases.__bv_smulo_elim_rec.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 = some (__bv_smulo_elim_rec y0 y1 y2 y3 y4 y5)
      | core.result.Result.Ok none => EoCases.__bv_smulo_elim_rec.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24bv_5fsmulo_5felim_5frec
  have hG := Store.Grows.refl s
  pat_unapply h_a4 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__bv_smulo_elim_rec.case_0
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__40_40TypedList_2enil.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__bv_smulo_elim_rec.case_0
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo_Int.construct s1 e_v4 (by rw [he_v4]; exact empty_args) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v3
  pat_same v2 v4 with h_v2 h_v4 using hinv2 else hinv2 hG in EoCases.__bv_smulo_elim_rec.case_0
  case_done hinv2 hG with h_a3 in EoCases.__bv_smulo_elim_rec.case_0 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_a5 hn_v1 hn_v2

theorem case_1_eo__24bv_5fsmulo_5felim_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) (hn_a4 : x_a4 ≠ Eo.Term.Stuck) (hn_a5 : x_a5 ≠ Eo.Term.Stuck) :
    case_1_eo__24bv_5fsmulo_5felim_5frec s a0 a1 a2 a3 a4 a5 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__bv_smulo_elim_rec.case_1 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _) (u3 : Term) (y3 : _) (u4 : Term) (y4 : _) (u5 : Term) (y5 : _), arr.val = [u0, u1, u2, u3, u4, u5] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧ Represents.rep s' u3 y3 ∧ Represents.rep s' u4 y4 ∧ Represents.rep s' u5 y5 ∧
          EoCases.__bv_smulo_elim_rec.case_1 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 = some (__bv_smulo_elim_rec y0 y1 y2 y3 y4 y5)
      | core.result.Result.Ok none => EoCases.__bv_smulo_elim_rec.case_1 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24bv_5fsmulo_5felim_5frec more_0_eo__24bv_5fsmulo_5felim_5frec more_1_eo__24bv_5fsmulo_5felim_5frec more_2_eo__24bv_5fsmulo_5felim_5frec more_3_eo__24bv_5fsmulo_5felim_5frec
  have hG := Store.Grows.refl s
  pat_unapply h_a4 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__bv_smulo_elim_rec.case_1
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__bv_smulo_elim_rec.case_1
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__40_40TypedList_2econs.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__bv_smulo_elim_rec.case_1
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo_bvor.construct s1 e_v7 (by rw [he_v7]; exact empty_args) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with Store.apply_rep s2 v7 a2 _ _ hinv2 h64 h_v7 h_a2 (by ns_tac) (by ns_tac) as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_bvor.construct s3 e_v9 (by rw [he_v9]; exact empty_args) hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  step as ⟨e_v10, he_v10⟩
  store_step with Store.builtin_spec_neg s4 e_v10 (by rw [he_v10]; rfl) h_v5 hinv4 h64 as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  step as ⟨e_v11, he_v11⟩
  store_step with Store.builtin_spec_add s5 e_v11 (by rw [he_v11]; rfl) h_a5 h_v10 hinv5 h64 as ⟨v11, s6, hinv6, h_v11⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
  step as ⟨e_v12, he_v12⟩
  store_step with Store.builtin_spec_neg s6 e_v12 (by rw [he_v12]; rfl) h_v5 hinv6 h64 as ⟨v12, s7, hinv7, h_v12⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11
  step as ⟨e_v13, he_v13⟩
  store_step with Store.builtin_spec_add s7 e_v13 (by rw [he_v13]; rfl) h_a5 h_v12 hinv7 h64 as ⟨v13, s8, hinv8, h_v13⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo_extract.construct s8 e_v14 (by rw [he_v14]; rfl) h_v11 h_v13 hinv8 h64 as ⟨v14, s9, hinv9, h_v14⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13
  store_step with Store.apply_mk_rep s9 v14 a0 _ _ hinv9 h64 h_v14 h_a0 as ⟨v15, s10, hinv10, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14
  store_step with Store.apply_mk_rep s10 v9 v15 _ _ hinv10 h64 h_v9 h_v15 as ⟨v16, s11, hinv11, h_v16⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s11 1#u32 0#u32 (1) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv11 h64 as ⟨v17, s12, hinv12, h_v17⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16
  store_step with Store.apply_mk_rep s12 v16 v17 _ _ hinv12 h64 h_v16 h_v17 as ⟨v18, s13, hinv13, h_v18⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17
  store_step with Store.apply_mk_rep s13 v8 v18 _ _ hinv13 h64 h_v8 h_v18 as ⟨v19, s14, hinv14, h_v19⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18
  step as ⟨e_v20, he_v20⟩
  store_step with CtorSpec.eo_bvor.construct s14 e_v20 (by rw [he_v20]; exact empty_args) hinv14 h64 as ⟨v20, s15, hinv15, h_v20⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19
  store_step with Store.apply_rep s15 v20 a3 _ _ hinv15 h64 h_v20 h_a3 (by ns_tac) (by ns_tac) as ⟨v21, s16, hinv16, h_v21⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20
  step as ⟨e_v22, he_v22⟩
  store_step with CtorSpec.eo_bvor.construct s16 e_v22 (by rw [he_v22]; exact empty_args) hinv16 h64 as ⟨v22, s17, hinv17, h_v22⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21
  step as ⟨e_v23, he_v23⟩
  store_step with CtorSpec.eo_bvand.construct s17 e_v23 (by rw [he_v23]; exact empty_args) hinv17 h64 as ⟨v23, s18, hinv18, h_v23⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s18 1#u32 (1) (by scalar_tac) hinv18 h64 as ⟨v24, s19, hinv19, h_v24⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23
  step as ⟨e_v25, he_v25⟩
  store_step with Store.builtin_spec_add s19 e_v25 (by rw [he_v25]; rfl) h_v5 h_v24 hinv19 h64 as ⟨v25, s20, hinv20, h_v25⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s20 1#u32 (1) (by scalar_tac) hinv20 h64 as ⟨v26, s21, hinv21, h_v26⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25
  step as ⟨e_v27, he_v27⟩
  store_step with Store.builtin_spec_add s21 e_v27 (by rw [he_v27]; rfl) h_v5 h_v26 hinv21 h64 as ⟨v27, s22, hinv22, h_v27⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26
  step as ⟨e_v28, he_v28⟩
  store_step with CtorSpec.eo_extract.construct s22 e_v28 (by rw [he_v28]; rfl) h_v25 h_v27 hinv22 h64 as ⟨v28, s23, hinv23, h_v28⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27
  store_step with Store.apply_mk_rep s23 v28 a1 _ _ hinv23 h64 h_v28 h_a1 as ⟨v29, s24, hinv24, h_v29⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28
  store_step with Store.apply_mk_rep s24 v23 v29 _ _ hinv24 h64 h_v23 h_v29 as ⟨v30, s25, hinv25, h_v30⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29
  step as ⟨e_v31, he_v31⟩
  store_step with CtorSpec.eo_bvand.construct s25 e_v31 (by rw [he_v31]; exact empty_args) hinv25 h64 as ⟨v31, s26, hinv26, h_v31⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30
  step as ⟨e_v32, he_v32⟩
  store_step with CtorSpec.eo_bvor.construct s26 e_v32 (by rw [he_v32]; exact empty_args) hinv26 h64 as ⟨v32, s27, hinv27, h_v32⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31
  store_step with Store.apply_rep s27 v32 a2 _ _ hinv27 h64 h_v32 h_a2 (by ns_tac) (by ns_tac) as ⟨v33, s28, hinv28, h_v33⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32
  step as ⟨e_v34, he_v34⟩
  store_step with CtorSpec.eo_bvor.construct s28 e_v34 (by rw [he_v34]; exact empty_args) hinv28 h64 as ⟨v34, s29, hinv29, h_v34⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33
  step as ⟨e_v35, he_v35⟩
  store_step with Store.builtin_spec_neg s29 e_v35 (by rw [he_v35]; rfl) h_v5 hinv29 h64 as ⟨v35, s30, hinv30, h_v35⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34
  step as ⟨e_v36, he_v36⟩
  store_step with Store.builtin_spec_add s30 e_v36 (by rw [he_v36]; rfl) h_a5 h_v35 hinv30 h64 as ⟨v36, s31, hinv31, h_v36⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35
  step as ⟨e_v37, he_v37⟩
  store_step with Store.builtin_spec_neg s31 e_v37 (by rw [he_v37]; rfl) h_v5 hinv31 h64 as ⟨v37, s32, hinv32, h_v37⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36
  step as ⟨e_v38, he_v38⟩
  store_step with Store.builtin_spec_add s32 e_v38 (by rw [he_v38]; rfl) h_a5 h_v37 hinv32 h64 as ⟨v38, s33, hinv33, h_v38⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37
  step as ⟨e_v39, he_v39⟩
  store_step with CtorSpec.eo_extract.construct s33 e_v39 (by rw [he_v39]; rfl) h_v36 h_v38 hinv33 h64 as ⟨v39, s34, hinv34, h_v39⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38
  store_step with Store.apply_mk_rep s34 v39 a0 _ _ hinv34 h64 h_v39 h_a0 as ⟨v40, s35, hinv35, h_v40⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39
  store_step with Store.apply_mk_rep s35 v34 v40 _ _ hinv35 h64 h_v34 h_v40 as ⟨v41, s36, hinv36, h_v41⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s36 1#u32 0#u32 (1) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv36 h64 as ⟨v42, s37, hinv37, h_v42⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41
  store_step with Store.apply_mk_rep s37 v41 v42 _ _ hinv37 h64 h_v41 h_v42 as ⟨v43, s38, hinv38, h_v43⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42
  store_step with Store.apply_mk_rep s38 v33 v43 _ _ hinv38 h64 h_v33 h_v43 as ⟨v44, s39, hinv39, h_v44⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43
  store_step with Store.apply_mk_rep s39 v31 v44 _ _ hinv39 h64 h_v31 h_v44 as ⟨v45, s40, hinv40, h_v45⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44
  step as ⟨e_v46, he_v46⟩
  store_step with CtorSpec.eo_bvand.construct s40 e_v46 (by rw [he_v46]; exact empty_args) hinv40 h64 as ⟨v46, s41, hinv41, h_v46⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s41 1#u32 (1) (by scalar_tac) hinv41 h64 as ⟨v47, s42, hinv42, h_v47⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46
  step as ⟨e_v48, he_v48⟩
  store_step with Store.builtin_spec_add s42 e_v48 (by rw [he_v48]; rfl) h_v5 h_v47 hinv42 h64 as ⟨v48, s43, hinv43, h_v48⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s43 1#u32 (1) (by scalar_tac) hinv43 h64 as ⟨v49, s44, hinv44, h_v49⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48
  step as ⟨e_v50, he_v50⟩
  store_step with Store.builtin_spec_add s44 e_v50 (by rw [he_v50]; rfl) h_v5 h_v49 hinv44 h64 as ⟨v50, s45, hinv45, h_v50⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49
  step as ⟨e_v51, he_v51⟩
  store_step with CtorSpec.eo_extract.construct s45 e_v51 (by rw [he_v51]; rfl) h_v48 h_v50 hinv45 h64 as ⟨v51, s46, hinv46, h_v51⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50
  store_step with Store.apply_mk_rep s46 v51 a1 _ _ hinv46 h64 h_v51 h_a1 as ⟨v52, s47, hinv47, h_v52⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51
  store_step with ih.eo__24eo_5ftypeof s47 v52 _ hinv47 h64 (hG.rem hrem) h_v52 as ⟨v53, s48, hinv48, h_v53⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52
  store_step with ih.eo__24eo_5fnil s48 v46 v53 _ _ hinv48 h64 (hG.rem hrem) h_v46 h_v53 as ⟨v54, s49, hinv49, h_v54⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53
  store_step with Store.apply_mk_rep s49 v45 v54 _ _ hinv49 h64 h_v45 h_v54 as ⟨v55, s50, hinv50, h_v55⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54
  store_step with Store.apply_mk_rep s50 v30 v55 _ _ hinv50 h64 h_v30 h_v55 as ⟨v56, s51, hinv51, h_v56⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55
  store_step with Store.apply_mk_rep s51 v22 v56 _ _ hinv51 h64 h_v22 h_v56 as ⟨v57, s52, hinv52, h_v57⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s52 1#u32 0#u32 (1) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv52 h64 as ⟨v58, s53, hinv53, h_v58⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57
  store_step with Store.apply_mk_rep s53 v57 v58 _ _ hinv53 h64 h_v57 h_v58 as ⟨v59, s54, hinv54, h_v59⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58
  store_step with Store.apply_mk_rep s54 v21 v59 _ _ hinv54 h64 h_v21 h_v59 as ⟨v60, s55, hinv55, h_v60⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59
  case_again hinv55 hG with h_a0 h_a1 h_v19 h_v60 h_v2 h_a5 in EoCases.__bv_smulo_elim_rec.case_1 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_a5 hn_v1 hn_v2 hn_v4 hn_v5

/-- logos's `__bv_smulo_elim_rec` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24bv_5fsmulo_5felim_5frec.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) (hw_a4 : Valid.valid x_a4) (hw_a5 : Valid.valid x_a5) :
    __bv_smulo_elim_rec x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else if x_a4 = Eo.Term.Stuck then HasStuck.stuck else if x_a5 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__bv_smulo_elim_rec.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5, EoCases.__bv_smulo_elim_rec.case_1 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5] HasStuck.stuck) := by
  conv => lhs; unfold __bv_smulo_elim_rec
  unfold EoCases.__bv_smulo_elim_rec.case_0 EoCases.__bv_smulo_elim_rec.case_1
  logos_eq

theorem step_eo__24bv_5fsmulo_5felim_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) :
    step_eo__24bv_5fsmulo_5felim_5frec s a0 a1 a2 a3 a4 a5 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (Next.Done t) => Represents.rep s' t (__bv_smulo_elim_rec x_a0 x_a1 x_a2 x_a3 x_a4 x_a5)
      | core.result.Result.Ok (Next.Again arr) =>
        s'.budget < s.budget ∧ ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _) (u3 : Term) (y3 : _) (u4 : Term) (y4 : _) (u5 : Term) (y5 : _), arr.val = [u0, u1, u2, u3, u4, u5] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧ Represents.rep s' u3 y3 ∧ Represents.rep s' u4 y4 ∧ Represents.rep s' u5 y5 ∧
          __bv_smulo_elim_rec x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 = __bv_smulo_elim_rec y0 y1 y2 y3 y4 y5
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24bv_5fsmulo_5felim_5frec.rust_eq x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3) (by valid_tac hinv h_a4) (by valid_tac hinv h_a5)]
  unfold step_eo__24bv_5fsmulo_5felim_5frec
  have hG := Store.Grows.refl s
  tick_step as ⟨s1, hinv1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5
  stuck_check h_a0 : x_a0 as hn_a0 else hinv1 hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv1 hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv1 hG
  stuck_check h_a3 : x_a3 as hn_a3 else hinv1 hG
  stuck_check h_a4 : x_a4 as hn_a4 else hinv1 hG
  stuck_check h_a5 : x_a5 as hn_a5 else hinv1 hG
  round_step with case_0_eo__24bv_5fsmulo_5felim_5frec_spec n ih s1 a0 a1 a2 a3 a4 a5 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_a5
    as ⟨s2, hinv2, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 hbud using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_a5
  round_step with case_1_eo__24bv_5fsmulo_5felim_5frec_spec n ih s2 a0 a1 a2 a3 a4 a5 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 hinv2 h64 (hG.rem hrem) h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_a5
    as ⟨s3, hinv3, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 hbud using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_a5 hc0
  round_stuck hinv3 hG using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_a5 hc0 hc1 in EoCases.__bv_smulo_elim_rec.case_0 EoCases.__bv_smulo_elim_rec.case_1

theorem body_eo__24bv_5fsmulo_5felim_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) :
    body_eo__24bv_5fsmulo_5felim_5frec s a0 a1 a2 a3 a4 a5 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__bv_smulo_elim_rec x_a0 x_a1 x_a2 x_a3 x_a4 x_a5)
      | core.result.Result.Err _ => True ⦄div := by
  refine (?_ : ∀ (k : Nat) (a0 a1 a2 a3 a4 a5 : Term) (s : Store) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _), s.budget ≤ k → s.Inv → s.remaining ≤ n →
      Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 → Represents.rep s a4 x_a4 → Represents.rep s a5 x_a5 →
      body_eo__24bv_5fsmulo_5felim_5frec s a0 a1 a2 a3 a4 a5 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__bv_smulo_elim_rec x_a0 x_a1 x_a2 x_a3 x_a4 x_a5)
      | core.result.Result.Err _ => True ⦄div) s.budget a0 a1 a2 a3 a4 a5 s x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 le_rfl hinv hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5
  intro k
  refine Nat.strong_induction_on k ?_
  intro k ihl a0 a1 a2 a3 a4 a5 s x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 hk hinv hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5
  unfold body_eo__24bv_5fsmulo_5felim_5frec body_eo__24bv_5fsmulo_5felim_5frec_loop
  step with step_eo__24bv_5fsmulo_5felim_5frec_spec n ih s a0 a1 a2 a3 a4 a5 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 as ⟨r, s1, hinv1, hg1, hr⟩
  cases r with
  | Err e => simp only [WP.dspec_ok, WP.uncurry'_pair]; exact ⟨hinv1, hg1, trivial⟩
  | Ok nx =>
    cases nx with
    | Done value =>
      simp only [WP.dspec_ok, WP.uncurry'_pair]
      exact ⟨hinv1, hg1, hr⟩
    | Again next =>
      obtain ⟨hlt, u0, y0, u1, y1, u2, y2, u3, y3, u4, y4, u5, y5, hnext, hrep0, hrep1, hrep2, hrep3, hrep4, hrep5, heq⟩ := hr
      simp only
      have hlen : next.length = 6 := by simp [Array.length, hnext]
      step as ⟨b0, hb0⟩
      obtain rfl : b0 = u0 := by simp [hb0, hnext]
      step as ⟨b1, hb1⟩
      obtain rfl : b1 = u1 := by simp [hb1, hnext]
      step as ⟨b2, hb2⟩
      obtain rfl : b2 = u2 := by simp [hb2, hnext]
      step as ⟨b3, hb3⟩
      obtain rfl : b3 = u3 := by simp [hb3, hnext]
      step as ⟨b4, hb4⟩
      obtain rfl : b4 = u4 := by simp [hb4, hnext]
      step as ⟨b5, hb5⟩
      obtain rfl : b5 = u5 := by simp [hb5, hnext]
      have hrec := ihl s1.budget (by omega) b0 b1 b2 b3 b4 b5 s1 y0 y1 y2 y3 y4 y5 le_rfl hinv1 (hg1.rem hrem)  hrep0  hrep1  hrep2  hrep3  hrep4  hrep5
      unfold body_eo__24bv_5fsmulo_5felim_5frec at hrec
      apply WP.dspec_mono hrec
      loop_close hg1 heq

theorem eo__24bv_5fsmulo_5felim_5frec_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24bv_5fsmulo_5felim_5frec.Spec n := by
  intro s a0 a1 a2 a3 a4 a5 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5
  unfold eo__24bv_5fsmulo_5felim_5frec
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 52#u32 _ [a0, a1, a2, a3, a4, a5] rfl
    (fun s1 => body_eo__24bv_5fsmulo_5felim_5frec s1 a0 a1 a2 a3 a4 a5) (fun s' t => Represents.rep s' t (__bv_smulo_elim_rec x_a0 x_a1 x_a2 x_a3 x_a4 x_a5))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, b2, b3, b4, b5, y0, y1, y2, y3, y4, y5, hargs, hb0, hb1, hb2, hb3, hb4, hb5, hr⟩ := ProgramSem.of_52 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      obtain rfl := Rep.functional hb2 (Represents.congr h_a2 hn)
      obtain rfl := Rep.functional hb3 (Represents.congr h_a3 hn)
      obtain rfl := Rep.functional hb4 (Represents.congr h_a4 hn)
      obtain rfl := Rep.functional hb5 (Represents.congr h_a5 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_52 ⟨a0, a1, a2, a3, a4, a5, x_a0, x_a1, x_a2, x_a3, x_a4, x_a5, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, Rep.mono hpre h_a2, Rep.mono hpre h_a3, Rep.mono hpre h_a4, Rep.mono hpre h_a5, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24bv_5fsmulo_5felim_5frec_spec m (ih m hm) s1 a0 a1 a2 a3 a4 a5 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn) (by congr_one h_a4 hn) (by congr_one h_a5 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24bv_5fumulo_5felim_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) (hn_a4 : x_a4 ≠ Eo.Term.Stuck) (hn_a5 : x_a5 ≠ Eo.Term.Stuck) :
    case_0_eo__24bv_5fumulo_5felim_5frec s a0 a1 a2 a3 a4 a5 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__bv_umulo_elim_rec.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__bv_umulo_elim_rec.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24bv_5fumulo_5felim_5frec
  have hG := Store.Grows.refl s
  pat_unapply h_a4 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__bv_umulo_elim_rec.case_0
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__40_40TypedList_2enil.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__bv_umulo_elim_rec.case_0
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo_Int.construct s1 e_v4 (by rw [he_v4]; exact empty_args) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v3
  pat_same v2 v4 with h_v2 h_v4 using hinv2 else hinv2 hG in EoCases.__bv_umulo_elim_rec.case_0
  case_done hinv2 hG with h_a3 in EoCases.__bv_umulo_elim_rec.case_0 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_a5 hn_v1 hn_v2

theorem case_1_eo__24bv_5fumulo_5felim_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) (hn_a4 : x_a4 ≠ Eo.Term.Stuck) (hn_a5 : x_a5 ≠ Eo.Term.Stuck) :
    case_1_eo__24bv_5fumulo_5felim_5frec s a0 a1 a2 a3 a4 a5 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__bv_umulo_elim_rec.case_1 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__bv_umulo_elim_rec.case_1 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24bv_5fumulo_5felim_5frec more_0_eo__24bv_5fumulo_5felim_5frec more_1_eo__24bv_5fumulo_5felim_5frec more_2_eo__24bv_5fumulo_5felim_5frec more_3_eo__24bv_5fumulo_5felim_5frec
  have hG := Store.Grows.refl s
  pat_unapply h_a4 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__bv_umulo_elim_rec.case_1
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__bv_umulo_elim_rec.case_1
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__40_40TypedList_2econs.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__bv_umulo_elim_rec.case_1
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo_bvor.construct s1 e_v7 (by rw [he_v7]; exact empty_args) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo_bvand.construct s2 e_v8 (by rw [he_v8]; exact empty_args) hinv2 h64 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_extract.construct s3 e_v9 (by rw [he_v9]; rfl) h_v5 h_v5 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  store_step with Store.apply_rep s4 v9 a1 _ _ hinv4 h64 h_v9 h_a1 (by ns_tac) (by ns_tac) as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  store_step with Store.apply_rep s5 v8 v10 _ _ hinv5 h64 h_v8 h_v10 (by ns_tac) (by ns_tac) as ⟨v11, s6, hinv6, h_v11⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo_bvand.construct s6 e_v12 (by rw [he_v12]; exact empty_args) hinv6 h64 as ⟨v12, s7, hinv7, h_v12⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11
  store_step with Store.apply_rep s7 v12 a2 _ _ hinv7 h64 h_v12 h_a2 (by ns_tac) (by ns_tac) as ⟨v13, s8, hinv8, h_v13⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo_bvand.construct s8 e_v14 (by rw [he_v14]; exact empty_args) hinv8 h64 as ⟨v14, s9, hinv9, h_v14⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo_extract.construct s9 e_v15 (by rw [he_v15]; rfl) h_v5 h_v5 hinv9 h64 as ⟨v15, s10, hinv10, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14
  store_step with Store.apply_rep s10 v15 a1 _ _ hinv10 h64 h_v15 h_a1 (by ns_tac) (by ns_tac) as ⟨v16, s11, hinv11, h_v16⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15
  store_step with ih.eo__24eo_5ftypeof s11 v16 _ hinv11 h64 (hG.rem hrem) h_v16 as ⟨v17, s12, hinv12, h_v17⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16
  store_step with ih.eo__24eo_5fnil s12 v14 v17 _ _ hinv12 h64 (hG.rem hrem) h_v14 h_v17 as ⟨v18, s13, hinv13, h_v18⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17
  store_step with Store.apply_mk_rep s13 v13 v18 _ _ hinv13 h64 h_v13 h_v18 as ⟨v19, s14, hinv14, h_v19⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18
  store_step with Store.apply_mk_rep s14 v11 v19 _ _ hinv14 h64 h_v11 h_v19 as ⟨v20, s15, hinv15, h_v20⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19
  store_step with Store.apply_mk_rep s15 v7 v20 _ _ hinv15 h64 h_v7 h_v20 as ⟨v21, s16, hinv16, h_v21⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20
  step as ⟨e_v22, he_v22⟩
  store_step with CtorSpec.eo_bvor.construct s16 e_v22 (by rw [he_v22]; exact empty_args) hinv16 h64 as ⟨v22, s17, hinv17, h_v22⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_neg_u32_spec s17 1#u32 (-1) (by scalar_tac) hinv17 h64 as ⟨v23, s18, hinv18, h_v23⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22
  step as ⟨e_v24, he_v24⟩
  store_step with Store.builtin_spec_add s18 e_v24 (by rw [he_v24]; rfl) h_a5 h_v23 hinv18 h64 as ⟨v24, s19, hinv19, h_v24⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23
  step as ⟨e_v25, he_v25⟩
  store_step with Store.builtin_spec_neg s19 e_v25 (by rw [he_v25]; rfl) h_v5 hinv19 h64 as ⟨v25, s20, hinv20, h_v25⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24
  step as ⟨e_v26, he_v26⟩
  store_step with Store.builtin_spec_add s20 e_v26 (by rw [he_v26]; rfl) h_v24 h_v25 hinv20 h64 as ⟨v26, s21, hinv21, h_v26⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_neg_u32_spec s21 1#u32 (-1) (by scalar_tac) hinv21 h64 as ⟨v27, s22, hinv22, h_v27⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26
  step as ⟨e_v28, he_v28⟩
  store_step with Store.builtin_spec_add s22 e_v28 (by rw [he_v28]; rfl) h_a5 h_v27 hinv22 h64 as ⟨v28, s23, hinv23, h_v28⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27
  step as ⟨e_v29, he_v29⟩
  store_step with Store.builtin_spec_neg s23 e_v29 (by rw [he_v29]; rfl) h_v5 hinv23 h64 as ⟨v29, s24, hinv24, h_v29⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28
  step as ⟨e_v30, he_v30⟩
  store_step with Store.builtin_spec_add s24 e_v30 (by rw [he_v30]; rfl) h_v28 h_v29 hinv24 h64 as ⟨v30, s25, hinv25, h_v30⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29
  step as ⟨e_v31, he_v31⟩
  store_step with CtorSpec.eo_extract.construct s25 e_v31 (by rw [he_v31]; rfl) h_v26 h_v30 hinv25 h64 as ⟨v31, s26, hinv26, h_v31⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30
  store_step with Store.apply_mk_rep s26 v31 a0 _ _ hinv26 h64 h_v31 h_a0 as ⟨v32, s27, hinv27, h_v32⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31
  store_step with Store.apply_mk_rep s27 v22 v32 _ _ hinv27 h64 h_v22 h_v32 as ⟨v33, s28, hinv28, h_v33⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32
  step as ⟨e_v34, he_v34⟩
  store_step with CtorSpec.eo_bvor.construct s28 e_v34 (by rw [he_v34]; exact empty_args) hinv28 h64 as ⟨v34, s29, hinv29, h_v34⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33
  store_step with Store.apply_rep s29 v34 a2 _ _ hinv29 h64 h_v34 h_a2 (by ns_tac) (by ns_tac) as ⟨v35, s30, hinv30, h_v35⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34
  step as ⟨e_v36, he_v36⟩
  store_step with CtorSpec.eo_bvor.construct s30 e_v36 (by rw [he_v36]; exact empty_args) hinv30 h64 as ⟨v36, s31, hinv31, h_v36⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_neg_u32_spec s31 1#u32 (-1) (by scalar_tac) hinv31 h64 as ⟨v37, s32, hinv32, h_v37⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36
  step as ⟨e_v38, he_v38⟩
  store_step with Store.builtin_spec_add s32 e_v38 (by rw [he_v38]; rfl) h_a5 h_v37 hinv32 h64 as ⟨v38, s33, hinv33, h_v38⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37
  step as ⟨e_v39, he_v39⟩
  store_step with Store.builtin_spec_neg s33 e_v39 (by rw [he_v39]; rfl) h_v5 hinv33 h64 as ⟨v39, s34, hinv34, h_v39⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38
  step as ⟨e_v40, he_v40⟩
  store_step with Store.builtin_spec_add s34 e_v40 (by rw [he_v40]; rfl) h_v38 h_v39 hinv34 h64 as ⟨v40, s35, hinv35, h_v40⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_neg_u32_spec s35 1#u32 (-1) (by scalar_tac) hinv35 h64 as ⟨v41, s36, hinv36, h_v41⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40
  step as ⟨e_v42, he_v42⟩
  store_step with Store.builtin_spec_add s36 e_v42 (by rw [he_v42]; rfl) h_a5 h_v41 hinv36 h64 as ⟨v42, s37, hinv37, h_v42⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41
  step as ⟨e_v43, he_v43⟩
  store_step with Store.builtin_spec_neg s37 e_v43 (by rw [he_v43]; rfl) h_v5 hinv37 h64 as ⟨v43, s38, hinv38, h_v43⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42
  step as ⟨e_v44, he_v44⟩
  store_step with Store.builtin_spec_add s38 e_v44 (by rw [he_v44]; rfl) h_v42 h_v43 hinv38 h64 as ⟨v44, s39, hinv39, h_v44⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43
  step as ⟨e_v45, he_v45⟩
  store_step with CtorSpec.eo_extract.construct s39 e_v45 (by rw [he_v45]; rfl) h_v40 h_v44 hinv39 h64 as ⟨v45, s40, hinv40, h_v45⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44
  store_step with Store.apply_mk_rep s40 v45 a0 _ _ hinv40 h64 h_v45 h_a0 as ⟨v46, s41, hinv41, h_v46⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45
  store_step with ih.eo__24eo_5ftypeof s41 v46 _ hinv41 h64 (hG.rem hrem) h_v46 as ⟨v47, s42, hinv42, h_v47⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46
  store_step with ih.eo__24eo_5fnil s42 v36 v47 _ _ hinv42 h64 (hG.rem hrem) h_v36 h_v47 as ⟨v48, s43, hinv43, h_v48⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47
  store_step with Store.apply_mk_rep s43 v35 v48 _ _ hinv43 h64 h_v35 h_v48 as ⟨v49, s44, hinv44, h_v49⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48
  store_step with Store.apply_mk_rep s44 v33 v49 _ _ hinv44 h64 h_v33 h_v49 as ⟨v50, s45, hinv45, h_v50⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49
  store_step with ih.eo__24bv_5fumulo_5felim_5frec s45 a0 a1 v50 a3 v2 a5 _ _ _ _ _ _ hinv45 h64 (hG.rem hrem) h_a0 h_a1 h_v50 h_a3 h_v2 h_a5 as ⟨v51, s46, hinv46, h_v51⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50
  store_step with Store.apply_mk_rep s46 v21 v51 _ _ hinv46 h64 h_v21 h_v51 as ⟨v52, s47, hinv47, h_v52⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51
  case_done hinv47 hG with h_v52 in EoCases.__bv_umulo_elim_rec.case_1 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_a5 hn_v1 hn_v2 hn_v4 hn_v5

/-- logos's `__bv_umulo_elim_rec` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24bv_5fumulo_5felim_5frec.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) (hw_a4 : Valid.valid x_a4) (hw_a5 : Valid.valid x_a5) :
    __bv_umulo_elim_rec x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else if x_a4 = Eo.Term.Stuck then HasStuck.stuck else if x_a5 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__bv_umulo_elim_rec.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5, EoCases.__bv_umulo_elim_rec.case_1 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5] HasStuck.stuck) := by
  conv => lhs; unfold __bv_umulo_elim_rec
  unfold EoCases.__bv_umulo_elim_rec.case_0 EoCases.__bv_umulo_elim_rec.case_1
  logos_eq

theorem body_eo__24bv_5fumulo_5felim_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) :
    body_eo__24bv_5fumulo_5felim_5frec s a0 a1 a2 a3 a4 a5 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__bv_umulo_elim_rec x_a0 x_a1 x_a2 x_a3 x_a4 x_a5)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24bv_5fumulo_5felim_5frec.rust_eq x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3) (by valid_tac hinv h_a4) (by valid_tac hinv h_a5)]
  unfold body_eo__24bv_5fumulo_5felim_5frec
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  stuck_check h_a3 : x_a3 as hn_a3 else hinv hG
  stuck_check h_a4 : x_a4 as hn_a4 else hinv hG
  stuck_check h_a5 : x_a5 as hn_a5 else hinv hG
  case_step with case_0_eo__24bv_5fumulo_5felim_5frec_spec n ih s a0 a1 a2 a3 a4 a5 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_a5
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_a5
  case_step with case_1_eo__24bv_5fumulo_5felim_5frec_spec n ih s1 a0 a1 a2 a3 a4 a5 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_a5
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_a5 hc0
  body_stuck hinv2 hG using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_a5 hc0 hc1 in EoCases.__bv_umulo_elim_rec.case_0 EoCases.__bv_umulo_elim_rec.case_1

theorem eo__24bv_5fumulo_5felim_5frec_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24bv_5fumulo_5felim_5frec.Spec n := by
  intro s a0 a1 a2 a3 a4 a5 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5
  unfold eo__24bv_5fumulo_5felim_5frec
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 53#u32 _ [a0, a1, a2, a3, a4, a5] rfl
    (fun s1 => body_eo__24bv_5fumulo_5felim_5frec s1 a0 a1 a2 a3 a4 a5) (fun s' t => Represents.rep s' t (__bv_umulo_elim_rec x_a0 x_a1 x_a2 x_a3 x_a4 x_a5))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, b2, b3, b4, b5, y0, y1, y2, y3, y4, y5, hargs, hb0, hb1, hb2, hb3, hb4, hb5, hr⟩ := ProgramSem.of_53 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      obtain rfl := Rep.functional hb2 (Represents.congr h_a2 hn)
      obtain rfl := Rep.functional hb3 (Represents.congr h_a3 hn)
      obtain rfl := Rep.functional hb4 (Represents.congr h_a4 hn)
      obtain rfl := Rep.functional hb5 (Represents.congr h_a5 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_53 ⟨a0, a1, a2, a3, a4, a5, x_a0, x_a1, x_a2, x_a3, x_a4, x_a5, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, Rep.mono hpre h_a2, Rep.mono hpre h_a3, Rep.mono hpre h_a4, Rep.mono hpre h_a5, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24bv_5fumulo_5felim_5frec_spec m (ih m hm) s1 a0 a1 a2 a3 a4 a5 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn) (by congr_one h_a4 hn) (by congr_one h_a5 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24chain_5fm_5fresolve_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24chain_5fm_5fresolve s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__chain_m_resolve.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__chain_m_resolve.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24chain_5fm_5fresolve
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__chain_m_resolve.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__chain_m_resolve.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_and.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__chain_m_resolve.case_0
  store_step with ih.eo__24chain_5fm_5fresolve_5frec s1 v2 a1 a2 _ _ _ hinv1 h64 (hG.rem hrem) h_v2 h_a1 h_a2 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24chain_5fm_5fresolve_5ffinal s2 v5 v7 _ _ hinv2 h64 (hG.rem hrem) h_v5 h_v7 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  case_done hinv3 hG with h_v8 in EoCases.__chain_m_resolve.case_0 using hn_a0 hn_a1 hn_a2 hn_v1 hn_v2 hn_v4 hn_v5

/-- logos's `__chain_m_resolve` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24chain_5fm_5fresolve.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __chain_m_resolve x_a0 x_a1 x_a2 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__chain_m_resolve.case_0 x_a0 x_a1 x_a2] HasStuck.stuck) := by
  conv => lhs; unfold __chain_m_resolve
  unfold EoCases.__chain_m_resolve.case_0
  logos_eq

theorem body_eo__24chain_5fm_5fresolve_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24chain_5fm_5fresolve s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__chain_m_resolve x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24chain_5fm_5fresolve.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24chain_5fm_5fresolve
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24chain_5fm_5fresolve_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1 hn_a2
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hc0 in EoCases.__chain_m_resolve.case_0

theorem eo__24chain_5fm_5fresolve_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24chain_5fm_5fresolve.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24chain_5fm_5fresolve
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24chain_5fm_5fresolve s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__chain_m_resolve x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24chain_5fm_5fresolve_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24chain_5fm_5fresolve_5ffinal_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24chain_5fm_5fresolve_5ffinal s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__chain_m_resolve_final.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__chain_m_resolve_final.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24chain_5fm_5fresolve_5ffinal
  have hG := Store.Grows.refl s
  pat_unapply h_a1 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__chain_m_resolve_final.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__chain_m_resolve_final.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__40_40pair.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__chain_m_resolve_final.case_0
  pat_unapply h_v2 as ⟨v8, v9, x_v8, x_v9, h_v8, h_v9, hn_v8, hn_v9⟩ using hinv1 else hinv1 hG in EoCases.__chain_m_resolve_final.case_0
  pat_unapply h_v8 as ⟨v11, v12, x_v11, x_v12, h_v11, h_v12, hn_v11, hn_v12⟩ using hinv1 else hinv1 hG in EoCases.__chain_m_resolve_final.case_0
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo_or.construct s1 e_v13 (by rw [he_v13]; exact empty_args) hinv1 h64 as ⟨v13, s2, hinv2, h_v13⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12
  pat_same v11 v13 with h_v11 h_v13 using hinv2 else hinv2 hG in EoCases.__chain_m_resolve_final.case_0
  step as ⟨e_v14, he_v14⟩
  store_step with Store.builtin_spec_eq s2 e_v14 (by rw [he_v14]; rfl) h_a0 h_v12 hinv2 h64 as ⟨v14, s3, hinv3, h_v14⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13
  have h_ite_v22 := (show if_0_eo__24chain_5fm_5fresolve_5ffinal s3 v14 v5 v12 v9 a0 ⦃ r s' => s'.Inv ∧ s3.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_0_eo__24chain_5fm_5fresolve_5ffinal
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s3
    rcases Store.boolean_value_term h_v14 with ⟨hx_15, hbv_15⟩ | ⟨hx_15, hbv_15⟩ | ⟨hx_15, hbv_15⟩
    · ite_branch hbv_15
      ite_done hinv3 hG with (eo_ite_true_rep _ hx_15 h_v5)
    · ite_branch hbv_15
      step as ⟨e_v15, he_v15⟩
      store_step with CtorSpec.eo_or.construct s3 e_v15 (by rw [he_v15]; exact empty_args) hinv3 h64 as ⟨v15, s4, hinv4, h_v15⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14
      step as ⟨e_v16, he_v16⟩
      store_step with CtorSpec.eo_or.construct s4 e_v16 (by rw [he_v16]; exact empty_args) hinv4 h64 as ⟨v16, s5, hinv5, h_v16⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15
      step as ⟨e_v17, he_v17⟩
      store_step with CtorSpec.eo_or.construct s5 e_v17 (by rw [he_v17]; exact empty_args) hinv5 h64 as ⟨v17, s6, hinv6, h_v17⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16
      store_step with Store.apply_rep s6 v17 v12 _ _ hinv6 h64 h_v17 h_v12 (by ns_tac) (by ns_tac) as ⟨v18, s7, hinv7, h_v18⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17
      store_step with Store.apply_rep s7 v18 v9 _ _ hinv7 h64 h_v18 h_v9 (by ns_tac) (by ns_tac) as ⟨v19, s8, hinv8, h_v19⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18
      step as ⟨e_v20, he_v20⟩
      store_step with Store.builtin_spec_list_diff n ih.eo__24eo_5fis_5flist_5fnil s8 e_v20 (by rw [he_v20]; rfl) h_v16 h_a0 h_v19 hinv8 h64 (hG.rem hrem) (by not_left_tac) (by unique_nil_tac) as ⟨v20, s9, hinv9, h_v20⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19
      step as ⟨e_v21, he_v21⟩
      store_step with Store.builtin_spec_list_concat n ih.eo__24eo_5fis_5flist_5fnil s9 e_v21 (by rw [he_v21]; rfl) h_v15 h_v20 h_v5 hinv9 h64 (hG.rem hrem) (by not_left_tac) (by unique_nil_tac) as ⟨v21, s10, hinv10, h_v21⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20
      ite_done hinv10 hG with (eo_ite_false_rep _ hx_15 h_v21)
    · ite_branch hbv_15
      ite_stuck hinv3 hG with hx_15)
  store_step with h_ite_v22 as ⟨v22, s4, hinv4, h_v22⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14
  case_done hinv4 hG with h_v22 in EoCases.__chain_m_resolve_final.case_0 using hn_a0 hn_a1 hn_v1 hn_v2 hn_v4 hn_v5 hn_v8 hn_v9 hn_v11 hn_v12

/-- logos's `__chain_m_resolve_final` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24chain_5fm_5fresolve_5ffinal.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __chain_m_resolve_final x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__chain_m_resolve_final.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __chain_m_resolve_final
  unfold EoCases.__chain_m_resolve_final.case_0
  logos_eq

theorem body_eo__24chain_5fm_5fresolve_5ffinal_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24chain_5fm_5fresolve_5ffinal s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__chain_m_resolve_final x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24chain_5fm_5fresolve_5ffinal.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24chain_5fm_5fresolve_5ffinal
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24chain_5fm_5fresolve_5ffinal_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__chain_m_resolve_final.case_0

theorem eo__24chain_5fm_5fresolve_5ffinal_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24chain_5fm_5fresolve_5ffinal.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24chain_5fm_5fresolve_5ffinal
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24chain_5fm_5fresolve_5ffinal s1 a0 a1) (fun s' t => Represents.rep s' t (__chain_m_resolve_final x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24chain_5fm_5fresolve_5ffinal_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24chain_5fm_5fresolve_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24chain_5fm_5fresolve_5frec s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__chain_m_resolve_rec.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__chain_m_resolve_rec.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24chain_5fm_5fresolve_5frec
  have hG := Store.Grows.refl s
  store_step with Store.literal_boolean_spec s true hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__chain_m_resolve_rec.case_0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0
  pat_same a1 v1 with h_a1 h_v1 using hinv2 else hinv2 hG in EoCases.__chain_m_resolve_rec.case_0
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1
  pat_same a2 v2 with h_a2 h_v2 using hinv3 else hinv3 hG in EoCases.__chain_m_resolve_rec.case_0
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__40_40pair.construct s3 e_v3 (by rw [he_v3]; exact empty_args) hinv3 h64 as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2
  store_step with Store.literal_boolean_spec s4 false hinv4 h64 as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3
  store_step with Store.apply_rep s5 v3 v4 _ _ hinv5 h64 h_v3 h_v4 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4
  store_step with Store.literal_boolean_spec s6 false hinv6 h64 as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with Store.apply_rep s7 v5 v6 _ _ hinv7 h64 h_v5 h_v6 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  case_done hinv8 hG with h_v7 in EoCases.__chain_m_resolve_rec.case_0 using hn_a0 hn_a1 hn_a2

theorem case_1_eo__24chain_5fm_5fresolve_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_1_eo__24chain_5fm_5fresolve_5frec s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__chain_m_resolve_rec.case_1 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__chain_m_resolve_rec.case_1 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24chain_5fm_5fresolve_5frec more_0_eo__24chain_5fm_5fresolve_5frec
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__chain_m_resolve_rec.case_1
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__chain_m_resolve_rec.case_1
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_and.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__chain_m_resolve_rec.case_1
  pat_unapply h_a1 as ⟨v8, v9, x_v8, x_v9, h_v8, h_v9, hn_v8, hn_v9⟩ using hinv1 else hinv1 hG in EoCases.__chain_m_resolve_rec.case_1
  pat_unapply h_v8 as ⟨v11, v12, x_v11, x_v12, h_v11, h_v12, hn_v11, hn_v12⟩ using hinv1 else hinv1 hG in EoCases.__chain_m_resolve_rec.case_1
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s1 e_v13 (by rw [he_v13]; exact empty_args) hinv1 h64 as ⟨v13, s2, hinv2, h_v13⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12
  pat_same v11 v13 with h_v11 h_v13 using hinv2 else hinv2 hG in EoCases.__chain_m_resolve_rec.case_1
  pat_unapply h_a2 as ⟨v15, v16, x_v15, x_v16, h_v15, h_v16, hn_v15, hn_v16⟩ using hinv2 else hinv2 hG in EoCases.__chain_m_resolve_rec.case_1
  pat_unapply h_v15 as ⟨v18, v19, x_v18, x_v19, h_v18, h_v19, hn_v18, hn_v19⟩ using hinv2 else hinv2 hG in EoCases.__chain_m_resolve_rec.case_1
  step as ⟨e_v20, he_v20⟩
  store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s2 e_v20 (by rw [he_v20]; exact empty_args) hinv2 h64 as ⟨v20, s3, hinv3, h_v20⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v15 h_v16 h_v18 h_v19
  pat_same v18 v20 with h_v18 h_v20 using hinv3 else hinv3 hG in EoCases.__chain_m_resolve_rec.case_1
  store_step with ih.eo__24chain_5fm_5fresolve_5frec s3 v2 v9 v16 _ _ _ hinv3 h64 (hG.rem hrem) h_v2 h_v9 h_v16 as ⟨v21, s4, hinv4, h_v21⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v15 h_v16 h_v18 h_v19 h_v20
  store_step with ih.eo__24chain_5fm_5fresolve_5frec_5fstep s4 v21 v5 v12 v19 _ _ _ _ hinv4 h64 (hG.rem hrem) h_v21 h_v5 h_v12 h_v19 as ⟨v22, s5, hinv5, h_v22⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v15 h_v16 h_v18 h_v19 h_v20 h_v21
  case_done hinv5 hG with h_v22 in EoCases.__chain_m_resolve_rec.case_1 using hn_a0 hn_a1 hn_a2 hn_v1 hn_v2 hn_v4 hn_v5 hn_v8 hn_v9 hn_v11 hn_v12 hn_v15 hn_v16 hn_v18 hn_v19

/-- logos's `__chain_m_resolve_rec` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24chain_5fm_5fresolve_5frec.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __chain_m_resolve_rec x_a0 x_a1 x_a2 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__chain_m_resolve_rec.case_0 x_a0 x_a1 x_a2, EoCases.__chain_m_resolve_rec.case_1 x_a0 x_a1 x_a2] HasStuck.stuck) := by
  conv => lhs; unfold __chain_m_resolve_rec
  unfold EoCases.__chain_m_resolve_rec.case_0 EoCases.__chain_m_resolve_rec.case_1
  logos_eq

theorem body_eo__24chain_5fm_5fresolve_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24chain_5fm_5fresolve_5frec s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__chain_m_resolve_rec x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24chain_5fm_5fresolve_5frec.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24chain_5fm_5fresolve_5frec
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24chain_5fm_5fresolve_5frec_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1 hn_a2
  case_step with case_1_eo__24chain_5fm_5fresolve_5frec_spec n ih s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1 hn_a2 hc0
  body_stuck hinv2 hG using hn_a0 hn_a1 hn_a2 hc0 hc1 in EoCases.__chain_m_resolve_rec.case_0 EoCases.__chain_m_resolve_rec.case_1

theorem eo__24chain_5fm_5fresolve_5frec_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24chain_5fm_5fresolve_5frec.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24chain_5fm_5fresolve_5frec
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 56#u32 _ [a0, a1, a2] rfl
    (fun s1 => body_eo__24chain_5fm_5fresolve_5frec s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__chain_m_resolve_rec x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, b2, y0, y1, y2, hargs, hb0, hb1, hb2, hr⟩ := ProgramSem.of_56 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      obtain rfl := Rep.functional hb2 (Represents.congr h_a2 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_56 ⟨a0, a1, a2, x_a0, x_a1, x_a2, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, Rep.mono hpre h_a2, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24chain_5fm_5fresolve_5frec_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

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

/-- logos's `__chain_m_resolve_rec_step` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24chain_5fm_5fresolve_5frec_5fstep.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) :
    __chain_m_resolve_rec_step x_a0 x_a1 x_a2 x_a3 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__chain_m_resolve_rec_step.case_0 x_a0 x_a1 x_a2 x_a3] HasStuck.stuck) := by
  conv => lhs; unfold __chain_m_resolve_rec_step
  unfold EoCases.__chain_m_resolve_rec_step.case_0
  logos_eq

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

theorem case_0_eo__24compute_5fcard_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24compute_5fcard s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__compute_card.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__compute_card.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24compute_5fcard
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fBool.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__compute_card.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s1 2#u32 (2) (by scalar_tac) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__compute_card.case_0 using hn_a0

theorem case_1_eo__24compute_5fcard_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_1_eo__24compute_5fcard s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__compute_card.case_1 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__compute_card.case_1 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24compute_5fcard
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__compute_card.case_1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_BitVec.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__compute_card.case_1
  step as ⟨e_v4, he_v4⟩
  store_step with Store.builtin_spec_is_z s1 e_v4 (by rw [he_v4]; rfl) h_v2 hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  have h_ite_v12 := (show if_1_eo__24compute_5fcard s2 v4 v2 ⦃ r s' => s'.Inv ∧ s2.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_1_eo__24compute_5fcard
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s2
    rcases Store.boolean_value_term h_v4 with ⟨hx_5, hbv_5⟩ | ⟨hx_5, hbv_5⟩ | ⟨hx_5, hbv_5⟩
    · ite_branch hbv_5
      step as ⟨e_v5, he_v5⟩
      store_step with Store.builtin_spec_is_neg s2 e_v5 (by rw [he_v5]; rfl) h_v2 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
      have h_ite_v9 := (show if_0_eo__24compute_5fcard s3 v5 v2 ⦃ r s' => s'.Inv ∧ s3.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_0_eo__24compute_5fcard
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s3
        rcases Store.boolean_value_term h_v5 with ⟨hx_6, hbv_6⟩ | ⟨hx_6, hbv_6⟩ | ⟨hx_6, hbv_6⟩
        · ite_branch hbv_6
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s3 0#u32 (0) (by scalar_tac) hinv3 h64 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
          ite_done hinv4 hG with (eo_ite_true_rep _ hx_6 h_v6)
        · ite_branch hbv_6
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s3 2#u32 (2) (by scalar_tac) hinv3 h64 as ⟨v7, s4, hinv4, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
          step as ⟨e_v8, he_v8⟩
          store_step with Store.builtin_spec_pow s4 e_v8 (by rw [he_v8]; rfl) h_v7 h_v2 hinv4 h64 as ⟨v8, s5, hinv5, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v7
          ite_done hinv5 hG with (eo_ite_false_rep _ hx_6 h_v8)
        · ite_branch hbv_6
          ite_stuck hinv3 hG with hx_6)
      store_step with h_ite_v9 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
      ite_done hinv4 hG with (eo_ite_true_rep _ hx_5 h_v9)
    · ite_branch hbv_5
      step as ⟨e_v10, he_v10⟩
      store_step with CtorSpec.eo_int_2epow2.construct s2 e_v10 (by rw [he_v10]; exact empty_args) hinv2 h64 as ⟨v10, s3, hinv3, h_v10⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
      store_step with Store.apply_rep s3 v10 v2 _ _ hinv3 h64 h_v10 h_v2 (by ns_tac) (by ns_tac) as ⟨v11, s4, hinv4, h_v11⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v10
      ite_done hinv4 hG with (eo_ite_false_rep _ hx_5 h_v11)
    · ite_branch hbv_5
      ite_stuck hinv2 hG with hx_5)
  store_step with h_ite_v12 as ⟨v12, s3, hinv3, h_v12⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v12 in EoCases.__compute_card.case_1 using hn_a0 hn_v1 hn_v2

/-- logos's `__compute_card` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24compute_5fcard.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __compute_card x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__compute_card.case_0 x_a0, EoCases.__compute_card.case_1 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __compute_card
  unfold EoCases.__compute_card.case_0 EoCases.__compute_card.case_1
  logos_eq

theorem body_eo__24compute_5fcard_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24compute_5fcard s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__compute_card x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24compute_5fcard.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24compute_5fcard
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24compute_5fcard_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  case_step with case_1_eo__24compute_5fcard_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 using hn_a0 hc0
  body_stuck hinv2 hG using hn_a0 hc0 hc1 in EoCases.__compute_card.case_0 EoCases.__compute_card.case_1

theorem eo__24compute_5fcard_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24compute_5fcard.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24compute_5fcard
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24compute_5fcard s1 a0) (fun s' t => Represents.rep s' t (__compute_card x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24compute_5fcard_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24dt_5farg_5flist_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24dt_5farg_5flist s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__dt_arg_list.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__dt_arg_list.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24dt_5farg_5flist
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__dt_arg_list.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__dt_arg_list.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_tuple.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__dt_arg_list.case_0
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo_tuple.construct s1 e_v7 (by rw [he_v7]; exact empty_args) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with Store.apply_rep s2 v7 v5 _ _ hinv2 h64 h_v7 h_v5 (by ns_tac) (by ns_tac) as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with Store.apply_rep s3 v8 v2 _ _ hinv3 h64 h_v8 h_v2 (by ns_tac) (by ns_tac) as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  store_step with ih.eo__24tuple_5farg_5flist s4 v9 _ hinv4 h64 (hG.rem hrem) h_v9 as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  case_done hinv5 hG with h_v10 in EoCases.__dt_arg_list.case_0 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_1_eo__24dt_5farg_5flist_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_1_eo__24dt_5farg_5flist s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__dt_arg_list.case_1 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__dt_arg_list.case_1 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24dt_5farg_5flist
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  store_step with ih.eo__24get_5farg_5flist_5frec s1 a0 v0 _ _ hinv1 h64 (hG.rem hrem) h_a0 h_v0 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__dt_arg_list.case_1 using hn_a0

/-- logos's `__dt_arg_list` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24dt_5farg_5flist.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __dt_arg_list x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__dt_arg_list.case_0 x_a0, EoCases.__dt_arg_list.case_1 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __dt_arg_list
  unfold EoCases.__dt_arg_list.case_0 EoCases.__dt_arg_list.case_1
  logos_eq

theorem body_eo__24dt_5farg_5flist_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24dt_5farg_5flist s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__dt_arg_list x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24dt_5farg_5flist.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24dt_5farg_5flist
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24dt_5farg_5flist_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  case_step with case_1_eo__24dt_5farg_5flist_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 using hn_a0 hc0
  body_stuck hinv2 hG using hn_a0 hc0 hc1 in EoCases.__dt_arg_list.case_0 EoCases.__dt_arg_list.case_1

theorem eo__24dt_5farg_5flist_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24dt_5farg_5flist.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24dt_5farg_5flist
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24dt_5farg_5flist s1 a0) (fun s' t => Represents.rep s' t (__dt_arg_list x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24dt_5farg_5flist_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24dt_5fcollapse_5fupdater_5frhs_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24dt_5fcollapse_5fupdater_5frhs s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__dt_collapse_updater_rhs.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__dt_collapse_updater_rhs.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24dt_5fcollapse_5fupdater_5frhs
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__dt_collapse_updater_rhs.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s 0#u32 (0) (by scalar_tac) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2
  pat_same a2 v3 with h_a2 h_v3 using hinv1 else hinv1 hG in EoCases.__dt_collapse_updater_rhs.case_0
  store_step with Store.apply_rep s1 v1 a1 _ _ hinv1 h64 h_v1 h_a1 (by ns_tac) (by ns_tac) as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v3
  case_done hinv2 hG with h_v4 in EoCases.__dt_collapse_updater_rhs.case_0 using hn_a0 hn_a1 hn_a2 hn_v1 hn_v2

theorem case_1_eo__24dt_5fcollapse_5fupdater_5frhs_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_1_eo__24dt_5fcollapse_5fupdater_5frhs s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__dt_collapse_updater_rhs.case_1 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__dt_collapse_updater_rhs.case_1 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24dt_5fcollapse_5fupdater_5frhs
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__dt_collapse_updater_rhs.case_1
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_neg_u32_spec s 1#u32 (-1) (by scalar_tac) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2
  step as ⟨e_v4, he_v4⟩
  store_step with Store.builtin_spec_add s1 e_v4 (by rw [he_v4]; rfl) h_a2 h_v3 hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v3
  store_step with ih.eo__24dt_5fcollapse_5fupdater_5frhs s2 v1 a1 v4 _ _ _ hinv2 h64 (hG.rem hrem) h_v1 h_a1 h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v3 h_v4
  store_step with Store.apply_mk_rep s3 v5 v2 _ _ hinv3 h64 h_v5 h_v2 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v3 h_v4 h_v5
  case_done hinv4 hG with h_v6 in EoCases.__dt_collapse_updater_rhs.case_1 using hn_a0 hn_a1 hn_a2 hn_v1 hn_v2

/-- logos's `__dt_collapse_updater_rhs` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24dt_5fcollapse_5fupdater_5frhs.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __dt_collapse_updater_rhs x_a0 x_a1 x_a2 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__dt_collapse_updater_rhs.case_0 x_a0 x_a1 x_a2, EoCases.__dt_collapse_updater_rhs.case_1 x_a0 x_a1 x_a2] HasStuck.stuck) := by
  conv => lhs; unfold __dt_collapse_updater_rhs
  unfold EoCases.__dt_collapse_updater_rhs.case_0 EoCases.__dt_collapse_updater_rhs.case_1
  logos_eq

theorem body_eo__24dt_5fcollapse_5fupdater_5frhs_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24dt_5fcollapse_5fupdater_5frhs s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__dt_collapse_updater_rhs x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24dt_5fcollapse_5fupdater_5frhs.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24dt_5fcollapse_5fupdater_5frhs
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24dt_5fcollapse_5fupdater_5frhs_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1 hn_a2
  case_step with case_1_eo__24dt_5fcollapse_5fupdater_5frhs_spec n ih s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1 hn_a2 hc0
  body_stuck hinv2 hG using hn_a0 hn_a1 hn_a2 hc0 hc1 in EoCases.__dt_collapse_updater_rhs.case_0 EoCases.__dt_collapse_updater_rhs.case_1

theorem eo__24dt_5fcollapse_5fupdater_5frhs_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24dt_5fcollapse_5fupdater_5frhs.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24dt_5fcollapse_5fupdater_5frhs
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 62#u32 _ [a0, a1, a2] rfl
    (fun s1 => body_eo__24dt_5fcollapse_5fupdater_5frhs s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__dt_collapse_updater_rhs x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, b2, y0, y1, y2, hargs, hb0, hb1, hb2, hr⟩ := ProgramSem.of_62 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      obtain rfl := Rep.functional hb2 (Represents.congr h_a2 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_62 ⟨a0, a1, a2, x_a0, x_a1, x_a2, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, Rep.mono hpre h_a2, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24dt_5fcollapse_5fupdater_5frhs_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24dt_5fdistinct_5fterms_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24dt_5fdistinct_5fterms s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__dt_distinct_terms.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _), arr.val = [u0, u1] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧
          EoCases.__dt_distinct_terms.case_0 x_a0 x_a1 = some (__dt_distinct_terms y0 y1)
      | core.result.Result.Ok none => EoCases.__dt_distinct_terms.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24dt_5fdistinct_5fterms
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__dt_distinct_terms.case_0
  pat_unapply h_a1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__dt_distinct_terms.case_0
  store_step with ih.eo__24dt_5fdistinct_5fterms s v1 v4 _ _ hinv h64 hrem h_v1 h_v4 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5
  have h_ite_v13 := (show if_1_eo__24dt_5fdistinct_5fterms s1 v6 v2 v5 ⦃ r s' => s'.Inv ∧ s1.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_1_eo__24dt_5fdistinct_5fterms
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s1
    rcases Store.boolean_value_term h_v6 with ⟨hx_7, hbv_7⟩ | ⟨hx_7, hbv_7⟩ | ⟨hx_7, hbv_7⟩
    · ite_branch hbv_7
      store_step with Store.literal_boolean_spec s1 true hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6
      ite_done hinv2 hG with (eo_ite_true_rep _ hx_7 h_v7)
    · ite_branch hbv_7
      step as ⟨e_v8, he_v8⟩
      store_step with Store.builtin_spec_eq s1 e_v8 (by rw [he_v8]; rfl) h_v2 h_v5 hinv1 h64 as ⟨v8, s2, hinv2, h_v8⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6
      have h_ite_v12 := (show if_0_eo__24dt_5fdistinct_5fterms s2 v8 v2 v5 ⦃ r s' => s'.Inv ∧ s2.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_0_eo__24dt_5fdistinct_5fterms
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s2
        rcases Store.boolean_value_term h_v8 with ⟨hx_9, hbv_9⟩ | ⟨hx_9, hbv_9⟩ | ⟨hx_9, hbv_9⟩
        · ite_branch hbv_9
          store_step with Store.literal_boolean_spec s2 false hinv2 h64 as ⟨v9, s3, hinv3, h_v9⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8
          ite_done hinv3 hG with (eo_ite_true_rep _ hx_9 h_v9)
        · ite_branch hbv_9
          store_step with ih.eo__24eo_5ftypeof s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v10, s3, hinv3, h_v10⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8
          store_step with ih.eo__24are_5fdistinct_5fterms_5ftype s3 v2 v5 v10 _ _ _ hinv3 h64 (hG.rem hrem) h_v2 h_v5 h_v10 as ⟨v11, s4, hinv4, h_v11⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v10
          ite_done hinv4 hG with (eo_ite_false_rep _ hx_9 h_v11)
        · ite_branch hbv_9
          ite_stuck hinv2 hG with hx_9)
      store_step with h_ite_v12 as ⟨v12, s3, hinv3, h_v12⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8
      ite_done hinv3 hG with (eo_ite_false_rep _ hx_7 h_v12)
    · ite_branch hbv_7
      ite_stuck hinv1 hG with hx_7)
  store_step with h_ite_v13 as ⟨v13, s2, hinv2, h_v13⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6
  case_done hinv2 hG with h_v13 in EoCases.__dt_distinct_terms.case_0 using hn_a0 hn_a1 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_1_eo__24dt_5fdistinct_5fterms_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_1_eo__24dt_5fdistinct_5fterms s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__dt_distinct_terms.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _), arr.val = [u0, u1] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧
          EoCases.__dt_distinct_terms.case_1 x_a0 x_a1 = some (__dt_distinct_terms y0 y1)
      | core.result.Result.Ok none => EoCases.__dt_distinct_terms.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24dt_5fdistinct_5fterms
  have hG := Store.Grows.refl s
  pat_unapply h_a1 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__dt_distinct_terms.case_1
  case_again hinv hG with h_a0 h_v1 in EoCases.__dt_distinct_terms.case_1 using hn_a0 hn_a1 hn_v1 hn_v2

theorem case_2_eo__24dt_5fdistinct_5fterms_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_2_eo__24dt_5fdistinct_5fterms s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__dt_distinct_terms.case_2 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _), arr.val = [u0, u1] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧
          EoCases.__dt_distinct_terms.case_2 x_a0 x_a1 = some (__dt_distinct_terms y0 y1)
      | core.result.Result.Ok none => EoCases.__dt_distinct_terms.case_2 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24dt_5fdistinct_5fterms
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__dt_distinct_terms.case_2
  case_again hinv hG with h_v1 h_a1 in EoCases.__dt_distinct_terms.case_2 using hn_a0 hn_a1 hn_v1 hn_v2

theorem case_3_eo__24dt_5fdistinct_5fterms_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_3_eo__24dt_5fdistinct_5fterms s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__dt_distinct_terms.case_3 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _), arr.val = [u0, u1] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧
          EoCases.__dt_distinct_terms.case_3 x_a0 x_a1 = some (__dt_distinct_terms y0 y1)
      | core.result.Result.Ok none => EoCases.__dt_distinct_terms.case_3 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_3_eo__24dt_5fdistinct_5fterms
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_tuple.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  step as ⟨e_v1, he_v1⟩
  store_step with Store.builtin_spec_is_eq s1 e_v1 (by rw [he_v1]; rfl) h_a0 h_v0 hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  have h_ite_v9 := (show if_3_eo__24dt_5fdistinct_5fterms s2 v1 a0 ⦃ r s' => s'.Inv ∧ s2.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_3_eo__24dt_5fdistinct_5fterms
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s2
    rcases Store.boolean_value_term h_v1 with ⟨hx_2, hbv_2⟩ | ⟨hx_2, hbv_2⟩ | ⟨hx_2, hbv_2⟩
    · ite_branch hbv_2
      store_step with Store.literal_boolean_spec s2 true hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1
      ite_done hinv3 hG with (eo_ite_true_rep _ hx_2 h_v2)
    · ite_branch hbv_2
      step as ⟨e_v3, he_v3⟩
      store_step with CtorSpec.eo_tuple_2eunit.construct s2 e_v3 (by rw [he_v3]; exact empty_args) hinv2 h64 as ⟨v3, s3, hinv3, h_v3⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1
      step as ⟨e_v4, he_v4⟩
      store_step with Store.builtin_spec_is_eq s3 e_v4 (by rw [he_v4]; rfl) h_a0 h_v3 hinv3 h64 as ⟨v4, s4, hinv4, h_v4⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v3
      have h_ite_v8 := (show if_2_eo__24dt_5fdistinct_5fterms s4 v4 a0 ⦃ r s' => s'.Inv ∧ s4.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_2_eo__24dt_5fdistinct_5fterms
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s4
        rcases Store.boolean_value_term h_v4 with ⟨hx_5, hbv_5⟩ | ⟨hx_5, hbv_5⟩ | ⟨hx_5, hbv_5⟩
        · ite_branch hbv_5
          store_step with Store.literal_boolean_spec s4 true hinv4 h64 as ⟨v5, s5, hinv5, h_v5⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v3 h_v4
          ite_done hinv5 hG with (eo_ite_true_rep _ hx_5 h_v5)
        · ite_branch hbv_5
          store_step with ih.eo__24eo_5fdt_5fselectors s4 a0 _ hinv4 h64 (hG.rem hrem) h_a0 as ⟨v6, s5, hinv5, h_v6⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v3 h_v4
          step as ⟨e_v7, he_v7⟩
          store_step with Store.builtin_spec_is_ok s5 e_v7 (by rw [he_v7]; rfl) h_v6 hinv5 h64 as ⟨v7, s6, hinv6, h_v7⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v3 h_v4 h_v6
          ite_done hinv6 hG with (eo_ite_false_rep _ hx_5 h_v7)
        · ite_branch hbv_5
          ite_stuck hinv4 hG with hx_5)
      store_step with h_ite_v8 as ⟨v8, s5, hinv5, h_v8⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v3 h_v4
      ite_done hinv5 hG with (eo_ite_false_rep _ hx_2 h_v8)
    · ite_branch hbv_2
      ite_stuck hinv2 hG with hx_2)
  store_step with h_ite_v9 as ⟨v9, s3, hinv3, h_v9⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo_tuple.construct s3 e_v10 (by rw [he_v10]; exact empty_args) hinv3 h64 as ⟨v10, s4, hinv4, h_v10⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v9
  step as ⟨e_v11, he_v11⟩
  store_step with Store.builtin_spec_is_eq s4 e_v11 (by rw [he_v11]; rfl) h_a1 h_v10 hinv4 h64 as ⟨v11, s5, hinv5, h_v11⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v9 h_v10
  have h_ite_v19 := (show if_5_eo__24dt_5fdistinct_5fterms s5 v11 a1 ⦃ r s' => s'.Inv ∧ s5.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_5_eo__24dt_5fdistinct_5fterms
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s5
    rcases Store.boolean_value_term h_v11 with ⟨hx_12, hbv_12⟩ | ⟨hx_12, hbv_12⟩ | ⟨hx_12, hbv_12⟩
    · ite_branch hbv_12
      store_step with Store.literal_boolean_spec s5 true hinv5 h64 as ⟨v12, s6, hinv6, h_v12⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v9 h_v10 h_v11
      ite_done hinv6 hG with (eo_ite_true_rep _ hx_12 h_v12)
    · ite_branch hbv_12
      step as ⟨e_v13, he_v13⟩
      store_step with CtorSpec.eo_tuple_2eunit.construct s5 e_v13 (by rw [he_v13]; exact empty_args) hinv5 h64 as ⟨v13, s6, hinv6, h_v13⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v9 h_v10 h_v11
      step as ⟨e_v14, he_v14⟩
      store_step with Store.builtin_spec_is_eq s6 e_v14 (by rw [he_v14]; rfl) h_a1 h_v13 hinv6 h64 as ⟨v14, s7, hinv7, h_v14⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v9 h_v10 h_v11 h_v13
      have h_ite_v18 := (show if_4_eo__24dt_5fdistinct_5fterms s7 v14 a1 ⦃ r s' => s'.Inv ∧ s7.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_4_eo__24dt_5fdistinct_5fterms
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s7
        rcases Store.boolean_value_term h_v14 with ⟨hx_15, hbv_15⟩ | ⟨hx_15, hbv_15⟩ | ⟨hx_15, hbv_15⟩
        · ite_branch hbv_15
          store_step with Store.literal_boolean_spec s7 true hinv7 h64 as ⟨v15, s8, hinv8, h_v15⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v9 h_v10 h_v11 h_v13 h_v14
          ite_done hinv8 hG with (eo_ite_true_rep _ hx_15 h_v15)
        · ite_branch hbv_15
          store_step with ih.eo__24eo_5fdt_5fselectors s7 a1 _ hinv7 h64 (hG.rem hrem) h_a1 as ⟨v16, s8, hinv8, h_v16⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v9 h_v10 h_v11 h_v13 h_v14
          step as ⟨e_v17, he_v17⟩
          store_step with Store.builtin_spec_is_ok s8 e_v17 (by rw [he_v17]; rfl) h_v16 hinv8 h64 as ⟨v17, s9, hinv9, h_v17⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v9 h_v10 h_v11 h_v13 h_v14 h_v16
          ite_done hinv9 hG with (eo_ite_false_rep _ hx_15 h_v17)
        · ite_branch hbv_15
          ite_stuck hinv7 hG with hx_15)
      store_step with h_ite_v18 as ⟨v18, s8, hinv8, h_v18⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v9 h_v10 h_v11 h_v13 h_v14
      ite_done hinv8 hG with (eo_ite_false_rep _ hx_12 h_v18)
    · ite_branch hbv_12
      ite_stuck hinv5 hG with hx_12)
  store_step with h_ite_v19 as ⟨v19, s6, hinv6, h_v19⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v9 h_v10 h_v11
  step as ⟨e_v20, he_v20⟩
  store_step with Store.builtin_spec_and s6 e_v20 (by rw [he_v20]; rfl) h_v9 h_v19 hinv6 h64 as ⟨v20, s7, hinv7, h_v20⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v9 h_v10 h_v11 h_v19
  store_step with Store.literal_boolean_spec s7 true hinv7 h64 as ⟨v21, s8, hinv8, h_v21⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v9 h_v10 h_v11 h_v19 h_v20
  have h_req_v24 := (show requires_6_eo__24dt_5fdistinct_5fterms s8 v20 v21 a0 a1 ⦃ r s' => s'.Inv ∧ s8.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold requires_6_eo__24dt_5fdistinct_5fterms
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s8
    req_same v20 v21 with h_v20 h_v21 using hinv8 hG
    req_stuck h_v20 as hq_v20 using hinv8 hG
    step as ⟨e_v22, he_v22⟩
    store_step with Store.builtin_spec_eq s8 e_v22 (by rw [he_v22]; rfl) h_a0 h_a1 hinv8 h64 as ⟨v22, s9, hinv9, h_v22⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v9 h_v10 h_v11 h_v19 h_v20 h_v21
    step as ⟨e_v23, he_v23⟩
    store_step with Store.builtin_spec_not s9 e_v23 (by rw [he_v23]; rfl) h_v22 hinv9 h64 as ⟨v23, s10, hinv10, h_v23⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v9 h_v10 h_v11 h_v19 h_v20 h_v21 h_v22
    req_done hinv10 hG with h_v23 using hq_v20)
  store_step with h_req_v24 as ⟨v24, s11, hinv11, h_v24⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v9 h_v10 h_v11 h_v19 h_v20 h_v21
  case_done hinv11 hG with h_v24 in EoCases.__dt_distinct_terms.case_3 using hn_a0 hn_a1

/-- logos's `__dt_distinct_terms` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24dt_5fdistinct_5fterms.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __dt_distinct_terms x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__dt_distinct_terms.case_0 x_a0 x_a1, EoCases.__dt_distinct_terms.case_1 x_a0 x_a1, EoCases.__dt_distinct_terms.case_2 x_a0 x_a1, EoCases.__dt_distinct_terms.case_3 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __dt_distinct_terms
  unfold EoCases.__dt_distinct_terms.case_0 EoCases.__dt_distinct_terms.case_1 EoCases.__dt_distinct_terms.case_2 EoCases.__dt_distinct_terms.case_3
  logos_eq

theorem step_eo__24dt_5fdistinct_5fterms_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    step_eo__24dt_5fdistinct_5fterms s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (Next.Done t) => Represents.rep s' t (__dt_distinct_terms x_a0 x_a1)
      | core.result.Result.Ok (Next.Again arr) =>
        s'.budget < s.budget ∧ ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _), arr.val = [u0, u1] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧
          __dt_distinct_terms x_a0 x_a1 = __dt_distinct_terms y0 y1
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24dt_5fdistinct_5fterms.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold step_eo__24dt_5fdistinct_5fterms
  have hG := Store.Grows.refl s
  tick_step as ⟨s1, hinv1⟩ growing hG carrying h_a0 h_a1
  stuck_check h_a0 : x_a0 as hn_a0 else hinv1 hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv1 hG
  round_step with case_0_eo__24dt_5fdistinct_5fterms_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s2, hinv2, hc0⟩ growing hG carrying h_a0 h_a1 hbud using hn_a0 hn_a1
  round_step with case_1_eo__24dt_5fdistinct_5fterms_spec n ih s2 a0 a1 x_a0 x_a1 hinv2 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s3, hinv3, hc1⟩ growing hG carrying h_a0 h_a1 hbud using hn_a0 hn_a1 hc0
  round_step with case_2_eo__24dt_5fdistinct_5fterms_spec n ih s3 a0 a1 x_a0 x_a1 hinv3 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s4, hinv4, hc2⟩ growing hG carrying h_a0 h_a1 hbud using hn_a0 hn_a1 hc0 hc1
  round_step with case_3_eo__24dt_5fdistinct_5fterms_spec n ih s4 a0 a1 x_a0 x_a1 hinv4 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s5, hinv5, hc3⟩ growing hG carrying h_a0 h_a1 hbud using hn_a0 hn_a1 hc0 hc1 hc2
  round_stuck hinv5 hG using hn_a0 hn_a1 hc0 hc1 hc2 hc3 in EoCases.__dt_distinct_terms.case_0 EoCases.__dt_distinct_terms.case_1 EoCases.__dt_distinct_terms.case_2 EoCases.__dt_distinct_terms.case_3

theorem body_eo__24dt_5fdistinct_5fterms_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24dt_5fdistinct_5fterms s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__dt_distinct_terms x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  refine (?_ : ∀ (k : Nat) (a0 a1 : Term) (s : Store) (x_a0 : _) (x_a1 : _), s.budget ≤ k → s.Inv → s.remaining ≤ n →
      Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
      body_eo__24dt_5fdistinct_5fterms s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__dt_distinct_terms x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div) s.budget a0 a1 s x_a0 x_a1 le_rfl hinv hrem h_a0 h_a1
  intro k
  refine Nat.strong_induction_on k ?_
  intro k ihl a0 a1 s x_a0 x_a1 hk hinv hrem h_a0 h_a1
  unfold body_eo__24dt_5fdistinct_5fterms body_eo__24dt_5fdistinct_5fterms_loop
  step with step_eo__24dt_5fdistinct_5fterms_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 as ⟨r, s1, hinv1, hg1, hr⟩
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
      unfold body_eo__24dt_5fdistinct_5fterms at hrec
      apply WP.dspec_mono hrec
      loop_close hg1 heq

theorem eo__24dt_5fdistinct_5fterms_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24dt_5fdistinct_5fterms.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24dt_5fdistinct_5fterms
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 63#u32 _ [a0, a1] rfl
    (fun s1 => body_eo__24dt_5fdistinct_5fterms s1 a0 a1) (fun s' t => Represents.rep s' t (__dt_distinct_terms x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, y0, y1, hargs, hb0, hb1, hr⟩ := ProgramSem.of_63 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_63 ⟨a0, a1, x_a0, x_a1, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24dt_5fdistinct_5fterms_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24dt_5feq_5fcons_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24dt_5feq_5fcons s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__dt_eq_cons.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _), arr.val = [u0, u1] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧
          EoCases.__dt_eq_cons.case_0 x_a0 x_a1 = some (__dt_eq_cons y0 y1)
      | core.result.Result.Ok none => EoCases.__dt_eq_cons.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24dt_5feq_5fcons
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__dt_eq_cons.case_0
  case_again hinv hG with h_v1 h_a1 in EoCases.__dt_eq_cons.case_0 using hn_a0 hn_a1 hn_v1 hn_v2

theorem case_1_eo__24dt_5feq_5fcons_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_1_eo__24dt_5feq_5fcons s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__dt_eq_cons.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _), arr.val = [u0, u1] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧
          EoCases.__dt_eq_cons.case_1 x_a0 x_a1 = some (__dt_eq_cons y0 y1)
      | core.result.Result.Ok none => EoCases.__dt_eq_cons.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24dt_5feq_5fcons
  have hG := Store.Grows.refl s
  pat_unapply h_a1 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__dt_eq_cons.case_1
  case_again hinv hG with h_a0 h_v1 in EoCases.__dt_eq_cons.case_1 using hn_a0 hn_a1 hn_v1 hn_v2

theorem case_2_eo__24dt_5feq_5fcons_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_2_eo__24dt_5feq_5fcons s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__dt_eq_cons.case_2 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _), arr.val = [u0, u1] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧
          EoCases.__dt_eq_cons.case_2 x_a0 x_a1 = some (__dt_eq_cons y0 y1)
      | core.result.Result.Ok none => EoCases.__dt_eq_cons.case_2 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24dt_5feq_5fcons
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_tuple.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  step as ⟨e_v1, he_v1⟩
  store_step with Store.builtin_spec_is_eq s1 e_v1 (by rw [he_v1]; rfl) h_a0 h_v0 hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  have h_ite_v9 := (show if_1_eo__24dt_5feq_5fcons s2 v1 a0 ⦃ r s' => s'.Inv ∧ s2.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_1_eo__24dt_5feq_5fcons
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s2
    rcases Store.boolean_value_term h_v1 with ⟨hx_2, hbv_2⟩ | ⟨hx_2, hbv_2⟩ | ⟨hx_2, hbv_2⟩
    · ite_branch hbv_2
      store_step with Store.literal_boolean_spec s2 true hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1
      ite_done hinv3 hG with (eo_ite_true_rep _ hx_2 h_v2)
    · ite_branch hbv_2
      step as ⟨e_v3, he_v3⟩
      store_step with CtorSpec.eo_tuple_2eunit.construct s2 e_v3 (by rw [he_v3]; exact empty_args) hinv2 h64 as ⟨v3, s3, hinv3, h_v3⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1
      step as ⟨e_v4, he_v4⟩
      store_step with Store.builtin_spec_is_eq s3 e_v4 (by rw [he_v4]; rfl) h_a0 h_v3 hinv3 h64 as ⟨v4, s4, hinv4, h_v4⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v3
      have h_ite_v8 := (show if_0_eo__24dt_5feq_5fcons s4 v4 a0 ⦃ r s' => s'.Inv ∧ s4.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_0_eo__24dt_5feq_5fcons
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s4
        rcases Store.boolean_value_term h_v4 with ⟨hx_5, hbv_5⟩ | ⟨hx_5, hbv_5⟩ | ⟨hx_5, hbv_5⟩
        · ite_branch hbv_5
          store_step with Store.literal_boolean_spec s4 true hinv4 h64 as ⟨v5, s5, hinv5, h_v5⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v3 h_v4
          ite_done hinv5 hG with (eo_ite_true_rep _ hx_5 h_v5)
        · ite_branch hbv_5
          store_step with ih.eo__24eo_5fdt_5fselectors s4 a0 _ hinv4 h64 (hG.rem hrem) h_a0 as ⟨v6, s5, hinv5, h_v6⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v3 h_v4
          step as ⟨e_v7, he_v7⟩
          store_step with Store.builtin_spec_is_ok s5 e_v7 (by rw [he_v7]; rfl) h_v6 hinv5 h64 as ⟨v7, s6, hinv6, h_v7⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v3 h_v4 h_v6
          ite_done hinv6 hG with (eo_ite_false_rep _ hx_5 h_v7)
        · ite_branch hbv_5
          ite_stuck hinv4 hG with hx_5)
      store_step with h_ite_v8 as ⟨v8, s5, hinv5, h_v8⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v3 h_v4
      ite_done hinv5 hG with (eo_ite_false_rep _ hx_2 h_v8)
    · ite_branch hbv_2
      ite_stuck hinv2 hG with hx_2)
  store_step with h_ite_v9 as ⟨v9, s3, hinv3, h_v9⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1
  store_step with Store.literal_boolean_spec s3 true hinv3 h64 as ⟨v10, s4, hinv4, h_v10⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v9
  have h_req_v27 := (show requires_6_eo__24dt_5feq_5fcons s4 v9 v10 a0 a1 ⦃ r s' => s'.Inv ∧ s4.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold requires_6_eo__24dt_5feq_5fcons
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s4
    req_same v9 v10 with h_v9 h_v10 using hinv4 hG
    req_stuck h_v9 as hq_v9 using hinv4 hG
    step as ⟨e_v11, he_v11⟩
    store_step with Store.builtin_spec_eq s4 e_v11 (by rw [he_v11]; rfl) h_a0 h_a1 hinv4 h64 as ⟨v11, s5, hinv5, h_v11⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v9 h_v10
    have h_ite_v26 := (show if_5_eo__24dt_5feq_5fcons s5 v11 a1 ⦃ r s' => s'.Inv ∧ s5.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
      unfold if_5_eo__24dt_5feq_5fcons
      have hrem := (hG.rem hrem)
      have hG := Store.Grows.refl s5
      rcases Store.boolean_value_term h_v11 with ⟨hx_12, hbv_12⟩ | ⟨hx_12, hbv_12⟩ | ⟨hx_12, hbv_12⟩
      · ite_branch hbv_12
        store_step with Store.literal_boolean_spec s5 true hinv5 h64 as ⟨v12, s6, hinv6, h_v12⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v9 h_v10 h_v11
        ite_done hinv6 hG with (eo_ite_true_rep _ hx_12 h_v12)
      · ite_branch hbv_12
        step as ⟨e_v13, he_v13⟩
        store_step with CtorSpec.eo_tuple.construct s5 e_v13 (by rw [he_v13]; exact empty_args) hinv5 h64 as ⟨v13, s6, hinv6, h_v13⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v9 h_v10 h_v11
        step as ⟨e_v14, he_v14⟩
        store_step with Store.builtin_spec_is_eq s6 e_v14 (by rw [he_v14]; rfl) h_a1 h_v13 hinv6 h64 as ⟨v14, s7, hinv7, h_v14⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v9 h_v10 h_v11 h_v13
        have h_ite_v22 := (show if_3_eo__24dt_5feq_5fcons s7 v14 a1 ⦃ r s' => s'.Inv ∧ s7.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
          unfold if_3_eo__24dt_5feq_5fcons
          have hrem := (hG.rem hrem)
          have hG := Store.Grows.refl s7
          rcases Store.boolean_value_term h_v14 with ⟨hx_15, hbv_15⟩ | ⟨hx_15, hbv_15⟩ | ⟨hx_15, hbv_15⟩
          · ite_branch hbv_15
            store_step with Store.literal_boolean_spec s7 true hinv7 h64 as ⟨v15, s8, hinv8, h_v15⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v9 h_v10 h_v11 h_v13 h_v14
            ite_done hinv8 hG with (eo_ite_true_rep _ hx_15 h_v15)
          · ite_branch hbv_15
            step as ⟨e_v16, he_v16⟩
            store_step with CtorSpec.eo_tuple_2eunit.construct s7 e_v16 (by rw [he_v16]; exact empty_args) hinv7 h64 as ⟨v16, s8, hinv8, h_v16⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v9 h_v10 h_v11 h_v13 h_v14
            step as ⟨e_v17, he_v17⟩
            store_step with Store.builtin_spec_is_eq s8 e_v17 (by rw [he_v17]; rfl) h_a1 h_v16 hinv8 h64 as ⟨v17, s9, hinv9, h_v17⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v9 h_v10 h_v11 h_v13 h_v14 h_v16
            have h_ite_v21 := (show if_2_eo__24dt_5feq_5fcons s9 v17 a1 ⦃ r s' => s'.Inv ∧ s9.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
              unfold if_2_eo__24dt_5feq_5fcons
              have hrem := (hG.rem hrem)
              have hG := Store.Grows.refl s9
              rcases Store.boolean_value_term h_v17 with ⟨hx_18, hbv_18⟩ | ⟨hx_18, hbv_18⟩ | ⟨hx_18, hbv_18⟩
              · ite_branch hbv_18
                store_step with Store.literal_boolean_spec s9 true hinv9 h64 as ⟨v18, s10, hinv10, h_v18⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v9 h_v10 h_v11 h_v13 h_v14 h_v16 h_v17
                ite_done hinv10 hG with (eo_ite_true_rep _ hx_18 h_v18)
              · ite_branch hbv_18
                store_step with ih.eo__24eo_5fdt_5fselectors s9 a1 _ hinv9 h64 (hG.rem hrem) h_a1 as ⟨v19, s10, hinv10, h_v19⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v9 h_v10 h_v11 h_v13 h_v14 h_v16 h_v17
                step as ⟨e_v20, he_v20⟩
                store_step with Store.builtin_spec_is_ok s10 e_v20 (by rw [he_v20]; rfl) h_v19 hinv10 h64 as ⟨v20, s11, hinv11, h_v20⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v9 h_v10 h_v11 h_v13 h_v14 h_v16 h_v17 h_v19
                ite_done hinv11 hG with (eo_ite_false_rep _ hx_18 h_v20)
              · ite_branch hbv_18
                ite_stuck hinv9 hG with hx_18)
            store_step with h_ite_v21 as ⟨v21, s10, hinv10, h_v21⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v9 h_v10 h_v11 h_v13 h_v14 h_v16 h_v17
            ite_done hinv10 hG with (eo_ite_false_rep _ hx_15 h_v21)
          · ite_branch hbv_15
            ite_stuck hinv7 hG with hx_15)
        store_step with h_ite_v22 as ⟨v22, s8, hinv8, h_v22⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v9 h_v10 h_v11 h_v13 h_v14
        store_step with Store.literal_boolean_spec s8 true hinv8 h64 as ⟨v23, s9, hinv9, h_v23⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v9 h_v10 h_v11 h_v13 h_v14 h_v22
        have h_req_v25 := (show requires_4_eo__24dt_5feq_5fcons s9 v22 v23 ⦃ r s' => s'.Inv ∧ s9.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
          unfold requires_4_eo__24dt_5feq_5fcons
          have hrem := (hG.rem hrem)
          have hG := Store.Grows.refl s9
          req_same v22 v23 with h_v22 h_v23 using hinv9 hG
          req_stuck h_v22 as hq_v22 using hinv9 hG
          store_step with Store.literal_boolean_spec s9 false hinv9 h64 as ⟨v24, s10, hinv10, h_v24⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v9 h_v10 h_v11 h_v13 h_v14 h_v22 h_v23
          req_done hinv10 hG with h_v24 using hq_v22)
        store_step with h_req_v25 as ⟨v25, s11, hinv11, h_v25⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v9 h_v10 h_v11 h_v13 h_v14 h_v22 h_v23
        ite_done hinv11 hG with (eo_ite_false_rep _ hx_12 h_v25)
      · ite_branch hbv_12
        ite_stuck hinv5 hG with hx_12)
    store_step with h_ite_v26 as ⟨v26, s6, hinv6, h_v26⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v9 h_v10 h_v11
    req_done hinv6 hG with h_v26 using hq_v9)
  store_step with h_req_v27 as ⟨v27, s7, hinv7, h_v27⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v9 h_v10
  case_done hinv7 hG with h_v27 in EoCases.__dt_eq_cons.case_2 using hn_a0 hn_a1

/-- logos's `__dt_eq_cons` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24dt_5feq_5fcons.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __dt_eq_cons x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__dt_eq_cons.case_0 x_a0 x_a1, EoCases.__dt_eq_cons.case_1 x_a0 x_a1, EoCases.__dt_eq_cons.case_2 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __dt_eq_cons
  unfold EoCases.__dt_eq_cons.case_0 EoCases.__dt_eq_cons.case_1 EoCases.__dt_eq_cons.case_2
  logos_eq

theorem step_eo__24dt_5feq_5fcons_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    step_eo__24dt_5feq_5fcons s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (Next.Done t) => Represents.rep s' t (__dt_eq_cons x_a0 x_a1)
      | core.result.Result.Ok (Next.Again arr) =>
        s'.budget < s.budget ∧ ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _), arr.val = [u0, u1] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧
          __dt_eq_cons x_a0 x_a1 = __dt_eq_cons y0 y1
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24dt_5feq_5fcons.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold step_eo__24dt_5feq_5fcons
  have hG := Store.Grows.refl s
  tick_step as ⟨s1, hinv1⟩ growing hG carrying h_a0 h_a1
  stuck_check h_a0 : x_a0 as hn_a0 else hinv1 hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv1 hG
  round_step with case_0_eo__24dt_5feq_5fcons_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s2, hinv2, hc0⟩ growing hG carrying h_a0 h_a1 hbud using hn_a0 hn_a1
  round_step with case_1_eo__24dt_5feq_5fcons_spec n ih s2 a0 a1 x_a0 x_a1 hinv2 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s3, hinv3, hc1⟩ growing hG carrying h_a0 h_a1 hbud using hn_a0 hn_a1 hc0
  round_step with case_2_eo__24dt_5feq_5fcons_spec n ih s3 a0 a1 x_a0 x_a1 hinv3 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s4, hinv4, hc2⟩ growing hG carrying h_a0 h_a1 hbud using hn_a0 hn_a1 hc0 hc1
  round_stuck hinv4 hG using hn_a0 hn_a1 hc0 hc1 hc2 in EoCases.__dt_eq_cons.case_0 EoCases.__dt_eq_cons.case_1 EoCases.__dt_eq_cons.case_2

theorem body_eo__24dt_5feq_5fcons_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24dt_5feq_5fcons s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__dt_eq_cons x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  refine (?_ : ∀ (k : Nat) (a0 a1 : Term) (s : Store) (x_a0 : _) (x_a1 : _), s.budget ≤ k → s.Inv → s.remaining ≤ n →
      Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
      body_eo__24dt_5feq_5fcons s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__dt_eq_cons x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div) s.budget a0 a1 s x_a0 x_a1 le_rfl hinv hrem h_a0 h_a1
  intro k
  refine Nat.strong_induction_on k ?_
  intro k ihl a0 a1 s x_a0 x_a1 hk hinv hrem h_a0 h_a1
  unfold body_eo__24dt_5feq_5fcons body_eo__24dt_5feq_5fcons_loop
  step with step_eo__24dt_5feq_5fcons_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 as ⟨r, s1, hinv1, hg1, hr⟩
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
      unfold body_eo__24dt_5feq_5fcons at hrec
      apply WP.dspec_mono hrec
      loop_close hg1 heq

theorem eo__24dt_5feq_5fcons_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24dt_5feq_5fcons.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24dt_5feq_5fcons
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 64#u32 _ [a0, a1] rfl
    (fun s1 => body_eo__24dt_5feq_5fcons s1 a0 a1) (fun s' t => Represents.rep s' t (__dt_eq_cons x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, y0, y1, hargs, hb0, hb1, hr⟩ := ProgramSem.of_64 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_64 ⟨a0, a1, x_a0, x_a1, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24dt_5feq_5fcons_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24dt_5ffind_5fcycle_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    case_0_eo__24dt_5ffind_5fcycle s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__dt_find_cycle.case_0 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__dt_find_cycle.case_0 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24dt_5ffind_5fcycle
  have hG := Store.Grows.refl s
  pat_same a1 a0 with h_a1 h_a0 using hinv else hinv hG in EoCases.__dt_find_cycle.case_0
  case_done hinv hG with h_a3 in EoCases.__dt_find_cycle.case_0 using hn_a0 hn_a1 hn_a2 hn_a3

theorem case_1_eo__24dt_5ffind_5fcycle_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    case_1_eo__24dt_5ffind_5fcycle s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__dt_find_cycle.case_1 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__dt_find_cycle.case_1 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24dt_5ffind_5fcycle
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__dt_find_cycle.case_1
  store_step with Store.literal_boolean_spec s true hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v2
  pat_same a2 v3 with h_a2 h_v3 using hinv1 else hinv1 hG in EoCases.__dt_find_cycle.case_1
  store_step with ih.eo__24is_5fcons_5fapp s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v2 h_v3
  store_step with Store.literal_boolean_spec s2 true hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v2 h_v3 h_v4
  store_step with ih.eo__24dt_5ffind_5fcycle s3 v2 a1 v4 v5 _ _ _ _ hinv3 h64 (hG.rem hrem) h_v2 h_a1 h_v4 h_v5 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v2 h_v3 h_v4 h_v5
  have h_ite_v10 := (show if_0_eo__24dt_5ffind_5fcycle s4 v6 v1 a1 a3 ⦃ r s' => s'.Inv ∧ s4.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_0_eo__24dt_5ffind_5fcycle
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s4
    rcases Store.boolean_value_term h_v6 with ⟨hx_7, hbv_7⟩ | ⟨hx_7, hbv_7⟩ | ⟨hx_7, hbv_7⟩
    · ite_branch hbv_7
      store_step with Store.literal_boolean_spec s4 true hinv4 h64 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
      ite_done hinv5 hG with (eo_ite_true_rep _ hx_7 h_v7)
    · ite_branch hbv_7
      store_step with Store.literal_boolean_spec s4 true hinv4 h64 as ⟨v8, s5, hinv5, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
      store_step with ih.eo__24dt_5ffind_5fcycle s5 v1 a1 v8 a3 _ _ _ _ hinv5 h64 (hG.rem hrem) h_v1 h_a1 h_v8 h_a3 as ⟨v9, s6, hinv6, h_v9⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v8
      ite_done hinv6 hG with (eo_ite_false_rep _ hx_7 h_v9)
    · ite_branch hbv_7
      ite_stuck hinv4 hG with hx_7)
  store_step with h_ite_v10 as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  case_done hinv5 hG with h_v10 in EoCases.__dt_find_cycle.case_1 using hn_a0 hn_a1 hn_a2 hn_a3 hn_v1 hn_v2

theorem case_2_eo__24dt_5ffind_5fcycle_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    case_2_eo__24dt_5ffind_5fcycle s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__dt_find_cycle.case_2 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__dt_find_cycle.case_2 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24dt_5ffind_5fcycle
  have hG := Store.Grows.refl s
  store_step with Store.literal_boolean_spec s false hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
  case_done hinv1 hG with h_v0 in EoCases.__dt_find_cycle.case_2 using hn_a0 hn_a1 hn_a2 hn_a3

/-- logos's `__dt_find_cycle` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24dt_5ffind_5fcycle.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) :
    __dt_find_cycle x_a0 x_a1 x_a2 x_a3 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__dt_find_cycle.case_0 x_a0 x_a1 x_a2 x_a3, EoCases.__dt_find_cycle.case_1 x_a0 x_a1 x_a2 x_a3, EoCases.__dt_find_cycle.case_2 x_a0 x_a1 x_a2 x_a3] HasStuck.stuck) := by
  conv => lhs; unfold __dt_find_cycle
  unfold EoCases.__dt_find_cycle.case_0 EoCases.__dt_find_cycle.case_1 EoCases.__dt_find_cycle.case_2
  try unfold Eo.__eo_l_1___dt_find_cycle
  logos_eq_deep

theorem body_eo__24dt_5ffind_5fcycle_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) :
    body_eo__24dt_5ffind_5fcycle s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__dt_find_cycle x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24dt_5ffind_5fcycle.rust_eq x_a0 x_a1 x_a2 x_a3 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3)]
  unfold body_eo__24dt_5ffind_5fcycle
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  stuck_check h_a3 : x_a3 as hn_a3 else hinv hG
  case_step with case_0_eo__24dt_5ffind_5fcycle_spec n ih s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2 hn_a3
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 using hn_a0 hn_a1 hn_a2 hn_a3
  case_step with case_1_eo__24dt_5ffind_5fcycle_spec n ih s1 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2 hn_a3
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 using hn_a0 hn_a1 hn_a2 hn_a3 hc0
  case_step with case_2_eo__24dt_5ffind_5fcycle_spec n ih s2 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv2 h64 (hG.rem hrem) h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2 hn_a3
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 using hn_a0 hn_a1 hn_a2 hn_a3 hc0 hc1
  body_stuck hinv3 hG using hn_a0 hn_a1 hn_a2 hn_a3 hc0 hc1 hc2 in EoCases.__dt_find_cycle.case_0 EoCases.__dt_find_cycle.case_1 EoCases.__dt_find_cycle.case_2

theorem eo__24dt_5ffind_5fcycle_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24dt_5ffind_5fcycle.Spec n := by
  intro s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3
  unfold eo__24dt_5ffind_5fcycle
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 65#u32 _ [a0, a1, a2, a3] rfl
    (fun s1 => body_eo__24dt_5ffind_5fcycle s1 a0 a1 a2 a3) (fun s' t => Represents.rep s' t (__dt_find_cycle x_a0 x_a1 x_a2 x_a3))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, b2, b3, y0, y1, y2, y3, hargs, hb0, hb1, hb2, hb3, hr⟩ := ProgramSem.of_65 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      obtain rfl := Rep.functional hb2 (Represents.congr h_a2 hn)
      obtain rfl := Rep.functional hb3 (Represents.congr h_a3 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_65 ⟨a0, a1, a2, a3, x_a0, x_a1, x_a2, x_a3, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, Rep.mono hpre h_a2, Rep.mono hpre h_a3, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24dt_5ffind_5fcycle_spec m (ih m hm) s1 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24dt_5fget_5fconstructors_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24dt_5fget_5fconstructors s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__dt_get_constructors.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__dt_get_constructors.case_0 x_a0 = some (__dt_get_constructors y0)
      | core.result.Result.Ok none => EoCases.__dt_get_constructors.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24dt_5fget_5fconstructors
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__dt_get_constructors.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__dt_get_constructors.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_Tuple.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__dt_get_constructors.case_0
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s1 e_v7 (by rw [he_v7]; exact empty_args) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo_tuple.construct s2 e_v8 (by rw [he_v8]; exact empty_args) hinv2 h64 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with Store.apply_rep s3 v7 v8 _ _ hinv3 h64 h_v7 h_v8 (by ns_tac) (by ns_tac) as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s4 e_v10 (by rw [he_v10]; exact empty_args) hinv4 h64 as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  store_step with Store.apply_rep s5 v9 v10 _ _ hinv5 h64 h_v9 h_v10 (by ns_tac) (by ns_tac) as ⟨v11, s6, hinv6, h_v11⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
  case_done hinv6 hG with h_v11 in EoCases.__dt_get_constructors.case_0 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_1_eo__24dt_5fget_5fconstructors_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_1_eo__24dt_5fget_5fconstructors s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__dt_get_constructors.case_1 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__dt_get_constructors.case_1 x_a0 = some (__dt_get_constructors y0)
      | core.result.Result.Ok none => EoCases.__dt_get_constructors.case_1 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24dt_5fget_5fconstructors
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_UnitTuple.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__dt_get_constructors.case_1
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo_tuple_2eunit.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_v0 h_v1
  store_step with Store.apply_rep s3 v1 v2 _ _ hinv3 h64 h_v1 h_v2 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s4 e_v4 (by rw [he_v4]; exact empty_args) hinv4 h64 as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3
  store_step with Store.apply_rep s5 v3 v4 _ _ hinv5 h64 h_v3 h_v4 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4
  case_done hinv6 hG with h_v5 in EoCases.__dt_get_constructors.case_1 using hn_a0

theorem case_2_eo__24dt_5fget_5fconstructors_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_2_eo__24dt_5fget_5fconstructors s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__dt_get_constructors.case_2 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__dt_get_constructors.case_2 x_a0 = some (__dt_get_constructors y0)
      | core.result.Result.Ok none => EoCases.__dt_get_constructors.case_2 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24dt_5fget_5fconstructors
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__dt_get_constructors.case_2
  case_again hinv hG with h_v1 in EoCases.__dt_get_constructors.case_2 using hn_a0 hn_v1 hn_v2

theorem case_3_eo__24dt_5fget_5fconstructors_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_3_eo__24dt_5fget_5fconstructors s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__dt_get_constructors.case_3 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__dt_get_constructors.case_3 x_a0 = some (__dt_get_constructors y0)
      | core.result.Result.Ok none => EoCases.__dt_get_constructors.case_3 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_3_eo__24dt_5fget_5fconstructors
  have hG := Store.Grows.refl s
  store_step with ih.eo__24eo_5fdt_5fconstructors s a0 _ hinv h64 hrem h_a0 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  case_done hinv1 hG with h_v0 in EoCases.__dt_get_constructors.case_3 using hn_a0

/-- logos's `__dt_get_constructors` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24dt_5fget_5fconstructors.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __dt_get_constructors x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__dt_get_constructors.case_0 x_a0, EoCases.__dt_get_constructors.case_1 x_a0, EoCases.__dt_get_constructors.case_2 x_a0, EoCases.__dt_get_constructors.case_3 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __dt_get_constructors
  unfold EoCases.__dt_get_constructors.case_0 EoCases.__dt_get_constructors.case_1 EoCases.__dt_get_constructors.case_2 EoCases.__dt_get_constructors.case_3
  logos_eq

theorem step_eo__24dt_5fget_5fconstructors_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    step_eo__24dt_5fget_5fconstructors s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (Next.Done t) => Represents.rep s' t (__dt_get_constructors x_a0)
      | core.result.Result.Ok (Next.Again arr) =>
        s'.budget < s.budget ∧ ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          __dt_get_constructors x_a0 = __dt_get_constructors y0
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24dt_5fget_5fconstructors.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold step_eo__24dt_5fget_5fconstructors
  have hG := Store.Grows.refl s
  tick_step as ⟨s1, hinv1⟩ growing hG carrying h_a0
  stuck_check h_a0 : x_a0 as hn_a0 else hinv1 hG
  round_step with case_0_eo__24dt_5fget_5fconstructors_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc0⟩ growing hG carrying h_a0 hbud using hn_a0
  round_step with case_1_eo__24dt_5fget_5fconstructors_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc1⟩ growing hG carrying h_a0 hbud using hn_a0 hc0
  round_step with case_2_eo__24dt_5fget_5fconstructors_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s4, hinv4, hc2⟩ growing hG carrying h_a0 hbud using hn_a0 hc0 hc1
  round_step with case_3_eo__24dt_5fget_5fconstructors_spec n ih s4 a0 x_a0 hinv4 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s5, hinv5, hc3⟩ growing hG carrying h_a0 hbud using hn_a0 hc0 hc1 hc2
  round_stuck hinv5 hG using hn_a0 hc0 hc1 hc2 hc3 in EoCases.__dt_get_constructors.case_0 EoCases.__dt_get_constructors.case_1 EoCases.__dt_get_constructors.case_2 EoCases.__dt_get_constructors.case_3

theorem body_eo__24dt_5fget_5fconstructors_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24dt_5fget_5fconstructors s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__dt_get_constructors x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  refine (?_ : ∀ (k : Nat) (a0 : Term) (s : Store) (x_a0 : _), s.budget ≤ k → s.Inv → s.remaining ≤ n →
      Represents.rep s a0 x_a0 →
      body_eo__24dt_5fget_5fconstructors s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__dt_get_constructors x_a0)
      | core.result.Result.Err _ => True ⦄div) s.budget a0 s x_a0 le_rfl hinv hrem h_a0
  intro k
  refine Nat.strong_induction_on k ?_
  intro k ihl a0 s x_a0 hk hinv hrem h_a0
  unfold body_eo__24dt_5fget_5fconstructors body_eo__24dt_5fget_5fconstructors_loop
  step with step_eo__24dt_5fget_5fconstructors_spec n ih s a0 x_a0 hinv h64 hrem h_a0 as ⟨r, s1, hinv1, hg1, hr⟩
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
      unfold body_eo__24dt_5fget_5fconstructors at hrec
      apply WP.dspec_mono hrec
      loop_close hg1 heq

theorem eo__24dt_5fget_5fconstructors_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24dt_5fget_5fconstructors.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24dt_5fget_5fconstructors
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 66#u32 _ [a0] rfl
    (fun s1 => body_eo__24dt_5fget_5fconstructors s1 a0) (fun s' t => Represents.rep s' t (__dt_get_constructors x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, y0, hargs, hb0, hr⟩ := ProgramSem.of_66 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_66 ⟨a0, x_a0, rfl, Rep.mono hpre h_a0, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24dt_5fget_5fconstructors_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24dt_5fget_5fselectors_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24dt_5fget_5fselectors s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__dt_get_selectors.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__dt_get_selectors.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24dt_5fget_5fselectors
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__dt_get_selectors.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__dt_get_selectors.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_Tuple.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__dt_get_selectors.case_0
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo_tuple.construct s1 e_v7 (by rw [he_v7]; exact empty_args) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6
  pat_same a1 v7 with h_a1 h_v7 using hinv2 else hinv2 hG in EoCases.__dt_get_selectors.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo_Tuple.construct s2 e_v8 (by rw [he_v8]; exact empty_args) hinv2 h64 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with Store.apply_rep s3 v8 v5 _ _ hinv3 h64 h_v8 h_v5 (by ns_tac) (by ns_tac) as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  store_step with Store.apply_rep s4 v9 v2 _ _ hinv4 h64 h_v9 h_v2 (by ns_tac) (by ns_tac) as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s5 0#u32 (0) (by scalar_tac) hinv5 h64 as ⟨v11, s6, hinv6, h_v11⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
  store_step with ih.eo__24tuple_5fget_5fselectors_5frec s6 v10 v11 _ _ hinv6 h64 (hG.rem hrem) h_v10 h_v11 as ⟨v12, s7, hinv7, h_v12⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11
  case_done hinv7 hG with h_v12 in EoCases.__dt_get_selectors.case_0 using hn_a0 hn_a1 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_1_eo__24dt_5fget_5fselectors_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_1_eo__24dt_5fget_5fselectors s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__dt_get_selectors.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__dt_get_selectors.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24dt_5fget_5fselectors
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_UnitTuple.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__dt_get_selectors.case_1
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_tuple_2eunit.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  pat_same a1 v1 with h_a1 h_v1 using hinv2 else hinv2 hG in EoCases.__dt_get_selectors.case_1
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1
  case_done hinv3 hG with h_v2 in EoCases.__dt_get_selectors.case_1 using hn_a0 hn_a1

theorem case_2_eo__24dt_5fget_5fselectors_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_2_eo__24dt_5fget_5fselectors s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__dt_get_selectors.case_2 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__dt_get_selectors.case_2 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24dt_5fget_5fselectors
  have hG := Store.Grows.refl s
  store_step with ih.eo__24eo_5fdt_5fselectors s a1 _ hinv h64 hrem h_a1 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  case_done hinv1 hG with h_v0 in EoCases.__dt_get_selectors.case_2 using hn_a0 hn_a1

/-- logos's `__dt_get_selectors` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24dt_5fget_5fselectors.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __dt_get_selectors x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__dt_get_selectors.case_0 x_a0 x_a1, EoCases.__dt_get_selectors.case_1 x_a0 x_a1, EoCases.__dt_get_selectors.case_2 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __dt_get_selectors
  unfold EoCases.__dt_get_selectors.case_0 EoCases.__dt_get_selectors.case_1 EoCases.__dt_get_selectors.case_2
  logos_eq

theorem body_eo__24dt_5fget_5fselectors_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24dt_5fget_5fselectors s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__dt_get_selectors x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24dt_5fget_5fselectors.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24dt_5fget_5fselectors
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24dt_5fget_5fselectors_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  case_step with case_1_eo__24dt_5fget_5fselectors_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1 hc0
  case_step with case_2_eo__24dt_5fget_5fselectors_spec n ih s2 a0 a1 x_a0 x_a1 hinv2 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1 hc0 hc1
  body_stuck hinv3 hG using hn_a0 hn_a1 hc0 hc1 hc2 in EoCases.__dt_get_selectors.case_0 EoCases.__dt_get_selectors.case_1 EoCases.__dt_get_selectors.case_2

theorem eo__24dt_5fget_5fselectors_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24dt_5fget_5fselectors.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24dt_5fget_5fselectors
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24dt_5fget_5fselectors s1 a0 a1) (fun s' t => Represents.rep s' t (__dt_get_selectors x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24dt_5fget_5fselectors_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24dt_5fget_5fselectors_5fof_5fapp_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24dt_5fget_5fselectors_5fof_5fapp s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__dt_get_selectors_of_app.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _), arr.val = [u0, u1] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧
          EoCases.__dt_get_selectors_of_app.case_0 x_a0 x_a1 = some (__dt_get_selectors_of_app y0 y1)
      | core.result.Result.Ok none => EoCases.__dt_get_selectors_of_app.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24dt_5fget_5fselectors_5fof_5fapp
  have hG := Store.Grows.refl s
  pat_unapply h_a1 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__dt_get_selectors_of_app.case_0
  case_again hinv hG with h_a0 h_v1 in EoCases.__dt_get_selectors_of_app.case_0 using hn_a0 hn_a1 hn_v1 hn_v2

theorem case_1_eo__24dt_5fget_5fselectors_5fof_5fapp_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_1_eo__24dt_5fget_5fselectors_5fof_5fapp s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__dt_get_selectors_of_app.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _), arr.val = [u0, u1] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧
          EoCases.__dt_get_selectors_of_app.case_1 x_a0 x_a1 = some (__dt_get_selectors_of_app y0 y1)
      | core.result.Result.Ok none => EoCases.__dt_get_selectors_of_app.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24dt_5fget_5fselectors_5fof_5fapp
  have hG := Store.Grows.refl s
  store_step with ih.eo__24dt_5fget_5fselectors s a0 a1 _ _ hinv h64 hrem h_a0 h_a1 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  case_done hinv1 hG with h_v0 in EoCases.__dt_get_selectors_of_app.case_1 using hn_a0 hn_a1

/-- logos's `__dt_get_selectors_of_app` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24dt_5fget_5fselectors_5fof_5fapp.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __dt_get_selectors_of_app x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__dt_get_selectors_of_app.case_0 x_a0 x_a1, EoCases.__dt_get_selectors_of_app.case_1 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __dt_get_selectors_of_app
  unfold EoCases.__dt_get_selectors_of_app.case_0 EoCases.__dt_get_selectors_of_app.case_1
  logos_eq

theorem step_eo__24dt_5fget_5fselectors_5fof_5fapp_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    step_eo__24dt_5fget_5fselectors_5fof_5fapp s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (Next.Done t) => Represents.rep s' t (__dt_get_selectors_of_app x_a0 x_a1)
      | core.result.Result.Ok (Next.Again arr) =>
        s'.budget < s.budget ∧ ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _), arr.val = [u0, u1] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧
          __dt_get_selectors_of_app x_a0 x_a1 = __dt_get_selectors_of_app y0 y1
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24dt_5fget_5fselectors_5fof_5fapp.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold step_eo__24dt_5fget_5fselectors_5fof_5fapp
  have hG := Store.Grows.refl s
  tick_step as ⟨s1, hinv1⟩ growing hG carrying h_a0 h_a1
  stuck_check h_a0 : x_a0 as hn_a0 else hinv1 hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv1 hG
  round_step with case_0_eo__24dt_5fget_5fselectors_5fof_5fapp_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s2, hinv2, hc0⟩ growing hG carrying h_a0 h_a1 hbud using hn_a0 hn_a1
  round_step with case_1_eo__24dt_5fget_5fselectors_5fof_5fapp_spec n ih s2 a0 a1 x_a0 x_a1 hinv2 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s3, hinv3, hc1⟩ growing hG carrying h_a0 h_a1 hbud using hn_a0 hn_a1 hc0
  round_stuck hinv3 hG using hn_a0 hn_a1 hc0 hc1 in EoCases.__dt_get_selectors_of_app.case_0 EoCases.__dt_get_selectors_of_app.case_1

theorem body_eo__24dt_5fget_5fselectors_5fof_5fapp_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24dt_5fget_5fselectors_5fof_5fapp s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__dt_get_selectors_of_app x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  refine (?_ : ∀ (k : Nat) (a0 a1 : Term) (s : Store) (x_a0 : _) (x_a1 : _), s.budget ≤ k → s.Inv → s.remaining ≤ n →
      Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
      body_eo__24dt_5fget_5fselectors_5fof_5fapp s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__dt_get_selectors_of_app x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div) s.budget a0 a1 s x_a0 x_a1 le_rfl hinv hrem h_a0 h_a1
  intro k
  refine Nat.strong_induction_on k ?_
  intro k ihl a0 a1 s x_a0 x_a1 hk hinv hrem h_a0 h_a1
  unfold body_eo__24dt_5fget_5fselectors_5fof_5fapp body_eo__24dt_5fget_5fselectors_5fof_5fapp_loop
  step with step_eo__24dt_5fget_5fselectors_5fof_5fapp_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 as ⟨r, s1, hinv1, hg1, hr⟩
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
      unfold body_eo__24dt_5fget_5fselectors_5fof_5fapp at hrec
      apply WP.dspec_mono hrec
      loop_close hg1 heq

theorem eo__24dt_5fget_5fselectors_5fof_5fapp_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24dt_5fget_5fselectors_5fof_5fapp.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24dt_5fget_5fselectors_5fof_5fapp
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 68#u32 _ [a0, a1] rfl
    (fun s1 => body_eo__24dt_5fget_5fselectors_5fof_5fapp s1 a0 a1) (fun s' t => Represents.rep s' t (__dt_get_selectors_of_app x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, y0, y1, hargs, hb0, hb1, hr⟩ := ProgramSem.of_68 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_68 ⟨a0, a1, x_a0, x_a1, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24dt_5fget_5fselectors_5fof_5fapp_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24dt_5fupdater_5felim_5frhs_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24dt_5fupdater_5felim_5frhs s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__dt_updater_elim_rhs.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _), arr.val = [u0, u1, u2] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧
          EoCases.__dt_updater_elim_rhs.case_0 x_a0 x_a1 x_a2 = some (__dt_updater_elim_rhs y0 y1 y2)
      | core.result.Result.Ok none => EoCases.__dt_updater_elim_rhs.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24dt_5fupdater_5felim_5frhs
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__dt_updater_elim_rhs.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__dt_updater_elim_rhs.case_0
  pat_destruct CtorSpec.eo_update.destruct h_v4 as ⟨v7, x_v7, h_v7⟩ else hinv hG in EoCases.__dt_updater_elim_rhs.case_0
  obtain hn_v7 := CtorSpec.eo_update.fields_ne_stuck hinv h_v4
  pat_unapply h_a1 as ⟨v9, v10, x_v9, x_v10, h_v9, h_v10, hn_v9, hn_v10⟩ using hinv else hinv hG in EoCases.__dt_updater_elim_rhs.case_0
  pat_unapply h_v9 as ⟨v12, v13, x_v12, x_v13, h_v12, h_v13, hn_v12, hn_v13⟩ using hinv else hinv hG in EoCases.__dt_updater_elim_rhs.case_0
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s e_v14 (by rw [he_v14]; exact empty_args) hinv h64 as ⟨v14, s1, hinv1, h_v14⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v9 h_v10 h_v12 h_v13
  pat_same v12 v14 with h_v12 h_v14 using hinv1 else hinv1 hG in EoCases.__dt_updater_elim_rhs.case_0
  pat_same v13 v7 with h_v13 h_v7 using hinv1 else hinv1 hG in EoCases.__dt_updater_elim_rhs.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo_update.construct s1 e_v15 (by rw [he_v15]; rfl) h_v7 hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14
  store_step with Store.apply_rep s2 v15 v5 _ _ hinv2 h64 h_v15 h_v5 (by ns_tac) (by ns_tac) as ⟨v16, s3, hinv3, h_v16⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14 h_v15
  store_step with Store.apply_rep s3 v16 v2 _ _ hinv3 h64 h_v16 h_v2 (by ns_tac) (by ns_tac) as ⟨v17, s4, hinv4, h_v17⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14 h_v15 h_v16
  store_step with Store.apply_rep s4 a2 v2 _ _ hinv4 h64 h_a2 h_v2 (by ns_tac) (by ns_tac) as ⟨v18, s5, hinv5, h_v18⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17
  case_again hinv5 hG with h_v17 h_v10 h_v18 in EoCases.__dt_updater_elim_rhs.case_0 using hn_a0 hn_a1 hn_a2 hn_v1 hn_v2 hn_v4 hn_v5 hn_v7 hn_v9 hn_v10 hn_v12 hn_v13

theorem case_1_eo__24dt_5fupdater_5felim_5frhs_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_1_eo__24dt_5fupdater_5felim_5frhs s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__dt_updater_elim_rhs.case_1 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _), arr.val = [u0, u1, u2] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧
          EoCases.__dt_updater_elim_rhs.case_1 x_a0 x_a1 x_a2 = some (__dt_updater_elim_rhs y0 y1 y2)
      | core.result.Result.Ok none => EoCases.__dt_updater_elim_rhs.case_1 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24dt_5fupdater_5felim_5frhs
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__dt_updater_elim_rhs.case_1
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__dt_updater_elim_rhs.case_1
  pat_destruct CtorSpec.eo_update.destruct h_v4 as ⟨v7, x_v7, h_v7⟩ else hinv hG in EoCases.__dt_updater_elim_rhs.case_1
  obtain hn_v7 := CtorSpec.eo_update.fields_ne_stuck hinv h_v4
  pat_unapply h_a1 as ⟨v9, v10, x_v9, x_v10, h_v9, h_v10, hn_v9, hn_v10⟩ using hinv else hinv hG in EoCases.__dt_updater_elim_rhs.case_1
  pat_unapply h_v9 as ⟨v12, v13, x_v12, x_v13, h_v12, h_v13, hn_v12, hn_v13⟩ using hinv else hinv hG in EoCases.__dt_updater_elim_rhs.case_1
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s e_v14 (by rw [he_v14]; exact empty_args) hinv h64 as ⟨v14, s1, hinv1, h_v14⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v9 h_v10 h_v12 h_v13
  pat_same v12 v14 with h_v12 h_v14 using hinv1 else hinv1 hG in EoCases.__dt_updater_elim_rhs.case_1
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo_update.construct s1 e_v15 (by rw [he_v15]; rfl) h_v7 hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14
  store_step with Store.apply_rep s2 v15 v5 _ _ hinv2 h64 h_v15 h_v5 (by ns_tac) (by ns_tac) as ⟨v16, s3, hinv3, h_v16⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14 h_v15
  store_step with Store.apply_rep s3 v16 v2 _ _ hinv3 h64 h_v16 h_v2 (by ns_tac) (by ns_tac) as ⟨v17, s4, hinv4, h_v17⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14 h_v15 h_v16
  store_step with Store.apply_rep s4 v13 v5 _ _ hinv4 h64 h_v13 h_v5 (by ns_tac) (by ns_tac) as ⟨v18, s5, hinv5, h_v18⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17
  store_step with Store.apply_rep s5 a2 v18 _ _ hinv5 h64 h_a2 h_v18 (by ns_tac) (by ns_tac) as ⟨v19, s6, hinv6, h_v19⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18
  case_again hinv6 hG with h_v17 h_v10 h_v19 in EoCases.__dt_updater_elim_rhs.case_1 using hn_a0 hn_a1 hn_a2 hn_v1 hn_v2 hn_v4 hn_v5 hn_v7 hn_v9 hn_v10 hn_v12 hn_v13

theorem case_2_eo__24dt_5fupdater_5felim_5frhs_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_2_eo__24dt_5fupdater_5felim_5frhs s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__dt_updater_elim_rhs.case_2 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _), arr.val = [u0, u1, u2] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧
          EoCases.__dt_updater_elim_rhs.case_2 x_a0 x_a1 x_a2 = some (__dt_updater_elim_rhs y0 y1 y2)
      | core.result.Result.Ok none => EoCases.__dt_updater_elim_rhs.case_2 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24dt_5fupdater_5felim_5frhs
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__dt_updater_elim_rhs.case_2
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__dt_updater_elim_rhs.case_2
  pat_destruct CtorSpec.eo_update.destruct h_v4 as ⟨v7, x_v7, h_v7⟩ else hinv hG in EoCases.__dt_updater_elim_rhs.case_2
  obtain hn_v7 := CtorSpec.eo_update.fields_ne_stuck hinv h_v4
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7
  pat_same a1 v8 with h_a1 h_v8 using hinv1 else hinv1 hG in EoCases.__dt_updater_elim_rhs.case_2
  case_done hinv1 hG with h_a2 in EoCases.__dt_updater_elim_rhs.case_2 using hn_a0 hn_a1 hn_a2 hn_v1 hn_v2 hn_v4 hn_v5 hn_v7

/-- logos's `__dt_updater_elim_rhs` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24dt_5fupdater_5felim_5frhs.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __dt_updater_elim_rhs x_a0 x_a1 x_a2 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__dt_updater_elim_rhs.case_0 x_a0 x_a1 x_a2, EoCases.__dt_updater_elim_rhs.case_1 x_a0 x_a1 x_a2, EoCases.__dt_updater_elim_rhs.case_2 x_a0 x_a1 x_a2] HasStuck.stuck) := by
  conv => lhs; unfold __dt_updater_elim_rhs
  unfold EoCases.__dt_updater_elim_rhs.case_0 EoCases.__dt_updater_elim_rhs.case_1 EoCases.__dt_updater_elim_rhs.case_2
  try unfold Eo.__eo_l_1___dt_updater_elim_rhs
  logos_eq_deep

theorem step_eo__24dt_5fupdater_5felim_5frhs_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    step_eo__24dt_5fupdater_5felim_5frhs s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (Next.Done t) => Represents.rep s' t (__dt_updater_elim_rhs x_a0 x_a1 x_a2)
      | core.result.Result.Ok (Next.Again arr) =>
        s'.budget < s.budget ∧ ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _), arr.val = [u0, u1, u2] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧
          __dt_updater_elim_rhs x_a0 x_a1 x_a2 = __dt_updater_elim_rhs y0 y1 y2
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24dt_5fupdater_5felim_5frhs.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold step_eo__24dt_5fupdater_5felim_5frhs
  have hG := Store.Grows.refl s
  tick_step as ⟨s1, hinv1⟩ growing hG carrying h_a0 h_a1 h_a2
  stuck_check h_a0 : x_a0 as hn_a0 else hinv1 hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv1 hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv1 hG
  round_step with case_0_eo__24dt_5fupdater_5felim_5frhs_spec n ih s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s2, hinv2, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 hbud using hn_a0 hn_a1 hn_a2
  round_step with case_1_eo__24dt_5fupdater_5felim_5frhs_spec n ih s2 a0 a1 a2 x_a0 x_a1 x_a2 hinv2 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s3, hinv3, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 hbud using hn_a0 hn_a1 hn_a2 hc0
  round_step with case_2_eo__24dt_5fupdater_5felim_5frhs_spec n ih s3 a0 a1 a2 x_a0 x_a1 x_a2 hinv3 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s4, hinv4, hc2⟩ growing hG carrying h_a0 h_a1 h_a2 hbud using hn_a0 hn_a1 hn_a2 hc0 hc1
  round_stuck hinv4 hG using hn_a0 hn_a1 hn_a2 hc0 hc1 hc2 in EoCases.__dt_updater_elim_rhs.case_0 EoCases.__dt_updater_elim_rhs.case_1 EoCases.__dt_updater_elim_rhs.case_2

theorem body_eo__24dt_5fupdater_5felim_5frhs_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24dt_5fupdater_5felim_5frhs s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__dt_updater_elim_rhs x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  refine (?_ : ∀ (k : Nat) (a0 a1 a2 : Term) (s : Store) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.budget ≤ k → s.Inv → s.remaining ≤ n →
      Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
      body_eo__24dt_5fupdater_5felim_5frhs s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__dt_updater_elim_rhs x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div) s.budget a0 a1 a2 s x_a0 x_a1 x_a2 le_rfl hinv hrem h_a0 h_a1 h_a2
  intro k
  refine Nat.strong_induction_on k ?_
  intro k ihl a0 a1 a2 s x_a0 x_a1 x_a2 hk hinv hrem h_a0 h_a1 h_a2
  unfold body_eo__24dt_5fupdater_5felim_5frhs body_eo__24dt_5fupdater_5felim_5frhs_loop
  step with step_eo__24dt_5fupdater_5felim_5frhs_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 as ⟨r, s1, hinv1, hg1, hr⟩
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
      unfold body_eo__24dt_5fupdater_5felim_5frhs at hrec
      apply WP.dspec_mono hrec
      loop_close hg1 heq

theorem eo__24dt_5fupdater_5felim_5frhs_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24dt_5fupdater_5felim_5frhs.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24dt_5fupdater_5felim_5frhs
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 69#u32 _ [a0, a1, a2] rfl
    (fun s1 => body_eo__24dt_5fupdater_5felim_5frhs s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__dt_updater_elim_rhs x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, b2, y0, y1, y2, hargs, hb0, hb1, hb2, hr⟩ := ProgramSem.of_69 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      obtain rfl := Rep.functional hb2 (Represents.congr h_a2 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_69 ⟨a0, a1, a2, x_a0, x_a1, x_a2, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, Rep.mono hpre h_a2, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24dt_5fupdater_5felim_5frhs_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fStateObj_5fproven_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24eo_5fStateObj_5fproven s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_StateObj_proven.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_StateObj_proven.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fStateObj_5fproven
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fso_2eassume.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_StateObj_proven.case_0
  case_done hinv hG with h_v1 in EoCases.__eo_StateObj_proven.case_0 using

theorem case_1_eo__24eo_5fStateObj_5fproven_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_1_eo__24eo_5fStateObj_5fproven s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_StateObj_proven.case_1 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_StateObj_proven.case_1 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24eo_5fStateObj_5fproven
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fso_2eassume_5fpush.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_StateObj_proven.case_1
  case_done hinv hG with h_v1 in EoCases.__eo_StateObj_proven.case_1 using

theorem case_2_eo__24eo_5fStateObj_5fproven_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_2_eo__24eo_5fStateObj_5fproven s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_StateObj_proven.case_2 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_StateObj_proven.case_2 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24eo_5fStateObj_5fproven
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fso_2eproven.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_StateObj_proven.case_2
  case_done hinv hG with h_v1 in EoCases.__eo_StateObj_proven.case_2 using

/-- logos's `__eo_StateObj_proven` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fStateObj_5fproven.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_StateObj_proven x_a0 =
      (firstSome [EoCases.__eo_StateObj_proven.case_0 x_a0, EoCases.__eo_StateObj_proven.case_1 x_a0, EoCases.__eo_StateObj_proven.case_2 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_StateObj_proven
  unfold EoCases.__eo_StateObj_proven.case_0 EoCases.__eo_StateObj_proven.case_1 EoCases.__eo_StateObj_proven.case_2
  logos_eq

theorem body_eo__24eo_5fStateObj_5fproven_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fStateObj_5fproven s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_StateObj_proven x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fStateObj_5fproven.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fStateObj_5fproven
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fStateObj_5fproven_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using
  case_step with case_1_eo__24eo_5fStateObj_5fproven_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 using hc0
  case_step with case_2_eo__24eo_5fStateObj_5fproven_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0 using hc0 hc1
  body_stuck hinv3 hG using hc0 hc1 hc2 in EoCases.__eo_StateObj_proven.case_0 EoCases.__eo_StateObj_proven.case_1 EoCases.__eo_StateObj_proven.case_2

theorem eo__24eo_5fStateObj_5fproven_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fStateObj_5fproven.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fStateObj_5fproven
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fStateObj_5fproven s1 a0) (fun s' t => Represents.rep s' t (__eo_StateObj_proven x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fStateObj_5fproven_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fcmd_5fstep_5fpop_5fproven_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (hg_a0 : StateOK x_a0) :
    case_0_eo__24eo_5fcmd_5fstep_5fpop_5fproven s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_cmd_step_pop_proven.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_cmd_step_pop_proven.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fcmd_5fstep_5fpop_5fproven
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fr_2escope.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4
  pat_same a1 v0 with h_a1 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_cmd_step_pop_proven.case_0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24emb_5fal_2enil.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v0
  pat_same a2 v1 with h_a2 h_v1 using hinv2 else hinv2 hG in EoCases.__eo_cmd_step_pop_proven.case_0
  pat_destruct CtorSpec.eo__24emb_5findl_2econs.destruct h_a4 as ⟨v3, x_v3, h_v3⟩ ⟨v4, x_v4, h_v4⟩ else hinv2 hG in EoCases.__eo_cmd_step_pop_proven.case_0
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5findl_2enil.construct s2 e_v5 (by rw [he_v5]; exact empty_args) hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v0 h_v1 h_v3 h_v4
  pat_same v4 v5 with h_v4 h_v5 using hinv3 else hinv3 hG in EoCases.__eo_cmd_step_pop_proven.case_0
  store_step with ih.eo__24eo_5fstate_5fproven_5fnth s3 a0 v3 _ _ hinv3 h64 (hG.rem hrem) h_a0 h_v3 (by good_tac) as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v0 h_v1 h_v3 h_v4 h_v5
  have hn_v6 := state_proven_nth_ne_stuck_of h_v6 (by good_tac)
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo__24eo_5fpf.construct s4 e_v7 (by rw [he_v7]; rfl) h_v6 hinv4 h64 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v0 h_v1 h_v3 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5fprog_5fscope s5 a3 v7 _ _ hinv5 h64 (hG.rem hrem) h_a3 h_v7 (by good_tac) as ⟨v8, s6, hinv6, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v0 h_v1 h_v3 h_v4 h_v5 h_v6 h_v7
  case_done hinv6 hG with h_v8 in EoCases.__eo_cmd_step_pop_proven.case_0 using hn_v6

theorem case_1_eo__24eo_5fcmd_5fstep_5fpop_5fproven_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (hg_a0 : StateOK x_a0) :
    case_1_eo__24eo_5fcmd_5fstep_5fpop_5fproven s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_cmd_step_pop_proven.case_1 x_a0 x_a1 x_a2 x_a3 x_a4 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_cmd_step_pop_proven.case_1 x_a0 x_a1 x_a2 x_a3 x_a4 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24eo_5fcmd_5fstep_5fpop_5fproven
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with Store.construct_stuck_spec s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4
  case_done hinv1 hG with h_v0 in EoCases.__eo_cmd_step_pop_proven.case_1 using

/-- logos's `__eo_cmd_step_pop_proven` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fcmd_5fstep_5fpop_5fproven.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) (hw_a4 : Valid.valid x_a4) :
    __eo_cmd_step_pop_proven x_a0 x_a1 x_a2 x_a3 x_a4 =
      (firstSome [EoCases.__eo_cmd_step_pop_proven.case_0 x_a0 x_a1 x_a2 x_a3 x_a4, EoCases.__eo_cmd_step_pop_proven.case_1 x_a0 x_a1 x_a2 x_a3 x_a4] HasStuck.stuck) := by
  conv => lhs; unfold __eo_cmd_step_pop_proven
  unfold EoCases.__eo_cmd_step_pop_proven.case_0 EoCases.__eo_cmd_step_pop_proven.case_1
  logos_eq

theorem body_eo__24eo_5fcmd_5fstep_5fpop_5fproven_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (hg_a0 : StateOK x_a0) :
    body_eo__24eo_5fcmd_5fstep_5fpop_5fproven s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_cmd_step_pop_proven x_a0 x_a1 x_a2 x_a3 x_a4)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fcmd_5fstep_5fpop_5fproven.rust_eq x_a0 x_a1 x_a2 x_a3 x_a4 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3) (by valid_tac hinv h_a4)]
  unfold body_eo__24eo_5fcmd_5fstep_5fpop_5fproven
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fcmd_5fstep_5fpop_5fproven_spec n ih s a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 hg_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 using
  case_step with case_1_eo__24eo_5fcmd_5fstep_5fpop_5fproven_spec n ih s1 a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 h_a3 h_a4 hg_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 using hc0
  body_stuck hinv2 hG using hc0 hc1 in EoCases.__eo_cmd_step_pop_proven.case_0 EoCases.__eo_cmd_step_pop_proven.case_1

theorem eo__24eo_5fcmd_5fstep_5fpop_5fproven_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fcmd_5fstep_5fpop_5fproven.Spec n := by
  intro s a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 hg_a0
  unfold eo__24eo_5fcmd_5fstep_5fpop_5fproven
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fcmd_5fstep_5fpop_5fproven s1 a0 a1 a2 a3 a4) (fun s' t => Represents.rep s' t (__eo_cmd_step_pop_proven x_a0 x_a1 x_a2 x_a3 x_a4))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fcmd_5fstep_5fpop_5fproven_spec m (ih m hm) s1 a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn) (by congr_one h_a4 hn) hg_a0))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fdatatype_5fcons_5fselectors_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) :
    case_0_eo__24eo_5fdatatype_5fcons_5fselectors_5frec s a0 a1 a2 a3 a4 a5 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__eo_datatype_cons_selectors_rec.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _) (u3 : Term) (y3 : _) (u4 : Term) (y4 : _) (u5 : Term) (y5 : _), arr.val = [u0, u1, u2, u3, u4, u5] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧ Represents.rep s' u3 y3 ∧ Represents.rep s' u4 y4 ∧ Represents.rep s' u5 y5 ∧
          EoCases.__eo_datatype_cons_selectors_rec.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 = some (__eo_datatype_cons_selectors_rec y0 y1 y2 y3 y4 y5)
      | core.result.Result.Ok none => EoCases.__eo_datatype_cons_selectors_rec.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fdatatype_5fcons_5fselectors_5frec
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fedt_2esum.destruct h_a3 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__eo_datatype_cons_selectors_rec.case_0
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__24emb_5fedtc_2eunit.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_datatype_cons_selectors_rec.case_0
  pat_native_zero Store.native_pattern_nat_zero_spec s1 a4 h_a4 hinv1 h64 storing ⟨s2, hinv2⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v3 in EoCases.__eo_datatype_cons_selectors_rec.case_0
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s2 e_v5 (by rw [he_v5]; exact empty_args) hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v3
  case_done hinv3 hG with h_v5 in EoCases.__eo_datatype_cons_selectors_rec.case_0 using

theorem case_1_eo__24eo_5fdatatype_5fcons_5fselectors_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) :
    case_1_eo__24eo_5fdatatype_5fcons_5fselectors_5frec s a0 a1 a2 a3 a4 a5 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__eo_datatype_cons_selectors_rec.case_1 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _) (u3 : Term) (y3 : _) (u4 : Term) (y4 : _) (u5 : Term) (y5 : _), arr.val = [u0, u1, u2, u3, u4, u5] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧ Represents.rep s' u3 y3 ∧ Represents.rep s' u4 y4 ∧ Represents.rep s' u5 y5 ∧
          EoCases.__eo_datatype_cons_selectors_rec.case_1 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 = some (__eo_datatype_cons_selectors_rec y0 y1 y2 y3 y4 y5)
      | core.result.Result.Ok none => EoCases.__eo_datatype_cons_selectors_rec.case_1 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24eo_5fdatatype_5fcons_5fselectors_5frec
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fedt_2esum.destruct h_a3 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__eo_datatype_cons_selectors_rec.case_1
  pat_destruct CtorSpec.eo__24emb_5fedtc_2econs.destruct h_v1 as ⟨v4, x_v4, h_v4⟩ ⟨v5, x_v5, h_v5⟩ else hinv hG in EoCases.__eo_datatype_cons_selectors_rec.case_1
  pat_native_zero Store.native_pattern_nat_zero_spec s a4 h_a4 hinv h64 storing ⟨s1, hinv1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 in EoCases.__eo_datatype_cons_selectors_rec.case_1
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s1 e_v7 (by rw [he_v7]; exact empty_args) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__24emb_5fDtSel.construct s2 e_v8 (by rw [he_v8]; rfl) h_a0 h_a1 h_a2 h_a5 hinv2 h64 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v7
  store_step with Store.apply_rep s3 v7 v8 _ _ hinv3 h64 h_v7 h_v8 (by ns_tac) (by ns_tac) as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo__24emb_5fedt_2esum.construct s4 e_v10 (by rw [he_v10]; rfl) h_v5 h_v2 hinv4 h64 as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9
  store_step with Store.native_nat_zero_spec s5 hinv5 h64 as ⟨v11, s6, hinv6, h_v11⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10
  step as ⟨e_v12, he_v12⟩
  store_step with Store.native_spec_nat_succ s6 e_v12 (by rw [he_v12]; rfl) h_a5 hinv6 h64 as ⟨v12, s7, hinv7, h_v12⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11
  store_step with ih.eo__24eo_5fdatatype_5fcons_5fselectors_5frec s7 a0 a1 a2 v10 v11 v12 _ _ _ _ _ _ hinv7 h64 (hG.rem hrem) h_a0 h_a1 h_a2 h_v10 h_v11 h_v12 as ⟨v13, s8, hinv8, h_v13⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
  store_step with Store.apply_mk_rep s8 v9 v13 _ _ hinv8 h64 h_v9 h_v13 as ⟨v14, s9, hinv9, h_v14⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13
  case_done hinv9 hG with h_v14 in EoCases.__eo_datatype_cons_selectors_rec.case_1 using

theorem case_2_eo__24eo_5fdatatype_5fcons_5fselectors_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) :
    case_2_eo__24eo_5fdatatype_5fcons_5fselectors_5frec s a0 a1 a2 a3 a4 a5 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__eo_datatype_cons_selectors_rec.case_2 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _) (u3 : Term) (y3 : _) (u4 : Term) (y4 : _) (u5 : Term) (y5 : _), arr.val = [u0, u1, u2, u3, u4, u5] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧ Represents.rep s' u3 y3 ∧ Represents.rep s' u4 y4 ∧ Represents.rep s' u5 y5 ∧
          EoCases.__eo_datatype_cons_selectors_rec.case_2 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 = some (__eo_datatype_cons_selectors_rec y0 y1 y2 y3 y4 y5)
      | core.result.Result.Ok none => EoCases.__eo_datatype_cons_selectors_rec.case_2 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24eo_5fdatatype_5fcons_5fselectors_5frec
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fedt_2esum.destruct h_a3 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__eo_datatype_cons_selectors_rec.case_2
  pat_destruct_lit Store.native_pattern_succ_spec s a4 h_a4 hinv h64 as ⟨v4, x_v4, h_v4⟩ storing ⟨s1, hinv1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v2 in EoCases.__eo_datatype_cons_selectors_rec.case_2
  case_again hinv1 hG with h_a0 h_a1 h_a2 h_v2 h_v4 h_a5 in EoCases.__eo_datatype_cons_selectors_rec.case_2 using

/-- logos's `__eo_datatype_cons_selectors_rec` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fdatatype_5fcons_5fselectors_5frec.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) (hw_a4 : Valid.valid x_a4) (hw_a5 : Valid.valid x_a5) :
    __eo_datatype_cons_selectors_rec x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 =
      (firstSome [EoCases.__eo_datatype_cons_selectors_rec.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5, EoCases.__eo_datatype_cons_selectors_rec.case_1 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5, EoCases.__eo_datatype_cons_selectors_rec.case_2 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5] HasStuck.stuck) := by
  conv => lhs; unfold __eo_datatype_cons_selectors_rec
  unfold EoCases.__eo_datatype_cons_selectors_rec.case_0 EoCases.__eo_datatype_cons_selectors_rec.case_1 EoCases.__eo_datatype_cons_selectors_rec.case_2
  logos_eq

theorem step_eo__24eo_5fdatatype_5fcons_5fselectors_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) :
    step_eo__24eo_5fdatatype_5fcons_5fselectors_5frec s a0 a1 a2 a3 a4 a5 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (Next.Done t) => Represents.rep s' t (__eo_datatype_cons_selectors_rec x_a0 x_a1 x_a2 x_a3 x_a4 x_a5)
      | core.result.Result.Ok (Next.Again arr) =>
        s'.budget < s.budget ∧ ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _) (u3 : Term) (y3 : _) (u4 : Term) (y4 : _) (u5 : Term) (y5 : _), arr.val = [u0, u1, u2, u3, u4, u5] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧ Represents.rep s' u3 y3 ∧ Represents.rep s' u4 y4 ∧ Represents.rep s' u5 y5 ∧
          __eo_datatype_cons_selectors_rec x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 = __eo_datatype_cons_selectors_rec y0 y1 y2 y3 y4 y5
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fdatatype_5fcons_5fselectors_5frec.rust_eq x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3) (by valid_tac hinv h_a4) (by valid_tac hinv h_a5)]
  unfold step_eo__24eo_5fdatatype_5fcons_5fselectors_5frec
  have hG := Store.Grows.refl s
  tick_step as ⟨s1, hinv1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5
  round_step with case_0_eo__24eo_5fdatatype_5fcons_5fselectors_5frec_spec n ih s1 a0 a1 a2 a3 a4 a5 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 h_a3 h_a4 h_a5
    as ⟨s2, hinv2, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 hbud using
  round_step with case_1_eo__24eo_5fdatatype_5fcons_5fselectors_5frec_spec n ih s2 a0 a1 a2 a3 a4 a5 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 hinv2 h64 (hG.rem hrem) h_a0 h_a1 h_a2 h_a3 h_a4 h_a5
    as ⟨s3, hinv3, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 hbud using hc0
  round_step with case_2_eo__24eo_5fdatatype_5fcons_5fselectors_5frec_spec n ih s3 a0 a1 a2 a3 a4 a5 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 hinv3 h64 (hG.rem hrem) h_a0 h_a1 h_a2 h_a3 h_a4 h_a5
    as ⟨s4, hinv4, hc2⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 hbud using hc0 hc1
  round_stuck hinv4 hG using hc0 hc1 hc2 in EoCases.__eo_datatype_cons_selectors_rec.case_0 EoCases.__eo_datatype_cons_selectors_rec.case_1 EoCases.__eo_datatype_cons_selectors_rec.case_2

theorem body_eo__24eo_5fdatatype_5fcons_5fselectors_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) :
    body_eo__24eo_5fdatatype_5fcons_5fselectors_5frec s a0 a1 a2 a3 a4 a5 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_datatype_cons_selectors_rec x_a0 x_a1 x_a2 x_a3 x_a4 x_a5)
      | core.result.Result.Err _ => True ⦄div := by
  refine (?_ : ∀ (k : Nat) (a0 a1 a2 a3 a4 a5 : Term) (s : Store) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _), s.budget ≤ k → s.Inv → s.remaining ≤ n →
      Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 → Represents.rep s a4 x_a4 → Represents.rep s a5 x_a5 →
      body_eo__24eo_5fdatatype_5fcons_5fselectors_5frec s a0 a1 a2 a3 a4 a5 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_datatype_cons_selectors_rec x_a0 x_a1 x_a2 x_a3 x_a4 x_a5)
      | core.result.Result.Err _ => True ⦄div) s.budget a0 a1 a2 a3 a4 a5 s x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 le_rfl hinv hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5
  intro k
  refine Nat.strong_induction_on k ?_
  intro k ihl a0 a1 a2 a3 a4 a5 s x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 hk hinv hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5
  unfold body_eo__24eo_5fdatatype_5fcons_5fselectors_5frec body_eo__24eo_5fdatatype_5fcons_5fselectors_5frec_loop
  step with step_eo__24eo_5fdatatype_5fcons_5fselectors_5frec_spec n ih s a0 a1 a2 a3 a4 a5 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 as ⟨r, s1, hinv1, hg1, hr⟩
  cases r with
  | Err e => simp only [WP.dspec_ok, WP.uncurry'_pair]; exact ⟨hinv1, hg1, trivial⟩
  | Ok nx =>
    cases nx with
    | Done value =>
      simp only [WP.dspec_ok, WP.uncurry'_pair]
      exact ⟨hinv1, hg1, hr⟩
    | Again next =>
      obtain ⟨hlt, u0, y0, u1, y1, u2, y2, u3, y3, u4, y4, u5, y5, hnext, hrep0, hrep1, hrep2, hrep3, hrep4, hrep5, heq⟩ := hr
      simp only
      have hlen : next.length = 6 := by simp [Array.length, hnext]
      step as ⟨b0, hb0⟩
      obtain rfl : b0 = u0 := by simp [hb0, hnext]
      step as ⟨b1, hb1⟩
      obtain rfl : b1 = u1 := by simp [hb1, hnext]
      step as ⟨b2, hb2⟩
      obtain rfl : b2 = u2 := by simp [hb2, hnext]
      step as ⟨b3, hb3⟩
      obtain rfl : b3 = u3 := by simp [hb3, hnext]
      step as ⟨b4, hb4⟩
      obtain rfl : b4 = u4 := by simp [hb4, hnext]
      step as ⟨b5, hb5⟩
      obtain rfl : b5 = u5 := by simp [hb5, hnext]
      have hrec := ihl s1.budget (by omega) b0 b1 b2 b3 b4 b5 s1 y0 y1 y2 y3 y4 y5 le_rfl hinv1 (hg1.rem hrem)  hrep0  hrep1  hrep2  hrep3  hrep4  hrep5
      unfold body_eo__24eo_5fdatatype_5fcons_5fselectors_5frec at hrec
      apply WP.dspec_mono hrec
      loop_close hg1 heq

theorem eo__24eo_5fdatatype_5fcons_5fselectors_5frec_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fdatatype_5fcons_5fselectors_5frec.Spec n := by
  intro s a0 a1 a2 a3 a4 a5 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5
  unfold eo__24eo_5fdatatype_5fcons_5fselectors_5frec
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 74#u32 _ [a0, a1, a2, a3, a4, a5] rfl
    (fun s1 => body_eo__24eo_5fdatatype_5fcons_5fselectors_5frec s1 a0 a1 a2 a3 a4 a5) (fun s' t => Represents.rep s' t (__eo_datatype_cons_selectors_rec x_a0 x_a1 x_a2 x_a3 x_a4 x_a5))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, b2, b3, b4, b5, y0, y1, y2, y3, y4, y5, hargs, hb0, hb1, hb2, hb3, hb4, hb5, hr⟩ := ProgramSem.of_74 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      obtain rfl := Rep.functional hb2 (Represents.congr h_a2 hn)
      obtain rfl := Rep.functional hb3 (Represents.congr h_a3 hn)
      obtain rfl := Rep.functional hb4 (Represents.congr h_a4 hn)
      obtain rfl := Rep.functional hb5 (Represents.congr h_a5 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_74 ⟨a0, a1, a2, a3, a4, a5, x_a0, x_a1, x_a2, x_a3, x_a4, x_a5, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, Rep.mono hpre h_a2, Rep.mono hpre h_a3, Rep.mono hpre h_a4, Rep.mono hpre h_a5, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fdatatype_5fcons_5fselectors_5frec_spec m (ih m hm) s1 a0 a1 a2 a3 a4 a5 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn) (by congr_one h_a4 hn) (by congr_one h_a5 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fdatatype_5fconstructors_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) :
    case_0_eo__24eo_5fdatatype_5fconstructors_5frec s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_datatype_constructors_rec.case_0 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_datatype_constructors_rec.case_0 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fdatatype_5fconstructors_5frec
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fedt_2esum.destruct h_a2 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__eo_datatype_constructors_rec.case_0
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v2
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo__24emb_5fDtCons.construct s1 e_v4 (by rw [he_v4]; rfl) h_a0 h_a1 h_a3 hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v2 h_v3
  store_step with Store.apply_rep s2 v3 v4 _ _ hinv2 h64 h_v3 h_v4 (by ns_tac) (by ns_tac) as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v2 h_v3 h_v4
  step as ⟨e_v6, he_v6⟩
  store_step with Store.native_spec_nat_succ s3 e_v6 (by rw [he_v6]; rfl) h_a3 hinv3 h64 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with ih.eo__24eo_5fdatatype_5fconstructors_5frec s4 a0 a1 v2 v6 _ _ _ _ hinv4 h64 (hG.rem hrem) h_a0 h_a1 h_v2 h_v6 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  store_step with Store.apply_mk_rep s5 v5 v7 _ _ hinv5 h64 h_v5 h_v7 as ⟨v8, s6, hinv6, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  case_done hinv6 hG with h_v8 in EoCases.__eo_datatype_constructors_rec.case_0 using

theorem case_1_eo__24eo_5fdatatype_5fconstructors_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) :
    case_1_eo__24eo_5fdatatype_5fconstructors_5frec s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_datatype_constructors_rec.case_1 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_datatype_constructors_rec.case_1 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24eo_5fdatatype_5fconstructors_5frec
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
  case_done hinv1 hG with h_v0 in EoCases.__eo_datatype_constructors_rec.case_1 using

/-- logos's `__eo_datatype_constructors_rec` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fdatatype_5fconstructors_5frec.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) :
    __eo_datatype_constructors_rec x_a0 x_a1 x_a2 x_a3 =
      (firstSome [EoCases.__eo_datatype_constructors_rec.case_0 x_a0 x_a1 x_a2 x_a3, EoCases.__eo_datatype_constructors_rec.case_1 x_a0 x_a1 x_a2 x_a3] HasStuck.stuck) := by
  conv => lhs; unfold __eo_datatype_constructors_rec
  unfold EoCases.__eo_datatype_constructors_rec.case_0 EoCases.__eo_datatype_constructors_rec.case_1
  logos_eq

theorem body_eo__24eo_5fdatatype_5fconstructors_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) :
    body_eo__24eo_5fdatatype_5fconstructors_5frec s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_datatype_constructors_rec x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fdatatype_5fconstructors_5frec.rust_eq x_a0 x_a1 x_a2 x_a3 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3)]
  unfold body_eo__24eo_5fdatatype_5fconstructors_5frec
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fdatatype_5fconstructors_5frec_spec n ih s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 using
  case_step with case_1_eo__24eo_5fdatatype_5fconstructors_5frec_spec n ih s1 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 h_a3
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 using hc0
  body_stuck hinv2 hG using hc0 hc1 in EoCases.__eo_datatype_constructors_rec.case_0 EoCases.__eo_datatype_constructors_rec.case_1

theorem eo__24eo_5fdatatype_5fconstructors_5frec_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fdatatype_5fconstructors_5frec.Spec n := by
  intro s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3
  unfold eo__24eo_5fdatatype_5fconstructors_5frec
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 75#u32 _ [a0, a1, a2, a3] rfl
    (fun s1 => body_eo__24eo_5fdatatype_5fconstructors_5frec s1 a0 a1 a2 a3) (fun s' t => Represents.rep s' t (__eo_datatype_constructors_rec x_a0 x_a1 x_a2 x_a3))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, b2, b3, y0, y1, y2, y3, hargs, hb0, hb1, hb2, hb3, hr⟩ := ProgramSem.of_75 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      obtain rfl := Rep.functional hb2 (Represents.congr h_a2 hn)
      obtain rfl := Rep.functional hb3 (Represents.congr h_a3 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_75 ⟨a0, a1, a2, a3, x_a0, x_a1, x_a2, x_a3, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, Rep.mono hpre h_a2, Rep.mono hpre h_a3, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fdatatype_5fconstructors_5frec_spec m (ih m hm) s1 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fdd_5flookup_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_0_eo__24eo_5fdd_5flookup s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_dd_lookup.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_dd_lookup.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fdd_5flookup
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fedd_2econs.destruct h_a1 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ ⟨v3, x_v3, h_v3⟩ else hinv hG in EoCases.__eo_dd_lookup.case_0
  step as ⟨e_v4, he_v4⟩
  store_step with Store.native_spec_streq s e_v4 (by rw [he_v4]; rfl) h_a0 h_v1 hinv h64 as ⟨v4, s1, hinv1, h_v4⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3
  rw [← Bridge.native_streq] at h_v4
  have h_ite_v6 := (show if_0_eo__24eo_5fdd_5flookup s1 v4 v2 a0 v3 ⦃ r s' => s'.Inv ∧ s1.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_0_eo__24eo_5fdd_5flookup
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s1
    rcases Store.boolean_value_native h_v4 with ⟨hx_5, hbv_5⟩ | ⟨hx_5, hbv_5⟩
    · ite_branch hbv_5
      ite_done hinv1 hG with (native_ite_true_rep _ hx_5 h_v2)
    · ite_branch hbv_5
      store_step with ih.eo__24eo_5fdd_5flookup s1 a0 v3 _ _ hinv1 h64 (hG.rem hrem) h_a0 h_v3 as ⟨v5, s2, hinv2, h_v5⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4
      ite_done hinv2 hG with (native_ite_false_rep _ hx_5 h_v5))
  store_step with h_ite_v6 as ⟨v6, s2, hinv2, h_v6⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4
  case_done hinv2 hG with h_v6 in EoCases.__eo_dd_lookup.case_0 using

theorem case_1_eo__24eo_5fdd_5flookup_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_1_eo__24eo_5fdd_5flookup s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_dd_lookup.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_dd_lookup.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24eo_5fdd_5flookup
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fedd_2enil.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a1 v0 with h_a1 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_dd_lookup.case_1
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24emb_5fedt_2enull.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__eo_dd_lookup.case_1 using

/-- logos's `__eo_dd_lookup` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fdd_5flookup.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_dd_lookup x_a0 x_a1 =
      (firstSome [EoCases.__eo_dd_lookup.case_0 x_a0 x_a1, EoCases.__eo_dd_lookup.case_1 x_a0 x_a1] default) := by
  conv => lhs; unfold __eo_dd_lookup
  unfold EoCases.__eo_dd_lookup.case_0 EoCases.__eo_dd_lookup.case_1
  logos_eq

theorem body_eo__24eo_5fdd_5flookup_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fdd_5flookup s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_dd_lookup x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fdd_5flookup.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fdd_5flookup
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fdd_5flookup_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using
  case_step with case_1_eo__24eo_5fdd_5flookup_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 using hc0
  body_stuck hinv2 hG using hc0 hc1 in EoCases.__eo_dd_lookup.case_0 EoCases.__eo_dd_lookup.case_1 splitting x_a0 x_a1

theorem eo__24eo_5fdd_5flookup_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fdd_5flookup.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fdd_5flookup
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 76#u32 _ [a0, a1] rfl
    (fun s1 => body_eo__24eo_5fdd_5flookup s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_dd_lookup x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, y0, y1, hargs, hb0, hb1, hr⟩ := ProgramSem.of_76 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_76 ⟨a0, a1, x_a0, x_a1, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fdd_5flookup_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fdd_5fresolve_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_0_eo__24eo_5fdd_5fresolve s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_dd_resolve.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_dd_resolve.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fdd_5fresolve
  have hG := Store.Grows.refl s
  store_step with ih.eo__24eo_5fdd_5flookup s a0 a1 _ _ hinv h64 hrem h_a0 h_a1 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  store_step with ih.eo__24eo_5fdt_5fresolve s1 v0 a1 _ _ hinv1 h64 (hG.rem hrem) h_v0 h_a1 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__eo_dd_resolve.case_0 using

/-- logos's `__eo_dd_resolve` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fdd_5fresolve.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_dd_resolve x_a0 x_a1 =
      (firstSome [EoCases.__eo_dd_resolve.case_0 x_a0 x_a1] default) := by
  conv => lhs; unfold __eo_dd_resolve
  unfold EoCases.__eo_dd_resolve.case_0
  logos_eq

theorem body_eo__24eo_5fdd_5fresolve_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fdd_5fresolve s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_dd_resolve x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fdd_5fresolve.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fdd_5fresolve
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fdd_5fresolve_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using
  body_stuck hinv1 hG using hc0 in EoCases.__eo_dd_resolve.case_0 splitting x_a0 x_a1

theorem eo__24eo_5fdd_5fresolve_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fdd_5fresolve.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fdd_5fresolve
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fdd_5fresolve s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_dd_resolve x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fdd_5fresolve_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fdisamb_5ftype_5fseq_2eempty_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fdisamb_5ftype_5fseq_2eempty s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_disamb_type_seq_empty.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_disamb_type_seq_empty.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fdisamb_5ftype_5fseq_2eempty
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_disamb_type_seq_empty.case_0
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_Seq.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_disamb_type_seq_empty.case_0
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo_Seq.construct s1 e_v4 (by rw [he_v4]; exact empty_args) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with Store.apply_rep s2 v4 v2 _ _ hinv2 h64 h_v4 h_v2 (by ns_tac) (by ns_tac) as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_disamb_type_seq_empty.case_0 using hn_a0 hn_v1 hn_v2

/-- logos's `__eo_disamb_type_seq_empty` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fdisamb_5ftype_5fseq_2eempty.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_disamb_type_seq_empty x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_disamb_type_seq_empty.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_disamb_type_seq_empty
  unfold EoCases.__eo_disamb_type_seq_empty.case_0
  logos_eq

theorem body_eo__24eo_5fdisamb_5ftype_5fseq_2eempty_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fdisamb_5ftype_5fseq_2eempty s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_disamb_type_seq_empty x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fdisamb_5ftype_5fseq_2eempty.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fdisamb_5ftype_5fseq_2eempty
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fdisamb_5ftype_5fseq_2eempty_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_disamb_type_seq_empty.case_0

theorem eo__24eo_5fdisamb_5ftype_5fseq_2eempty_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fdisamb_5ftype_5fseq_2eempty.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fdisamb_5ftype_5fseq_2eempty
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fdisamb_5ftype_5fseq_2eempty s1 a0) (fun s' t => Represents.rep s' t (__eo_disamb_type_seq_empty x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fdisamb_5ftype_5fseq_2eempty_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fdisamb_5ftype_5fset_2eempty_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fdisamb_5ftype_5fset_2eempty s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_disamb_type_set_empty.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_disamb_type_set_empty.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fdisamb_5ftype_5fset_2eempty
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_disamb_type_set_empty.case_0
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_Set.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_disamb_type_set_empty.case_0
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo_Set.construct s1 e_v4 (by rw [he_v4]; exact empty_args) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with Store.apply_rep s2 v4 v2 _ _ hinv2 h64 h_v4 h_v2 (by ns_tac) (by ns_tac) as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_disamb_type_set_empty.case_0 using hn_a0 hn_v1 hn_v2

/-- logos's `__eo_disamb_type_set_empty` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fdisamb_5ftype_5fset_2eempty.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_disamb_type_set_empty x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_disamb_type_set_empty.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_disamb_type_set_empty
  unfold EoCases.__eo_disamb_type_set_empty.case_0
  logos_eq

theorem body_eo__24eo_5fdisamb_5ftype_5fset_2eempty_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fdisamb_5ftype_5fset_2eempty s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_disamb_type_set_empty x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fdisamb_5ftype_5fset_2eempty.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fdisamb_5ftype_5fset_2eempty
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fdisamb_5ftype_5fset_2eempty_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_disamb_type_set_empty.case_0

theorem eo__24eo_5fdisamb_5ftype_5fset_2eempty_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fdisamb_5ftype_5fset_2eempty.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fdisamb_5ftype_5fset_2eempty
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fdisamb_5ftype_5fset_2eempty s1 a0) (fun s' t => Represents.rep s' t (__eo_disamb_type_set_empty x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fdisamb_5ftype_5fset_2eempty_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fdt_5fconstructors_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fdt_5fconstructors s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_dt_constructors.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_dt_constructors.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fdt_5fconstructors
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fDatatypeType.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__eo_dt_constructors.case_0
  store_step with ih.eo__24eo_5fdd_5flookup s v1 v2 _ _ hinv h64 hrem h_v1 h_v2 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with Store.native_nat_zero_spec s1 hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24eo_5fdatatype_5fconstructors_5frec s2 v1 v2 v3 v4 _ _ _ _ hinv2 h64 (hG.rem hrem) h_v1 h_v2 h_v3 h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_dt_constructors.case_0 using hn_a0

theorem case_1_eo__24eo_5fdt_5fconstructors_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_1_eo__24eo_5fdt_5fconstructors s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_dt_constructors.case_1 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_dt_constructors.case_1 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24eo_5fdt_5fconstructors
  have hG := Store.Grows.refl s
  store_step with ih.eo__24eo_5fdt_5fconstructors_5fmain s a0 _ hinv h64 hrem h_a0 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  case_done hinv1 hG with h_v0 in EoCases.__eo_dt_constructors.case_1 using hn_a0

/-- logos's `__eo_dt_constructors` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fdt_5fconstructors.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_dt_constructors x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_dt_constructors.case_0 x_a0, EoCases.__eo_dt_constructors.case_1 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_dt_constructors
  unfold EoCases.__eo_dt_constructors.case_0 EoCases.__eo_dt_constructors.case_1
  logos_eq

theorem body_eo__24eo_5fdt_5fconstructors_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fdt_5fconstructors s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_dt_constructors x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fdt_5fconstructors.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fdt_5fconstructors
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fdt_5fconstructors_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  case_step with case_1_eo__24eo_5fdt_5fconstructors_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 using hn_a0 hc0
  body_stuck hinv2 hG using hn_a0 hc0 hc1 in EoCases.__eo_dt_constructors.case_0 EoCases.__eo_dt_constructors.case_1

theorem eo__24eo_5fdt_5fconstructors_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fdt_5fconstructors.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fdt_5fconstructors
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fdt_5fconstructors s1 a0) (fun s' t => Represents.rep s' t (__eo_dt_constructors x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fdt_5fconstructors_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

/-- logos's `__eo_dt_constructors_main` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fdt_5fconstructors_5fmain.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_dt_constructors_main x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [] HasStuck.stuck) := by
  conv => lhs; unfold __eo_dt_constructors_main
  logos_eq

theorem body_eo__24eo_5fdt_5fconstructors_5fmain_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fdt_5fconstructors_5fmain s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_dt_constructors_main x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fdt_5fconstructors_5fmain.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fdt_5fconstructors_5fmain
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  body_stuck hinv hG using hn_a0 in

theorem eo__24eo_5fdt_5fconstructors_5fmain_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fdt_5fconstructors_5fmain.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fdt_5fconstructors_5fmain
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fdt_5fconstructors_5fmain s1 a0) (fun s' t => Represents.rep s' t (__eo_dt_constructors_main x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fdt_5fconstructors_5fmain_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fdt_5fresolve_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_0_eo__24eo_5fdt_5fresolve s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_dt_resolve.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_dt_resolve.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fdt_5fresolve
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fedt_2esum.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__eo_dt_resolve.case_0
  store_step with ih.eo__24eo_5fdtc_5fresolve s v1 a1 _ _ hinv h64 hrem h_v1 h_a1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2
  store_step with ih.eo__24eo_5fdt_5fresolve s1 v2 a1 _ _ hinv1 h64 (hG.rem hrem) h_v2 h_a1 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5fedt_2esum.construct s2 e_v5 (by rw [he_v5]; rfl) h_v3 h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_dt_resolve.case_0 using

theorem case_1_eo__24eo_5fdt_5fresolve_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_1_eo__24eo_5fdt_5fresolve s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_dt_resolve.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_dt_resolve.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24eo_5fdt_5fresolve
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fedt_2enull.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_dt_resolve.case_1
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24emb_5fedt_2enull.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__eo_dt_resolve.case_1 using

/-- logos's `__eo_dt_resolve` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fdt_5fresolve.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_dt_resolve x_a0 x_a1 =
      (firstSome [EoCases.__eo_dt_resolve.case_0 x_a0 x_a1, EoCases.__eo_dt_resolve.case_1 x_a0 x_a1] default) := by
  conv => lhs; unfold __eo_dt_resolve
  unfold EoCases.__eo_dt_resolve.case_0 EoCases.__eo_dt_resolve.case_1
  logos_eq

theorem body_eo__24eo_5fdt_5fresolve_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fdt_5fresolve s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_dt_resolve x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fdt_5fresolve.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fdt_5fresolve
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fdt_5fresolve_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using
  case_step with case_1_eo__24eo_5fdt_5fresolve_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 using hc0
  body_stuck hinv2 hG using hc0 hc1 in EoCases.__eo_dt_resolve.case_0 EoCases.__eo_dt_resolve.case_1 splitting x_a0 x_a1

theorem eo__24eo_5fdt_5fresolve_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fdt_5fresolve.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fdt_5fresolve
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 82#u32 _ [a0, a1] rfl
    (fun s1 => body_eo__24eo_5fdt_5fresolve s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_dt_resolve x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, y0, y1, hargs, hb0, hb1, hr⟩ := ProgramSem.of_82 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_82 ⟨a0, a1, x_a0, x_a1, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fdt_5fresolve_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fdt_5fselectors_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fdt_5fselectors s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_dt_selectors.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_dt_selectors.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fdt_5fselectors
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fDtCons.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ ⟨v3, x_v3, h_v3⟩ else hinv hG in EoCases.__eo_dt_selectors.case_0
  store_step with ih.eo__24eo_5fdd_5fresolve s v1 v2 _ _ hinv h64 hrem h_v1 h_v2 as ⟨v4, s1, hinv1, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with Store.native_nat_zero_spec s1 hinv1 h64 as ⟨v5, s2, hinv2, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  store_step with ih.eo__24eo_5fdatatype_5fcons_5fselectors_5frec s2 v1 v2 v3 v4 v3 v5 _ _ _ _ _ _ hinv2 h64 (hG.rem hrem) h_v1 h_v2 h_v3 h_v4 h_v3 h_v5 as ⟨v6, s3, hinv3, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  case_done hinv3 hG with h_v6 in EoCases.__eo_dt_selectors.case_0 using hn_a0

theorem case_1_eo__24eo_5fdt_5fselectors_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_1_eo__24eo_5fdt_5fselectors s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_dt_selectors.case_1 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_dt_selectors.case_1 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24eo_5fdt_5fselectors
  have hG := Store.Grows.refl s
  store_step with ih.eo__24eo_5fdt_5fselectors_5fmain s a0 _ hinv h64 hrem h_a0 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  case_done hinv1 hG with h_v0 in EoCases.__eo_dt_selectors.case_1 using hn_a0

/-- logos's `__eo_dt_selectors` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fdt_5fselectors.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_dt_selectors x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_dt_selectors.case_0 x_a0, EoCases.__eo_dt_selectors.case_1 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_dt_selectors
  unfold EoCases.__eo_dt_selectors.case_0 EoCases.__eo_dt_selectors.case_1
  logos_eq

theorem body_eo__24eo_5fdt_5fselectors_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fdt_5fselectors s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_dt_selectors x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fdt_5fselectors.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fdt_5fselectors
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fdt_5fselectors_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  case_step with case_1_eo__24eo_5fdt_5fselectors_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 using hn_a0 hc0
  body_stuck hinv2 hG using hn_a0 hc0 hc1 in EoCases.__eo_dt_selectors.case_0 EoCases.__eo_dt_selectors.case_1

theorem eo__24eo_5fdt_5fselectors_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fdt_5fselectors.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fdt_5fselectors
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fdt_5fselectors s1 a0) (fun s' t => Represents.rep s' t (__eo_dt_selectors x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fdt_5fselectors_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

/-- logos's `__eo_dt_selectors_main` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fdt_5fselectors_5fmain.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_dt_selectors_main x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [] HasStuck.stuck) := by
  conv => lhs; unfold __eo_dt_selectors_main
  logos_eq

theorem body_eo__24eo_5fdt_5fselectors_5fmain_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fdt_5fselectors_5fmain s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_dt_selectors_main x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fdt_5fselectors_5fmain.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fdt_5fselectors_5fmain
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  body_stuck hinv hG using hn_a0 in

theorem eo__24eo_5fdt_5fselectors_5fmain_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fdt_5fselectors_5fmain.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fdt_5fselectors_5fmain
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fdt_5fselectors_5fmain s1 a0) (fun s' t => Represents.rep s' t (__eo_dt_selectors_main x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fdt_5fselectors_5fmain_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fdtc_5fresolve_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_0_eo__24eo_5fdtc_5fresolve s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_dtc_resolve.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_dtc_resolve.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fdtc_5fresolve
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fedtc_2econs.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__eo_dtc_resolve.case_0
  pat_destruct CtorSpec.eo__24emb_5fDatatypeTypeRef.destruct h_v1 as ⟨v4, x_v4, h_v4⟩ else hinv hG in EoCases.__eo_dtc_resolve.case_0
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5fDatatypeType.construct s e_v5 (by rw [he_v5]; rfl) h_v4 h_a1 hinv h64 as ⟨v5, s1, hinv1, h_v5⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4
  store_step with ih.eo__24eo_5fdtc_5fresolve s1 v2 a1 _ _ hinv1 h64 (hG.rem hrem) h_v2 h_a1 as ⟨v6, s2, hinv2, h_v6⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo__24emb_5fedtc_2econs.construct s2 e_v7 (by rw [he_v7]; rfl) h_v5 h_v6 hinv2 h64 as ⟨v7, s3, hinv3, h_v7⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6
  case_done hinv3 hG with h_v7 in EoCases.__eo_dtc_resolve.case_0 using

theorem case_1_eo__24eo_5fdtc_5fresolve_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_1_eo__24eo_5fdtc_5fresolve s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_dtc_resolve.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_dtc_resolve.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24eo_5fdtc_5fresolve
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fedtc_2econs.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__eo_dtc_resolve.case_1
  store_step with ih.eo__24eo_5fdtc_5fresolve s v2 a1 _ _ hinv h64 hrem h_v2 h_a1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo__24emb_5fedtc_2econs.construct s1 e_v4 (by rw [he_v4]; rfl) h_v1 h_v3 hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3
  case_done hinv2 hG with h_v4 in EoCases.__eo_dtc_resolve.case_1 using

theorem case_2_eo__24eo_5fdtc_5fresolve_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_2_eo__24eo_5fdtc_5fresolve s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_dtc_resolve.case_2 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_dtc_resolve.case_2 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24eo_5fdtc_5fresolve
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fedtc_2eunit.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_dtc_resolve.case_2
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24emb_5fedtc_2eunit.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__eo_dtc_resolve.case_2 using

/-- logos's `__eo_dtc_resolve` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fdtc_5fresolve.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_dtc_resolve x_a0 x_a1 =
      (firstSome [EoCases.__eo_dtc_resolve.case_0 x_a0 x_a1, EoCases.__eo_dtc_resolve.case_1 x_a0 x_a1, EoCases.__eo_dtc_resolve.case_2 x_a0 x_a1] default) := by
  conv => lhs; unfold __eo_dtc_resolve
  unfold EoCases.__eo_dtc_resolve.case_0 EoCases.__eo_dtc_resolve.case_1 EoCases.__eo_dtc_resolve.case_2
  logos_eq

theorem body_eo__24eo_5fdtc_5fresolve_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fdtc_5fresolve s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_dtc_resolve x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fdtc_5fresolve.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fdtc_5fresolve
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fdtc_5fresolve_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using
  case_step with case_1_eo__24eo_5fdtc_5fresolve_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 using hc0
  case_step with case_2_eo__24eo_5fdtc_5fresolve_spec n ih s2 a0 a1 x_a0 x_a1 hinv2 h64 (hG.rem hrem) h_a0 h_a1
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0 h_a1 using hc0 hc1
  body_stuck hinv3 hG using hc0 hc1 hc2 in EoCases.__eo_dtc_resolve.case_0 EoCases.__eo_dtc_resolve.case_1 EoCases.__eo_dtc_resolve.case_2 splitting x_a0 x_a1

theorem eo__24eo_5fdtc_5fresolve_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fdtc_5fresolve.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fdtc_5fresolve
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 85#u32 _ [a0, a1] rfl
    (fun s1 => body_eo__24eo_5fdtc_5fresolve s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_dtc_resolve x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, y0, y1, hargs, hb0, hb1, hr⟩ := ProgramSem.of_85 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_85 ⟨a0, a1, x_a0, x_a1, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fdtc_5fresolve_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

end pathos_compiled_checker
