module
public import $PROOFS$.Head
public import $PROOFS$.Part34
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
  store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying dropping he_v0 e_v0
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
