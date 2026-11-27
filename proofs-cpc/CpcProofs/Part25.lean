module
public import CpcProofs.Head
public import CpcProofs.Part24
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
  store_step with ih.eo__24eo_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v2 dropping h_a0 h_v1 v1
  store_step with ih.eo__24eo_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v2 h_v3 dropping hinv1 s1
  store_step with ih.eo__24eo_5ftypeof_5f_40const s2 v3 v4 v2 _ _ _ hinv2 h64 (hG.rem hrem) h_v3 h_v4 h_v2 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying dropping h_v2 h_v3 h_v4 hinv2 s2 v2 v3 v4
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
  store_step with ih.eo__24eo_5ftypeof s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v2 dropping h_a0 h_v1 v1
  store_step with ih.eo__24eo_5ftypeof s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v3 dropping h_v2 hinv1 s1 v2
  store_step with ih.eo__24eo_5ftypeof_5fapply s2 v3 v4 _ _ hinv2 h64 (hG.rem hrem) h_v3 h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying dropping h_v3 h_v4 hinv2 s2 v3 v4
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

end pathos_compiled_checker
