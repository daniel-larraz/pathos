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

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
set_option maxRecDepth 8000

@[expose] public section

namespace pathos_compiled_checker

open Aeneas Aeneas.Std Result
open Eo hiding Term
open Smtm
open generated generated.part0 generated.part1 generated.part2 generated.part3 generated.part4 generated.part5 generated.part6 generated.part7 generated.part8 generated.part9 generated.part10 generated.part11 generated.part12

theorem case_0_eo__24smtx_5ftypeof_5fdt_5fcons_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    case_0_eo__24smtx_5ftypeof_5fdt_5fcons_5frec s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof_dt_cons_rec.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _), arr.val = [u0, u1, u2] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧
          EoCases.__smtx_typeof_dt_cons_rec.case_0 x_a0 x_a1 x_a2 = some (__smtx_typeof_dt_cons_rec y0 y1 y2)
      | core.result.Result.Ok none => EoCases.__smtx_typeof_dt_cons_rec.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24smtx_5ftypeof_5fdt_5fcons_5frec
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fdt_2esum.destruct h_a1 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof_dt_cons_rec.case_0
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__24emb_5fdtc_2eunit.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__smtx_typeof_dt_cons_rec.case_0
  pat_native_zero Store.native_pattern_nat_zero_spec s1 a2 h_a2 hinv1 h64 storing ⟨s2, hinv2⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v3 in EoCases.__smtx_typeof_dt_cons_rec.case_0
  case_done hinv2 hG with h_a0 in EoCases.__smtx_typeof_dt_cons_rec.case_0 using

theorem case_1_eo__24smtx_5ftypeof_5fdt_5fcons_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    case_1_eo__24smtx_5ftypeof_5fdt_5fcons_5frec s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof_dt_cons_rec.case_1 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _), arr.val = [u0, u1, u2] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧
          EoCases.__smtx_typeof_dt_cons_rec.case_1 x_a0 x_a1 x_a2 = some (__smtx_typeof_dt_cons_rec y0 y1 y2)
      | core.result.Result.Ok none => EoCases.__smtx_typeof_dt_cons_rec.case_1 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24smtx_5ftypeof_5fdt_5fcons_5frec
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fdt_2esum.destruct h_a1 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof_dt_cons_rec.case_1
  pat_destruct CtorSpec.eo__24emb_5fdtc_2econs.destruct h_v1 as ⟨v4, x_v4, h_v4⟩ ⟨v5, x_v5, h_v5⟩ else hinv hG in EoCases.__smtx_typeof_dt_cons_rec.case_1
  pat_native_zero Store.native_pattern_nat_zero_spec s a2 h_a2 hinv h64 storing ⟨s1, hinv1⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 in EoCases.__smtx_typeof_dt_cons_rec.case_1
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo__24emb_5fdt_2esum.construct s1 e_v7 (by rw [he_v7]; rfl) h_v5 h_v2 hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5
  store_step with Store.native_nat_zero_spec s2 hinv2 h64 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7
  store_step with ih.eo__24smtx_5ftypeof_5fdt_5fcons_5frec s3 a0 v7 v8 _ _ _ hinv3 h64 (hG.rem hrem) h_a0 h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eDtcAppType.construct s4 e_v10 (by rw [he_v10]; rfl) h_v4 h_v9 hinv4 h64 as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9
  case_done hinv5 hG with h_v10 in EoCases.__smtx_typeof_dt_cons_rec.case_1 using

theorem case_2_eo__24smtx_5ftypeof_5fdt_5fcons_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    case_2_eo__24smtx_5ftypeof_5fdt_5fcons_5frec s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof_dt_cons_rec.case_2 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _), arr.val = [u0, u1, u2] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧
          EoCases.__smtx_typeof_dt_cons_rec.case_2 x_a0 x_a1 x_a2 = some (__smtx_typeof_dt_cons_rec y0 y1 y2)
      | core.result.Result.Ok none => EoCases.__smtx_typeof_dt_cons_rec.case_2 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24smtx_5ftypeof_5fdt_5fcons_5frec
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fdt_2esum.destruct h_a1 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof_dt_cons_rec.case_2
  pat_destruct_lit Store.native_pattern_succ_spec s a2 h_a2 hinv h64 as ⟨v4, x_v4, h_v4⟩ storing ⟨s1, hinv1⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 in EoCases.__smtx_typeof_dt_cons_rec.case_2
  case_again hinv1 hG with h_a0 h_v2 h_v4 in EoCases.__smtx_typeof_dt_cons_rec.case_2 using

theorem case_3_eo__24smtx_5ftypeof_5fdt_5fcons_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    case_3_eo__24smtx_5ftypeof_5fdt_5fcons_5frec s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_typeof_dt_cons_rec.case_3 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _), arr.val = [u0, u1, u2] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧
          EoCases.__smtx_typeof_dt_cons_rec.case_3 x_a0 x_a1 x_a2 = some (__smtx_typeof_dt_cons_rec y0 y1 y2)
      | core.result.Result.Ok none => EoCases.__smtx_typeof_dt_cons_rec.case_3 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_3_eo__24smtx_5ftypeof_5fdt_5fcons_5frec
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2
  case_done hinv1 hG with h_v0 in EoCases.__smtx_typeof_dt_cons_rec.case_3 using

/-- logos's `__smtx_typeof_dt_cons_rec` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24smtx_5ftypeof_5fdt_5fcons_5frec.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __smtx_typeof_dt_cons_rec x_a0 x_a1 x_a2 =
      (firstSome [EoCases.__smtx_typeof_dt_cons_rec.case_0 x_a0 x_a1 x_a2, EoCases.__smtx_typeof_dt_cons_rec.case_1 x_a0 x_a1 x_a2, EoCases.__smtx_typeof_dt_cons_rec.case_2 x_a0 x_a1 x_a2, EoCases.__smtx_typeof_dt_cons_rec.case_3 x_a0 x_a1 x_a2] default) := by
  conv => lhs; unfold __smtx_typeof_dt_cons_rec
  unfold EoCases.__smtx_typeof_dt_cons_rec.case_0 EoCases.__smtx_typeof_dt_cons_rec.case_1 EoCases.__smtx_typeof_dt_cons_rec.case_2 EoCases.__smtx_typeof_dt_cons_rec.case_3
  logos_eq

theorem step_eo__24smtx_5ftypeof_5fdt_5fcons_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    step_eo__24smtx_5ftypeof_5fdt_5fcons_5frec s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (Next.Done t) => Represents.rep s' t (__smtx_typeof_dt_cons_rec x_a0 x_a1 x_a2)
      | core.result.Result.Ok (Next.Again arr) =>
        s'.budget < s.budget ∧ ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _), arr.val = [u0, u1, u2] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧
          __smtx_typeof_dt_cons_rec x_a0 x_a1 x_a2 = __smtx_typeof_dt_cons_rec y0 y1 y2
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24smtx_5ftypeof_5fdt_5fcons_5frec.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold step_eo__24smtx_5ftypeof_5fdt_5fcons_5frec
  have hG := Store.Grows.refl s
  tick_step as ⟨s1, hinv1⟩ growing hG carrying h_a0 h_a1 h_a2
  round_step with case_0_eo__24smtx_5ftypeof_5fdt_5fcons_5frec_spec n ih s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2
    as ⟨s2, hinv2, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 hbud using
  round_step with case_1_eo__24smtx_5ftypeof_5fdt_5fcons_5frec_spec n ih s2 a0 a1 a2 x_a0 x_a1 x_a2 hinv2 h64 (hG.rem hrem) h_a0 h_a1 h_a2
    as ⟨s3, hinv3, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 hbud using hc0
  round_step with case_2_eo__24smtx_5ftypeof_5fdt_5fcons_5frec_spec n ih s3 a0 a1 a2 x_a0 x_a1 x_a2 hinv3 h64 (hG.rem hrem) h_a0 h_a1 h_a2
    as ⟨s4, hinv4, hc2⟩ growing hG carrying h_a0 h_a1 h_a2 hbud using hc0 hc1
  round_step with case_3_eo__24smtx_5ftypeof_5fdt_5fcons_5frec_spec n ih s4 a0 a1 a2 x_a0 x_a1 x_a2 hinv4 h64 (hG.rem hrem) h_a0 h_a1 h_a2
    as ⟨s5, hinv5, hc3⟩ growing hG carrying h_a0 h_a1 h_a2 hbud using hc0 hc1 hc2
  round_stuck hinv5 hG using hc0 hc1 hc2 hc3 in EoCases.__smtx_typeof_dt_cons_rec.case_0 EoCases.__smtx_typeof_dt_cons_rec.case_1 EoCases.__smtx_typeof_dt_cons_rec.case_2 EoCases.__smtx_typeof_dt_cons_rec.case_3 splitting x_a0 x_a1 x_a2

theorem body_eo__24smtx_5ftypeof_5fdt_5fcons_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24smtx_5ftypeof_5fdt_5fcons_5frec s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_typeof_dt_cons_rec x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  refine (?_ : ∀ (k : Nat) (a0 a1 a2 : Term) (s : Store) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.budget ≤ k → s.Inv → s.remaining ≤ n →
      Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
      body_eo__24smtx_5ftypeof_5fdt_5fcons_5frec s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_typeof_dt_cons_rec x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div) s.budget a0 a1 a2 s x_a0 x_a1 x_a2 le_rfl hinv hrem h_a0 h_a1 h_a2
  intro k
  refine Nat.strong_induction_on k ?_
  intro k ihl a0 a1 a2 s x_a0 x_a1 x_a2 hk hinv hrem h_a0 h_a1 h_a2
  unfold body_eo__24smtx_5ftypeof_5fdt_5fcons_5frec body_eo__24smtx_5ftypeof_5fdt_5fcons_5frec_loop
  step with step_eo__24smtx_5ftypeof_5fdt_5fcons_5frec_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 as ⟨r, s1, hinv1, hg1, hr⟩
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
      unfold body_eo__24smtx_5ftypeof_5fdt_5fcons_5frec at hrec
      apply WP.dspec_mono hrec
      loop_close hg1 heq

theorem eo__24smtx_5ftypeof_5fdt_5fcons_5frec_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24smtx_5ftypeof_5fdt_5fcons_5frec.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24smtx_5ftypeof_5fdt_5fcons_5frec
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 1016#u32 _ [a0, a1, a2] rfl
    (fun s1 => body_eo__24smtx_5ftypeof_5fdt_5fcons_5frec s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__smtx_typeof_dt_cons_rec x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, b2, y0, y1, y2, hargs, hb0, hb1, hb2, hr⟩ := ProgramSem.of_1016 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      obtain rfl := Rep.functional hb2 (Represents.congr h_a2 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_1016 ⟨a0, a1, a2, x_a0, x_a1, x_a2, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, Rep.mono hpre h_a2, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24smtx_5ftypeof_5fdt_5fcons_5frec_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
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
  have h_ite_v8 := (show if_0_eo__24smtx_5ftypeof_5fint_5fto_5fbv s3 v4 v1 ⦃ r s' => s'.Inv ∧ s3.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_0_eo__24smtx_5ftypeof_5fint_5fto_5fbv
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s3
    rcases Store.boolean_value_native h_v4 with ⟨hx_5, hbv_5⟩ | ⟨hx_5, hbv_5⟩
    · ite_branch hbv_5
      step as ⟨e_v5, he_v5⟩
      store_step with Store.native_spec_int_to_nat s3 e_v5 (by rw [he_v5]; rfl) h_v1 hinv3 h64 as ⟨v5, s4, hinv4, h_v5⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4
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
  have h_ite_v13 := (show if_1_eo__24smtx_5ftypeof_5fre_2eloop s3 v6 v3 ⦃ r s' => s'.Inv ∧ s3.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_1_eo__24smtx_5ftypeof_5fre_2eloop
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s3
    rcases Store.boolean_value_native h_v6 with ⟨hx_7, hbv_7⟩ | ⟨hx_7, hbv_7⟩
    · ite_branch hbv_7
      simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
      store_step with Store.raw_int_u32_spec s3 0#u32 (0) (by scalar_tac) hinv3 h64 as ⟨v7, s4, hinv4, h_v7⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v5 h_v6
      step as ⟨e_v8, he_v8⟩
      store_step with Store.native_spec_zleq s4 e_v8 (by rw [he_v8]; rfl) h_v7 h_v3 hinv4 h64 as ⟨v8, s5, hinv5, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v5 h_v6 h_v7
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

theorem case_0_eo__24str_5fmembership_5fre_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24str_5fmembership_5fre s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__str_membership_re.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__str_membership_re.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24str_5fmembership_5fre
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__str_membership_re.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__str_membership_re.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_str_2ein_5fre.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__str_membership_re.case_0
  case_done hinv1 hG with h_v2 in EoCases.__str_membership_re.case_0 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

/-- logos's `__str_membership_re` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24str_5fmembership_5fre.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __str_membership_re x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__str_membership_re.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __str_membership_re
  unfold EoCases.__str_membership_re.case_0
  logos_eq

theorem body_eo__24str_5fmembership_5fre_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24str_5fmembership_5fre s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__str_membership_re x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24str_5fmembership_5fre.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24str_5fmembership_5fre
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24str_5fmembership_5fre_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__str_membership_re.case_0

theorem eo__24str_5fmembership_5fre_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24str_5fmembership_5fre.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24str_5fmembership_5fre
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24str_5fmembership_5fre s1 a0) (fun s' t => Represents.rep s' t (__str_membership_re x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24str_5fmembership_5fre_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24str_5fmembership_5fstr_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24str_5fmembership_5fstr s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__str_membership_str.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__str_membership_str.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24str_5fmembership_5fstr
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__str_membership_str.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__str_membership_str.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_str_2ein_5fre.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__str_membership_str.case_0
  case_done hinv1 hG with h_v5 in EoCases.__str_membership_str.case_0 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

/-- logos's `__str_membership_str` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24str_5fmembership_5fstr.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __str_membership_str x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__str_membership_str.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __str_membership_str
  unfold EoCases.__str_membership_str.case_0
  logos_eq

theorem body_eo__24str_5fmembership_5fstr_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24str_5fmembership_5fstr s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__str_membership_str x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24str_5fmembership_5fstr.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24str_5fmembership_5fstr
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24str_5fmembership_5fstr_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__str_membership_str.case_0

theorem eo__24str_5fmembership_5fstr_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24str_5fmembership_5fstr.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24str_5fmembership_5fstr
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24str_5fmembership_5fstr s1 a0) (fun s' t => Represents.rep s' t (__str_membership_str x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24str_5fmembership_5fstr_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24str_5fstrip_5fprefix_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24str_5fstrip_5fprefix s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__str_strip_prefix.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _), arr.val = [u0, u1] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧
          EoCases.__str_strip_prefix.case_0 x_a0 x_a1 = some (__str_strip_prefix y0 y1)
      | core.result.Result.Ok none => EoCases.__str_strip_prefix.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24str_5fstrip_5fprefix
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__str_strip_prefix.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__str_strip_prefix.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__str_strip_prefix.case_0
  pat_unapply h_a1 as ⟨v8, v9, x_v8, x_v9, h_v8, h_v9, hn_v8, hn_v9⟩ using hinv1 else hinv1 hG in EoCases.__str_strip_prefix.case_0
  pat_unapply h_v8 as ⟨v11, v12, x_v11, x_v12, h_v11, h_v12, hn_v11, hn_v12⟩ using hinv1 else hinv1 hG in EoCases.__str_strip_prefix.case_0
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s1 e_v13 (by rw [he_v13]; exact empty_args) hinv1 h64 as ⟨v13, s2, hinv2, h_v13⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12
  pat_same v11 v13 with h_v11 h_v13 using hinv2 else hinv2 hG in EoCases.__str_strip_prefix.case_0
  pat_same v12 v5 with h_v12 h_v5 using hinv2 else hinv2 hG in EoCases.__str_strip_prefix.case_0
  case_again hinv2 hG with h_v2 h_v9 in EoCases.__str_strip_prefix.case_0 using hn_a0 hn_a1 hn_v1 hn_v2 hn_v4 hn_v5 hn_v8 hn_v9 hn_v11 hn_v12

theorem case_1_eo__24str_5fstrip_5fprefix_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_1_eo__24str_5fstrip_5fprefix s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__str_strip_prefix.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _), arr.val = [u0, u1] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧
          EoCases.__str_strip_prefix.case_1 x_a0 x_a1 = some (__str_strip_prefix y0 y1)
      | core.result.Result.Ok none => EoCases.__str_strip_prefix.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24str_5fstrip_5fprefix
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__40_40pair.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  store_step with Store.apply_rep s1 v0 a0 _ _ hinv1 h64 h_v0 h_a0 (by ns_tac) (by ns_tac) as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  store_step with Store.apply_rep s2 v1 a1 _ _ hinv2 h64 h_v1 h_a1 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1
  case_done hinv3 hG with h_v2 in EoCases.__str_strip_prefix.case_1 using hn_a0 hn_a1

/-- logos's `__str_strip_prefix` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24str_5fstrip_5fprefix.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __str_strip_prefix x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__str_strip_prefix.case_0 x_a0 x_a1, EoCases.__str_strip_prefix.case_1 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __str_strip_prefix
  unfold EoCases.__str_strip_prefix.case_0 EoCases.__str_strip_prefix.case_1
  try unfold Eo.__eo_l_1___str_strip_prefix
  logos_eq_deep

theorem step_eo__24str_5fstrip_5fprefix_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    step_eo__24str_5fstrip_5fprefix s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (Next.Done t) => Represents.rep s' t (__str_strip_prefix x_a0 x_a1)
      | core.result.Result.Ok (Next.Again arr) =>
        s'.budget < s.budget ∧ ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _), arr.val = [u0, u1] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧
          __str_strip_prefix x_a0 x_a1 = __str_strip_prefix y0 y1
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24str_5fstrip_5fprefix.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold step_eo__24str_5fstrip_5fprefix
  have hG := Store.Grows.refl s
  tick_step as ⟨s1, hinv1⟩ growing hG carrying h_a0 h_a1
  stuck_check h_a0 : x_a0 as hn_a0 else hinv1 hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv1 hG
  round_step with case_0_eo__24str_5fstrip_5fprefix_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s2, hinv2, hc0⟩ growing hG carrying h_a0 h_a1 hbud using hn_a0 hn_a1
  round_step with case_1_eo__24str_5fstrip_5fprefix_spec n ih s2 a0 a1 x_a0 x_a1 hinv2 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s3, hinv3, hc1⟩ growing hG carrying h_a0 h_a1 hbud using hn_a0 hn_a1 hc0
  round_stuck hinv3 hG using hn_a0 hn_a1 hc0 hc1 in EoCases.__str_strip_prefix.case_0 EoCases.__str_strip_prefix.case_1

theorem body_eo__24str_5fstrip_5fprefix_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24str_5fstrip_5fprefix s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__str_strip_prefix x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  refine (?_ : ∀ (k : Nat) (a0 a1 : Term) (s : Store) (x_a0 : _) (x_a1 : _), s.budget ≤ k → s.Inv → s.remaining ≤ n →
      Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
      body_eo__24str_5fstrip_5fprefix s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__str_strip_prefix x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div) s.budget a0 a1 s x_a0 x_a1 le_rfl hinv hrem h_a0 h_a1
  intro k
  refine Nat.strong_induction_on k ?_
  intro k ihl a0 a1 s x_a0 x_a1 hk hinv hrem h_a0 h_a1
  unfold body_eo__24str_5fstrip_5fprefix body_eo__24str_5fstrip_5fprefix_loop
  step with step_eo__24str_5fstrip_5fprefix_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 as ⟨r, s1, hinv1, hg1, hr⟩
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
      unfold body_eo__24str_5fstrip_5fprefix at hrec
      apply WP.dspec_mono hrec
      loop_close hg1 heq

theorem eo__24str_5fstrip_5fprefix_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24str_5fstrip_5fprefix.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24str_5fstrip_5fprefix
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 1090#u32 _ [a0, a1] rfl
    (fun s1 => body_eo__24str_5fstrip_5fprefix s1 a0 a1) (fun s' t => Represents.rep s' t (__str_strip_prefix x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, y0, y1, hargs, hb0, hb1, hr⟩ := ProgramSem.of_1090 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_1090 ⟨a0, a1, x_a0, x_a1, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24str_5fstrip_5fprefix_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24strip_5feven_5fexponent_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24strip_5feven_5fexponent s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__strip_even_exponent.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _), arr.val = [u0, u1] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧
          EoCases.__strip_even_exponent.case_0 x_a0 x_a1 = some (__strip_even_exponent y0 y1)
      | core.result.Result.Ok none => EoCases.__strip_even_exponent.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24strip_5feven_5fexponent
  have hG := Store.Grows.refl s
  pat_unapply h_a1 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__strip_even_exponent.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__strip_even_exponent.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__2a.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__strip_even_exponent.case_0
  pat_same v5 a0 with h_v5 h_a0 using hinv1 else hinv1 hG in EoCases.__strip_even_exponent.case_0
  pat_unapply h_v2 as ⟨v8, v9, x_v8, x_v9, h_v8, h_v9, hn_v8, hn_v9⟩ using hinv1 else hinv1 hG in EoCases.__strip_even_exponent.case_0
  pat_unapply h_v8 as ⟨v11, v12, x_v11, x_v12, h_v11, h_v12, hn_v11, hn_v12⟩ using hinv1 else hinv1 hG in EoCases.__strip_even_exponent.case_0
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo__2a.construct s1 e_v13 (by rw [he_v13]; exact empty_args) hinv1 h64 as ⟨v13, s2, hinv2, h_v13⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12
  pat_same v11 v13 with h_v11 h_v13 using hinv2 else hinv2 hG in EoCases.__strip_even_exponent.case_0
  pat_same v12 a0 with h_v12 h_a0 using hinv2 else hinv2 hG in EoCases.__strip_even_exponent.case_0
  case_again hinv2 hG with h_a0 h_v9 in EoCases.__strip_even_exponent.case_0 using hn_a0 hn_a1 hn_v1 hn_v2 hn_v4 hn_v5 hn_v8 hn_v9 hn_v11 hn_v12

theorem case_1_eo__24strip_5feven_5fexponent_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_1_eo__24strip_5feven_5fexponent s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__strip_even_exponent.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _), arr.val = [u0, u1] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧
          EoCases.__strip_even_exponent.case_1 x_a0 x_a1 = some (__strip_even_exponent y0 y1)
      | core.result.Result.Ok none => EoCases.__strip_even_exponent.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24strip_5feven_5fexponent
  have hG := Store.Grows.refl s
  case_done hinv hG with h_a1 in EoCases.__strip_even_exponent.case_1 using hn_a0 hn_a1

/-- logos's `__strip_even_exponent` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24strip_5feven_5fexponent.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __strip_even_exponent x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__strip_even_exponent.case_0 x_a0 x_a1, EoCases.__strip_even_exponent.case_1 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __strip_even_exponent
  unfold EoCases.__strip_even_exponent.case_0 EoCases.__strip_even_exponent.case_1
  try unfold Eo.__eo_l_1___strip_even_exponent
  logos_eq_deep

theorem step_eo__24strip_5feven_5fexponent_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    step_eo__24strip_5feven_5fexponent s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (Next.Done t) => Represents.rep s' t (__strip_even_exponent x_a0 x_a1)
      | core.result.Result.Ok (Next.Again arr) =>
        s'.budget < s.budget ∧ ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _), arr.val = [u0, u1] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧
          __strip_even_exponent x_a0 x_a1 = __strip_even_exponent y0 y1
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24strip_5feven_5fexponent.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold step_eo__24strip_5feven_5fexponent
  have hG := Store.Grows.refl s
  tick_step as ⟨s1, hinv1⟩ growing hG carrying h_a0 h_a1
  stuck_check h_a0 : x_a0 as hn_a0 else hinv1 hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv1 hG
  round_step with case_0_eo__24strip_5feven_5fexponent_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s2, hinv2, hc0⟩ growing hG carrying h_a0 h_a1 hbud using hn_a0 hn_a1
  round_step with case_1_eo__24strip_5feven_5fexponent_spec n ih s2 a0 a1 x_a0 x_a1 hinv2 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s3, hinv3, hc1⟩ growing hG carrying h_a0 h_a1 hbud using hn_a0 hn_a1 hc0
  round_stuck hinv3 hG using hn_a0 hn_a1 hc0 hc1 in EoCases.__strip_even_exponent.case_0 EoCases.__strip_even_exponent.case_1

theorem body_eo__24strip_5feven_5fexponent_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24strip_5feven_5fexponent s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__strip_even_exponent x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  refine (?_ : ∀ (k : Nat) (a0 a1 : Term) (s : Store) (x_a0 : _) (x_a1 : _), s.budget ≤ k → s.Inv → s.remaining ≤ n →
      Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
      body_eo__24strip_5feven_5fexponent s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__strip_even_exponent x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div) s.budget a0 a1 s x_a0 x_a1 le_rfl hinv hrem h_a0 h_a1
  intro k
  refine Nat.strong_induction_on k ?_
  intro k ihl a0 a1 s x_a0 x_a1 hk hinv hrem h_a0 h_a1
  unfold body_eo__24strip_5feven_5fexponent body_eo__24strip_5feven_5fexponent_loop
  step with step_eo__24strip_5feven_5fexponent_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 as ⟨r, s1, hinv1, hg1, hr⟩
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
      unfold body_eo__24strip_5feven_5fexponent at hrec
      apply WP.dspec_mono hrec
      loop_close hg1 heq

theorem eo__24strip_5feven_5fexponent_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24strip_5feven_5fexponent.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24strip_5feven_5fexponent
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 1094#u32 _ [a0, a1] rfl
    (fun s1 => body_eo__24strip_5feven_5fexponent s1 a0 a1) (fun s' t => Represents.rep s' t (__strip_even_exponent x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, y0, y1, hargs, hb0, hb1, hr⟩ := ProgramSem.of_1094 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_1094 ⟨a0, a1, x_a0, x_a1, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24strip_5feven_5fexponent_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24to_5fclause_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24to_5fclause s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__to_clause.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__to_clause.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24to_5fclause
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__to_clause.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__to_clause.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_or.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__to_clause.case_0
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo_or.construct s1 e_v7 (by rw [he_v7]; exact empty_args) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with Store.apply_rep s2 v7 v5 _ _ hinv2 h64 h_v7 h_v5 (by ns_tac) (by ns_tac) as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with Store.apply_rep s3 v8 v2 _ _ hinv3 h64 h_v8 h_v2 (by ns_tac) (by ns_tac) as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__to_clause.case_0 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_1_eo__24to_5fclause_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_1_eo__24to_5fclause s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__to_clause.case_1 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__to_clause.case_1 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24to_5fclause
  have hG := Store.Grows.refl s
  store_step with Store.literal_boolean_spec s false hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__to_clause.case_1
  store_step with Store.literal_boolean_spec s1 false hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__to_clause.case_1 using hn_a0

theorem case_2_eo__24to_5fclause_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_2_eo__24to_5fclause s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__to_clause.case_2 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__to_clause.case_2 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24to_5fclause
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_or.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  store_step with Store.apply_rep s1 v0 a0 _ _ hinv1 h64 h_v0 h_a0 (by ns_tac) (by ns_tac) as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  store_step with Store.literal_boolean_spec s2 false hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_v0 h_v1
  store_step with Store.apply_rep s3 v1 v2 _ _ hinv3 h64 h_v1 h_v2 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2
  case_done hinv4 hG with h_v3 in EoCases.__to_clause.case_2 using hn_a0

/-- logos's `__to_clause` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24to_5fclause.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __to_clause x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__to_clause.case_0 x_a0, EoCases.__to_clause.case_1 x_a0, EoCases.__to_clause.case_2 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __to_clause
  unfold EoCases.__to_clause.case_0 EoCases.__to_clause.case_1 EoCases.__to_clause.case_2
  logos_eq

theorem body_eo__24to_5fclause_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24to_5fclause s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__to_clause x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24to_5fclause.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24to_5fclause
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24to_5fclause_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  case_step with case_1_eo__24to_5fclause_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 using hn_a0 hc0
  case_step with case_2_eo__24to_5fclause_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0 using hn_a0 hc0 hc1
  body_stuck hinv3 hG using hn_a0 hc0 hc1 hc2 in EoCases.__to_clause.case_0 EoCases.__to_clause.case_1 EoCases.__to_clause.case_2

theorem eo__24to_5fclause_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24to_5fclause.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24to_5fclause
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24to_5fclause s1 a0) (fun s' t => Represents.rep s' t (__to_clause x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24to_5fclause_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24to_5fcube_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24to_5fcube s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__to_cube.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__to_cube.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24to_5fcube
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__to_cube.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__to_cube.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_and.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__to_cube.case_0
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo_and.construct s1 e_v7 (by rw [he_v7]; exact empty_args) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with Store.apply_rep s2 v7 v5 _ _ hinv2 h64 h_v7 h_v5 (by ns_tac) (by ns_tac) as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with Store.apply_rep s3 v8 v2 _ _ hinv3 h64 h_v8 h_v2 (by ns_tac) (by ns_tac) as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__to_cube.case_0 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_1_eo__24to_5fcube_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_1_eo__24to_5fcube s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__to_cube.case_1 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__to_cube.case_1 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24to_5fcube
  have hG := Store.Grows.refl s
  store_step with Store.literal_boolean_spec s true hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__to_cube.case_1
  store_step with Store.literal_boolean_spec s1 true hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__to_cube.case_1 using hn_a0

theorem case_2_eo__24to_5fcube_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_2_eo__24to_5fcube s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__to_cube.case_2 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__to_cube.case_2 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24to_5fcube
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_and.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  store_step with Store.apply_rep s1 v0 a0 _ _ hinv1 h64 h_v0 h_a0 (by ns_tac) (by ns_tac) as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  store_step with Store.literal_boolean_spec s2 true hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_v0 h_v1
  store_step with Store.apply_rep s3 v1 v2 _ _ hinv3 h64 h_v1 h_v2 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2
  case_done hinv4 hG with h_v3 in EoCases.__to_cube.case_2 using hn_a0

/-- logos's `__to_cube` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24to_5fcube.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __to_cube x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__to_cube.case_0 x_a0, EoCases.__to_cube.case_1 x_a0, EoCases.__to_cube.case_2 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __to_cube
  unfold EoCases.__to_cube.case_0 EoCases.__to_cube.case_1 EoCases.__to_cube.case_2
  logos_eq

theorem body_eo__24to_5fcube_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24to_5fcube s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__to_cube x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24to_5fcube.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24to_5fcube
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24to_5fcube_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  case_step with case_1_eo__24to_5fcube_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 using hn_a0 hc0
  case_step with case_2_eo__24to_5fcube_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0 using hn_a0 hc0 hc1
  body_stuck hinv3 hG using hn_a0 hc0 hc1 hc2 in EoCases.__to_cube.case_0 EoCases.__to_cube.case_1 EoCases.__to_cube.case_2

theorem eo__24to_5fcube_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24to_5fcube.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24to_5fcube
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24to_5fcube s1 a0) (fun s' t => Represents.rep s' t (__to_cube x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24to_5fcube_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24tuple_5farg_5flist_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24tuple_5farg_5flist s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__tuple_arg_list.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__tuple_arg_list.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24tuple_5farg_5flist
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__tuple_arg_list.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__tuple_arg_list.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_tuple.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__tuple_arg_list.case_0
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s1 e_v7 (by rw [he_v7]; exact empty_args) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with Store.apply_rep s2 v7 v5 _ _ hinv2 h64 h_v7 h_v5 (by ns_tac) (by ns_tac) as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24tuple_5farg_5flist s3 v2 _ hinv3 h64 (hG.rem hrem) h_v2 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  store_step with Store.apply_mk_rep s4 v8 v9 _ _ hinv4 h64 h_v8 h_v9 as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  case_done hinv5 hG with h_v10 in EoCases.__tuple_arg_list.case_0 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_1_eo__24tuple_5farg_5flist_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_1_eo__24tuple_5farg_5flist s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__tuple_arg_list.case_1 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__tuple_arg_list.case_1 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24tuple_5farg_5flist
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_tuple_2eunit.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__tuple_arg_list.case_1
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__tuple_arg_list.case_1 using hn_a0

/-- logos's `__tuple_arg_list` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24tuple_5farg_5flist.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __tuple_arg_list x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__tuple_arg_list.case_0 x_a0, EoCases.__tuple_arg_list.case_1 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __tuple_arg_list
  unfold EoCases.__tuple_arg_list.case_0 EoCases.__tuple_arg_list.case_1
  logos_eq

theorem body_eo__24tuple_5farg_5flist_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24tuple_5farg_5flist s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__tuple_arg_list x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24tuple_5farg_5flist.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24tuple_5farg_5flist
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24tuple_5farg_5flist_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  case_step with case_1_eo__24tuple_5farg_5flist_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 using hn_a0 hc0
  body_stuck hinv2 hG using hn_a0 hc0 hc1 in EoCases.__tuple_arg_list.case_0 EoCases.__tuple_arg_list.case_1

theorem eo__24tuple_5farg_5flist_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24tuple_5farg_5flist.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24tuple_5farg_5flist
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 1098#u32 _ [a0] rfl
    (fun s1 => body_eo__24tuple_5farg_5flist s1 a0) (fun s' t => Represents.rep s' t (__tuple_arg_list x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, y0, hargs, hb0, hr⟩ := ProgramSem.of_1098 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_1098 ⟨a0, x_a0, rfl, Rep.mono hpre h_a0, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24tuple_5farg_5flist_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24typed_5flist_5felement_5ftype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24typed_5flist_5felement_5ftype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__typed_list_element_type.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__typed_list_element_type.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24typed_5flist_5felement_5ftype
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__typed_list_element_type.case_0
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__40_40TypedList.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__typed_list_element_type.case_0
  case_done hinv1 hG with h_v2 in EoCases.__typed_list_element_type.case_0 using hn_a0 hn_v1 hn_v2

/-- logos's `__typed_list_element_type` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24typed_5flist_5felement_5ftype.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __typed_list_element_type x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__typed_list_element_type.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __typed_list_element_type
  unfold EoCases.__typed_list_element_type.case_0
  logos_eq

theorem body_eo__24typed_5flist_5felement_5ftype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24typed_5flist_5felement_5ftype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__typed_list_element_type x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24typed_5flist_5felement_5ftype.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24typed_5flist_5felement_5ftype
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24typed_5flist_5felement_5ftype_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__typed_list_element_type.case_0

theorem eo__24typed_5flist_5felement_5ftype_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24typed_5flist_5felement_5ftype.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24typed_5flist_5felement_5ftype
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24typed_5flist_5felement_5ftype s1 a0) (fun s' t => Represents.rep s' t (__typed_list_element_type x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24typed_5flist_5felement_5ftype_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

end pathos_compiled_checker
